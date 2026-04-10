#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
SMB-Downloader v3.1 — копирование файлов с сетевых дисков (SMB)
===============================================================
v3.1 — новые возможности:
  [NEW] Кнопка расчёта MD5 источника до начала копирования
  [NEW] Раздельные записи в истории: MD5 рассчитан / копирование
  [NEW] Двойной клик по истории — открыть папку с файлом
  [NEW] Контекстное меню истории (повтор, открыть папку)
  [NEW] Кнопка «Отмена» очищает поля ввода

  Исправления v3:
  [FIX] Пауза/возобновление — корректное переоткрытие файлов
  [FIX] MD5 проверяется ТОЛЬКО при полном завершении (не при паузе/отмене)
  [NEW] Запись в историю при СТАРТЕ (статус «в процессе»)
  [NEW] При запуске — автоопределение незавершённых копиований из .part/.meta
  [NEW] Двойной клик по записи истории «в процессе» — предложение докачать
  [FIX] После потери сети — переоткрытие файлов перед продолжением
  [FIX] Сохранение метаданных при закрытии окна

  [#5]  Умная пауза при потере сети (экспоненциальная задержка)
  [#8]  Динамический размер блока (32 КБ – 8 МБ)
  [#11] Автосохранение прогресса (30 с / 10 МБ)
  [#13] История копирования (history.json, CSV)
  [#14] Визуальный индикатор скорости
  [CFG] config.json
"""

import os
import csv
import json
import time
import shutil
import hashlib
import logging
import subprocess
import tkinter as tk
from tkinter import filedialog, messagebox, ttk
from threading import Thread, Event
from datetime import datetime
from pathlib import Path
from collections import deque

# ===================================================================
# Константы
# ===================================================================
CHUNK_SIZE_MIN = 32 * 1024
CHUNK_SIZE_MAX = 8 * 1024 * 1024
CHUNK_SIZE_START = 256 * 1024
CHUNK_SIZE_MID1 = 1024 * 1024
CHUNK_SIZE_MID2 = 4 * 1024 * 1024
SPEED_THRESH_HIGH_1 = 5 * 1024
SPEED_THRESH_HIGH_2 = 10 * 1024
SPEED_THRESH_LOW_1 = 500
SPEED_THRESH_LOW_2 = 100

NETWORK_RETRY_MAX = 10
NETWORK_RETRY_BASE = 5

AUTO_SAVE_INTERVAL_SEC = 30
AUTO_SAVE_INTERVAL_BYTES = 10 * 1024 * 1024

META_EXTENSION = ".meta"
PART_EXTENSION = ".part"
PARTIAL_META_EXTENSION = ".part.meta"

# Статусы для истории
STATUS_IN_PROGRESS = "в процессе"
STATUS_DONE = "успех"
STATUS_ERROR = "ошибка"
STATUS_CANCELLED = "отмена"
STATUS_PAUSED = "пауза"

# ===================================================================
# Логирование
# ===================================================================
# Определяем директорию программы.
# При запуске из .exe (PyInstaller) __file__ указывает на временную директорию,
# поэтому используем sys.executable для определения реальной папки.
def _get_program_dir() -> Path:
    """Возвращает дирекрию программы (работает и для .py, и для .exe)."""
    if getattr(sys, 'frozen', False):
        # Запуск из .exe (PyInstaller) — берём папку исполняемого файла
        return Path(sys.executable).parent
    else:
        # Запуск из исходников
        return Path(__file__).resolve().parent


PROGRAM_DIR = _get_program_dir()
LOG_FILE = PROGRAM_DIR / "copy_log.txt"


def setup_logger() -> logging.Logger:
    logger = logging.getLogger("smb_downloader")
    logger.setLevel(logging.DEBUG)
    logger.handlers.clear()
    fh = logging.FileHandler(LOG_FILE, encoding="utf-8")
    fh.setLevel(logging.DEBUG)
    fmt = logging.Formatter("%(asctime)s [%(levelname)s] %(message)s",
                            datefmt="%Y-%m-%d %H:%M:%S")
    fh.setFormatter(fmt)
    logger.addHandler(fh)
    return logger


logger = setup_logger()

# ===================================================================
# Конфигурация
# ===================================================================
CONFIG_FILE = PROGRAM_DIR / "config.json"

DEFAULT_CONFIG = {
    "speed_limit_kbps": 0,
    "dst_dir": str(Path.home() / "Downloads"),
    "chunk_mode": "auto",
    "manual_chunk_size": 1024 * 1024,
    "auto_save_interval_sec": AUTO_SAVE_INTERVAL_SEC,
    "auto_save_interval_bytes": AUTO_SAVE_INTERVAL_BYTES,
    "network_retry_max": NETWORK_RETRY_MAX,
    "network_retry_base": NETWORK_RETRY_BASE,
    "history_max_entries": 50,
    "window_geometry": "900x680",
}


def load_config() -> dict:
    if CONFIG_FILE.exists():
        try:
            with open(CONFIG_FILE, "r", encoding="utf-8") as f:
                cfg = json.load(f)
            for k, v in DEFAULT_CONFIG.items():
                cfg.setdefault(k, v)
            return cfg
        except Exception as exc:
            logger.warning(f"config.json corrupt, using defaults: {exc}")
    return dict(DEFAULT_CONFIG)


def save_config(cfg: dict):
    try:
        with open(CONFIG_FILE, "w", encoding="utf-8") as f:
            json.dump(cfg, f, indent=2)
    except Exception as exc:
        logger.error(f"Failed to save config: {exc}")

# ===================================================================
# Менеджер истории
# ===================================================================
HISTORY_FILE = PROGRAM_DIR / "history.json"


class HistoryManager:
    """Хранит историю копирований. Поддерживает записи «в процессе»."""

    def __init__(self, max_entries: int = 50):
        self.max_entries = max_entries
        self.entries: list[dict] = []
        self._load()

    def _load(self):
        if HISTORY_FILE.exists():
            try:
                with open(HISTORY_FILE, "r", encoding="utf-8") as f:
                    self.entries = json.load(f)
            except Exception:
                self.entries = []

    def save(self):
        try:
            with open(HISTORY_FILE, "w", encoding="utf-8") as f:
                json.dump(self.entries, f, indent=2, ensure_ascii=False)
        except Exception as exc:
            logger.error(f"Failed to save history: {exc}")

    def add(self, entry: dict) -> int:
        """Добавить запись. Возвращает индекс."""
        self.entries.append(entry)
        if len(self.entries) > self.max_entries:
            self.entries = self.entries[-self.max_entries:]
        self.save()
        return len(self.entries) - 1

    def update(self, index: int, updates: dict):
        """Обновить существующую запись."""
        if 0 <= index < len(self.entries):
            self.entries[index].update(updates)
            self.save()

    def find_in_progress(self, src: str, dst: str) -> int | None:
        """Найти запись «в процессе» или «MD5 рассчитан» с такими же src/dst."""
        for i, e in enumerate(self.entries):
            if (e.get("src") == src and e.get("dst") == dst and
                    e.get("status") in (STATUS_IN_PROGRESS, "MD5 рассчитан",
                                        STATUS_PAUSED)):
                return i
        return None

    def clear(self):
        self.entries.clear()
        self.save()

    def export_csv(self, filepath: str):
        if not self.entries:
            return
        keys = ["src", "dst", "size", "datetime", "status",
                "avg_speed_kbps", "interruptions", "md5_src", "md5_dst"]
        with open(filepath, "w", newline="", encoding="utf-8-sig") as f:
            writer = csv.DictWriter(f, fieldnames=keys, extrasaction="ignore")
            writer.writeheader()
            writer.writerows(self.entries)

# ===================================================================
# Утилиты
# ===================================================================

def fmt_size(nbytes: int) -> str:
    if nbytes < 1024:
        return f"{nbytes} Б"
    elif nbytes < 1024 ** 2:
        return f"{nbytes / 1024:.2f} КБ"
    elif nbytes < 1024 ** 3:
        return f"{nbytes / 1024 ** 2:.2f} МБ"
    else:
        return f"{nbytes / 1024 ** 3:.2f} ГБ"


def compute_md5(filepath: str, callback=None) -> str:
    h = hashlib.md5()
    total = os.path.getsize(filepath)
    read = 0
    with open(filepath, "rb") as f:
        while True:
            chunk = f.read(8192 * 1024)
            if not chunk:
                break
            h.update(chunk)
            read += len(chunk)
            if callback:
                callback(read, total)
    return h.hexdigest()


def load_meta(meta_path: str) -> dict:
    """Загрузить метаданные. Сначала .meta, затем .part.meta."""
    if os.path.exists(meta_path):
        try:
            with open(meta_path, "r", encoding="utf-8") as f:
                return json.load(f)
        except Exception:
            pass
    return {}


def save_meta(meta_path: str, data: dict):
    try:
        with open(meta_path, "w", encoding="utf-8") as f:
            json.dump(data, f, indent=2)
    except Exception as exc:
        logger.error(f"Failed to save meta {meta_path}: {exc}")


def detect_partials(dst_dir: str = None) -> list[dict]:
    """
    Поиск незавершённых .part файлов.
    Возвращает список dict с информацией о каждом.
    Если dst_dir задан — искать только в нём, иначе — в директории по умолчанию.
    """
    results = []
    search_dirs = [dst_dir] if dst_dir else [str(Path.home() / "Downloads")]
    # Также сканируем config.json dst_dir
    cfg = load_config()
    cfg_dst = cfg.get("dst_dir", "")
    if cfg_dst and cfg_dst not in search_dirs:
        search_dirs.append(cfg_dst)

    for d in search_dirs:
        if not os.path.isdir(d):
            continue
        for fname in os.listdir(d):
            fpath = os.path.join(d, fname)
            # Ищем .meta файлы
            if fname.endswith(META_EXTENSION):
                meta = load_meta(fpath)
                if meta:
                    part_path = fname.replace(META_EXTENSION, PART_EXTENSION)
                    part_full = os.path.join(d, part_path)
                    if os.path.exists(part_full):
                        results.append({
                            "src": meta.get("source", ""),
                            "dst": os.path.join(d, fname.replace(META_EXTENSION, "")),
                            "part_path": part_full,
                            "meta_path": fpath,
                            "total_size": meta.get("total_size", 0),
                            "copied_bytes": meta.get("copied_bytes", 0),
                            "timestamp": meta.get("timestamp", ""),
                            "interruptions": meta.get("interruptions", 0),
                        })
    return results

# ===================================================================
# Динамический размер блока (#8)
# ===================================================================

class DynamicChunkSizer:
    """Автоматическая подстройка размера блока."""

    def __init__(self, mode: str = "auto", manual_size: int = CHUNK_SIZE_START):
        self.mode = mode
        self.manual_size = manual_size
        self.current_chunk = CHUNK_SIZE_START
        self._speed_samples: deque = deque(maxlen=5)

    def update(self, speed_kbps: float):
        if self.mode != "auto":
            self.current_chunk = self.manual_size
            return

        self._speed_samples.append(speed_kbps)
        avg = sum(self._speed_samples) / len(self._speed_samples)

        if avg > SPEED_THRESH_HIGH_2:
            target = CHUNK_SIZE_MID2
        elif avg > SPEED_THRESH_HIGH_1:
            target = CHUNK_SIZE_MID1
        elif avg < SPEED_THRESH_LOW_2:
            target = 64 * 1024
        elif avg < SPEED_THRESH_LOW_1:
            target = 128 * 1024
        else:
            target = CHUNK_SIZE_START

        if target > self.current_chunk:
            self.current_chunk = min(target, self.current_chunk * 2)
        elif target < self.current_chunk:
            self.current_chunk = max(target, self.current_chunk // 2)

        self.current_chunk = max(CHUNK_SIZE_MIN,
                                 min(CHUNK_SIZE_MAX, self.current_chunk))

    @property
    def chunk_size(self) -> int:
        return self.current_chunk

# ===================================================================
# Копировальщик
# ===================================================================

class FileCopier:
    """Копирование с возобновлением, паузой, ограничением скорости,
    умной обработкой потери сети и динамическим блоком."""

    def __init__(self, src: str, dst: str, speed_limit_kbps: float,
                 pause_event: Event, cancel_event: Event,
                 progress_cb, status_cb, error_cb, complete_cb,
                 paused_cb=None, network_status_cb=None,
                 chunk_sizer: DynamicChunkSizer = None,
                 auto_save_interval_sec: int = AUTO_SAVE_INTERVAL_SEC,
                 auto_save_interval_bytes: int = AUTO_SAVE_INTERVAL_BYTES,
                 network_retry_max: int = NETWORK_RETRY_MAX,
                 network_retry_base: int = NETWORK_RETRY_BASE):
        self.src = src
        self.dst = dst
        self.part_path = dst + PART_EXTENSION
        self.meta_path = dst + META_EXTENSION
        self.partial_meta_path = dst + PARTIAL_META_EXTENSION
        self.speed_limit_kbps = speed_limit_kbps
        self.pause_event = pause_event
        self.cancel_event = cancel_event

        self.progress_cb = progress_cb
        self.status_cb = status_cb
        self.error_cb = error_cb
        self.complete_cb = complete_cb
        self.paused_cb = paused_cb or (lambda: None)  # сигнал о постановке на паузу
        self.network_status_cb = network_status_cb or (lambda m: None)

        self.chunk_sizer = chunk_sizer or DynamicChunkSizer()
        self.auto_save_interval_sec = auto_save_interval_sec
        self.auto_save_interval_bytes = auto_save_interval_bytes
        self.network_retry_max = network_retry_max
        self.network_retry_base = network_retry_base

        self._total_size = 0
        self._copied = 0
        self._speed_history: deque = deque(maxlen=20)
        self._start_time = 0.0
        self._last_update_time = 0.0
        self._last_auto_save_time = 0.0
        self._last_auto_save_bytes = 0
        self._interruption_count = 0
        self._current_speed_kbps = 0.0
        self._was_paused = False  # True если _copy_loop вышел по паузе

    # ---- основной запуск ----

    def run(self):
        """
        Главный цикл.
        При паузе — _copy_loop сохраняет .meta и делает return.
        Здесь мы это детектим по self._was_paused и НЕ вызываем _on_success().
        При отмене — аналогично.
        При OSError — retry через _handle_network_loss.
        При полном завершении файла — _on_success() с MD5.
        """
        try:
            if not os.path.exists(self.src):
                self._emit_error(f"Исходный файл не найден: {self.src}")
                return

            self._total_size = os.path.getsize(self.src)
            self._start_time = time.time()
            self._last_update_time = self._start_time
            self._last_auto_save_time = self._start_time
            self._last_auto_save_bytes = 0

            # Загрузка метаданных
            meta = load_meta(self.meta_path)
            partial_meta = load_meta(self.partial_meta_path)
            start_pos = max(meta.get("copied_bytes", 0),
                            partial_meta.get("copied_bytes", 0))

            if os.path.exists(self.part_path) and start_pos < self._total_size:
                self._copied = start_pos
                self.status_cb(
                    f"Возобновление копирования с {fmt_size(self._copied)}")
                logger.info(f"Resume from {fmt_size(self._copied)}")
            else:
                self._copied = 0
                if os.path.exists(self.part_path):
                    os.remove(self.part_path)

            self.status_cb(f"Начало копирования: {fmt_size(self._total_size)}")
            logger.info(f"Start: {self.src} -> {self.part_path} "
                        f"({fmt_size(self._total_size)})")

            while self._copied < self._total_size:
                self._was_paused = False  # сброс перед каждым проходом
                try:
                    self._copy_loop()
                except OSError as exc:
                    self._interruption_count += 1
                    logger.warning(f"Network error #{self._interruption_count}: {exc}")
                    if not self._handle_network_loss(exc):
                        self._save_meta()
                        self._emit_error(
                            f"Сеть недоступна после {self.network_retry_max} попыток.\n"
                            f"Последняя ошибка: {exc}")
                        return
                    continue  # после восстановления сети — переоткрыть файлы

                # _copy_loop вернулся — почему?
                if self._was_paused:
                    # Пауза: .meta уже сохранён в _copy_loop
                    self.status_cb(f"Пауза. Скопировано {fmt_size(self._copied)}. "
                                   f"Нажмите «Старт» для возобновления.")
                    logger.info(f"Paused at {fmt_size(self._copied)}. "
                                f"Thread exiting.")
                    return  # поток завершается

                if self.cancel_event.is_set():
                    # Отмена (может прийти во время throttle/sleep)
                    self._save_meta()
                    self.status_cb("Копирование отменено.")
                    logger.info("Cancelled.")
                    return

                # Файл полностью скопирован
                break

            self._on_success()

        except PermissionError as exc:
            self._emit_error(f"Ошибка доступа: {exc}")
        except OSError as exc:
            self._emit_error(f"Ошибка файловой системы: {exc}")
        except Exception as exc:
            self._emit_error(f"Неожиданная ошибка: {exc}")

    def _copy_loop(self):
        """
        Один проход чтения/записи. Файлы открываются/закрываются здесь.

        Выходы:
          - self._was_paused = True  → пользователь нажал «Пауза», .meta сохранён
          - self._copied >= self._total_size  → файл завершён
          - cancel_event → отмена
          - OSError → проброс наверх для retry
        """
        mode_src = "rb"
        mode_dst = "r+b" if self._copied > 0 else "wb"

        with open(self.src, mode_src) as fsrc:
            fsrc.seek(self._copied)
            with open(self.part_path, mode_dst) as fdst:
                if self._copied > 0:
                    fdst.seek(self._copied)

                while self._copied < self._total_size:
                    # --- Отмена ---
                    if self.cancel_event.is_set():
                        self._save_meta()
                        logger.info("Cancelled by user.")
                        return

                    # --- Пауза: сохранить мету и СРАЗУ выйти (поток завершится) ---
                    if self.pause_event.is_set():
                        self._was_paused = True
                        self._save_meta()
                        self.status_cb(
                            f"Пауза. Скопировано {fmt_size(self._copied)}. "
                            f"Нажмите «Старт» для возобновления.")
                        logger.info(f"Paused by user at {fmt_size(self._copied)}. "
                                    f"Meta saved. Thread will exit.")
                        self.paused_cb()
                        return  # ← ВЫХОД из _copy_loop → выход из run()

                    # --- Чтение блока (#8) ---
                    to_read = min(self.chunk_sizer.chunk_size,
                                  self._total_size - self._copied)

                    read_start = time.time()
                    try:
                        data = fsrc.read(to_read)
                    except OSError:
                        raise  # проксировать → _handle_network_loss

                    read_end = time.time()

                    if not data:
                        break

                    fdst.write(data)
                    fdst.flush()
                    self._copied += len(data)

                    # #8 — обновление размера блока
                    elapsed_read = read_end - read_start
                    if elapsed_read > 0:
                        inst = (len(data) / 1024) / elapsed_read
                        self.chunk_sizer.update(inst)

                    # Ограничение скорости
                    self._throttle(len(data))

                    # Прогресс
                    now = time.time()
                    elapsed = now - self._start_time
                    overall_speed = (self._copied / 1024) / elapsed if elapsed > 0 else 0
                    self._current_speed_kbps = overall_speed

                    # Скользящее окно ETA
                    self._speed_history.append((overall_speed, now))
                    while (self._speed_history and
                           now - self._speed_history[0][1] > 10):
                        self._speed_history.popleft()

                    avg_speed = (sum(s for s, _ in self._speed_history) /
                                 len(self._speed_history) if self._speed_history
                                 else overall_speed)

                    remaining = self._total_size - self._copied
                    eta = (remaining / 1024 / avg_speed) if avg_speed > 0 else 0

                    # #11 — автосохранение
                    self._auto_save_check(now)

                    # UI ~2 раза/с
                    if now - self._last_update_time >= 0.5:
                        self.progress_cb(self._copied, self._total_size,
                                         avg_speed, eta)
                        self.status_cb(
                            f"Скопировано {fmt_size(self._copied)} из "
                            f"{fmt_size(self._total_size)} "
                            f"({avg_speed:.1f} КБ/с)")
                        self._last_update_time = now

    def _handle_network_loss(self, exc: Exception) -> bool:
        """#5 — экспоненциальная задержка при потере сети."""
        self.network_status_cb(
            f"Сеть потеряна. Переподключение… ({exc})")
        logger.warning(f"Network lost: {exc}. Exponential retry.")

        for attempt in range(1, self.network_retry_max + 1):
            delay = min(self.network_retry_base * (2 ** (attempt - 1)), 300)

            if self.cancel_event.is_set():
                return False

            self.network_status_cb(
                f"Попытка {attempt}/{self.network_retry_max} через {delay:.0f} с…")
            logger.info(f"Retry {attempt}/{self.network_retry_max} in {delay}s")

            slept = 0
            while slept < delay:
                if self.cancel_event.is_set():
                    return False
                time.sleep(min(1.0, delay - slept))
                slept += 1

            if os.path.exists(self.src):
                self.network_status_cb("Сеть восстановлена!")
                logger.info("Network restored.")
                return True
            # Иначе — ждать дальше

        return False

    # ---- автосохранение (#11) ----

    def _auto_save_check(self, now: float):
        dt = now - self._last_auto_save_time
        db = self._copied - self._last_auto_save_bytes
        if dt >= self.auto_save_interval_sec or db >= self.auto_save_interval_bytes:
            self._auto_save()
            self._last_auto_save_time = now
            self._last_auto_save_bytes = self._copied

    def _auto_save(self):
        save_meta(self.partial_meta_path, {
            "type": "auto_save",
            "source": self.src,
            "destination": self.dst,
            "total_size": self._total_size,
            "copied_bytes": self._copied,
            "avg_speed_kbps": round(self._current_speed_kbps, 1),
            "timestamp": datetime.now().isoformat(),
            "interruptions": self._interruption_count,
        })
        logger.debug(f"Auto-save {fmt_size(self._copied)}")

    # ---- успешное завершение ----

    def _on_success(self):
        self.progress_cb(self._total_size, self._total_size, 0, 0)
        self.status_cb("Копирование завершено. Проверка MD5…")
        logger.info("Copy finished. MD5 check…")

        final_path = self.dst
        if os.path.exists(final_path):
            os.remove(final_path)
        os.rename(self.part_path, final_path)

        # Удалить все метаданные
        for mp in (self.meta_path, self.partial_meta_path):
            if os.path.exists(mp):
                os.remove(mp)

        # MD5 — только при ПОЛНОМ завершении
        src_md5 = compute_md5(
            self.src,
            callback=lambda r, t: self.status_cb(f"MD5 источник: {r*100//t}%"))
        dst_md5 = compute_md5(
            final_path,
            callback=lambda r, t: self.status_cb(f"MD5 приёмник: {r*100//t}%"))

        md5_match = (src_md5 == dst_md5)
        if md5_match:
            self.status_cb(f"MD5 совпадает: {src_md5}")
            logger.info(f"MD5 match: {src_md5}")
        else:
            self.status_cb("MD5 НЕ совпадает!")
            logger.error(f"MD5 mismatch: src={src_md5} dst={dst_md5}")

        self.complete_cb(md5_match, src_md5, dst_md5)

    # ---- ограничение скорости ----

    def _throttle(self, bytes_read: int):
        if self.speed_limit_kbps <= 0:
            return
        expected = (bytes_read / 1024) / self.speed_limit_kbps
        elapsed = time.time() - self._last_update_time
        sleep_time = expected - elapsed
        if sleep_time > 0:
            rem = sleep_time
            while rem > 0:
                if self.cancel_event.is_set() or self.pause_event.is_set():
                    return
                w = min(0.1, rem)
                time.sleep(w)
                rem -= w

    # ---- метаданные ----

    def _save_meta(self):
        save_meta(self.meta_path, {
            "source": self.src,
            "destination": self.dst,
            "total_size": self._total_size,
            "copied_bytes": self._copied,
            "timestamp": datetime.now().isoformat(),
            "interruptions": self._interruption_count,
        })

    def _emit_error(self, msg: str):
        logger.error(msg)
        self.error_cb(msg)

# ===================================================================
# GUI
# ===================================================================

class SMBDownloaderApp:
    """Главное окно: вкладки «Копирование» и «История»."""

    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title("SMB-Downloader v3.1")
        self.config = load_config()
        self.root.geometry(self.config.get("window_geometry", "900x680"))
        self.root.minsize(700, 500)

        self.history_mgr = HistoryManager(
            max_entries=self.config.get("history_max_entries", 50))

        self.pause_event = Event()
        self.cancel_event = Event()
        self.copier_thread: Thread | None = None
        self.copier: FileCopier | None = None

        # Индекс записи в истории для текущего копирования
        self._history_index: int | None = None

        self.chunk_sizer = DynamicChunkSizer(
            mode=self.config.get("chunk_mode", "auto"),
            manual_size=self.config.get("manual_chunk_size", CHUNK_SIZE_START))

        # MD5 источника (рассчитывается заранее)
        self._src_md5: str | None = None

        self._current_speed_kbps = 0.0

        self._build_ui()
        self._check_and_offer_resume()  # автоопределение незавершённых
        self._refresh_history_ui()

        self.root.protocol("WM_DELETE_WINDOW", self._on_close)

    # ======================== UI ========================

    def _build_ui(self):
        PAD = 8
        self.notebook = ttk.Notebook(self.root)
        self.notebook.pack(fill="both", expand=True, padx=PAD, pady=PAD)

        self.tab_copy = ttk.Frame(self.notebook, padding=PAD)
        self.notebook.add(self.tab_copy, text="  Копирование  ")
        self._build_copy_tab()

        self.tab_history = ttk.Frame(self.notebook, padding=PAD)
        self.notebook.add(self.tab_history, text="  История  ")
        self._build_history_tab()

    # ---------- Вкладка «Копирование» ----------

    def _build_copy_tab(self):
        PAD = 8

        # Источник
        frm = ttk.LabelFrame(self.tab_copy, text="Исходный файл", padding=PAD)
        frm.pack(fill="x", pady=5)
        self.var_src = tk.StringVar()
        ttk.Entry(frm, textvariable=self.var_src).pack(
            side="left", fill="x", expand=True, padx=(0, PAD))
        ttk.Button(frm, text="Обзор…", command=self._choose_src).pack(side="right")
        self.btn_md5_src = ttk.Button(frm, text="🔒 MD5", command=self._calc_src_md5,
                                       state="disabled")
        self.btn_md5_src.pack(side="right", padx=(0, 5))

        # Назначение
        frm = ttk.LabelFrame(self.tab_copy, text="Папка назначения", padding=PAD)
        frm.pack(fill="x", pady=5)
        self.var_dst = tk.StringVar(value=self.config.get(
            "dst_dir", str(Path.home() / "Downloads")))
        ttk.Entry(frm, textvariable=self.var_dst).pack(
            side="left", fill="x", expand=True, padx=(0, PAD))
        ttk.Button(frm, text="Обзор…", command=self._choose_dst).pack(side="right")

        # Настройки
        frm = ttk.LabelFrame(self.tab_copy, text="Настройки", padding=PAD)
        frm.pack(fill="x", pady=5)

        f1 = ttk.Frame(frm)
        f1.pack(fill="x", pady=2)
        ttk.Label(f1, text="Лимит (КБ/с, 0=∞):").pack(side="left", padx=(0, 5))
        self.var_speed = tk.StringVar(
            value=str(int(self.config.get("speed_limit_kbps", 0))))
        ttk.Entry(f1, textvariable=self.var_speed, width=10).pack(side="left")

        f2 = ttk.Frame(frm)
        f2.pack(fill="x", pady=2)
        ttk.Label(f2, text="Блок:").pack(side="left", padx=(0, 5))
        self.var_chunk_mode = tk.StringVar(
            value=self.config.get("chunk_mode", "auto"))
        ttk.Radiobutton(f2, text="Авто", variable=self.var_chunk_mode,
                        value="auto").pack(side="left")
        ttk.Radiobutton(f2, text="Ручной", variable=self.var_chunk_mode,
                        value="manual").pack(side="left")
        self.var_manual_chunk = tk.StringVar(
            value=str(self.config.get("manual_chunk_size", CHUNK_SIZE_START)))
        ttk.Label(f2, text="Б:").pack(side="left", padx=(8, 3))
        ttk.Entry(f2, textvariable=self.var_manual_chunk, width=10).pack(side="left")

        f3 = ttk.Frame(frm)
        f3.pack(fill="x", pady=2)
        ttk.Label(f3, text="Попытки:").pack(side="left", padx=(0, 5))
        self.var_retry_max = tk.StringVar(
            value=str(self.config.get("network_retry_max", NETWORK_RETRY_MAX)))
        ttk.Entry(f3, textvariable=self.var_retry_max, width=5).pack(
            side="left", padx=(0, 5))
        ttk.Label(f3, text="База (с):").pack(side="left", padx=(0, 5))
        self.var_retry_base = tk.StringVar(
            value=str(self.config.get("network_retry_base", NETWORK_RETRY_BASE)))
        ttk.Entry(f3, textvariable=self.var_retry_base, width=5).pack(side="left")

        # Прогресс
        frm = ttk.LabelFrame(self.tab_copy, text="Прогресс", padding=PAD)
        frm.pack(fill="x", pady=5)

        self.progress_bar = ttk.Progressbar(frm, mode="determinate")
        self.progress_bar.pack(fill="x", pady=(0, 5))

        self.lbl_progress_detail = ttk.Label(frm, text="Скопировано: 0 / 0")
        self.lbl_progress_detail.pack(anchor="w")
        self.lbl_eta = ttk.Label(frm, text="Осталось: —")
        self.lbl_eta.pack(anchor="w")
        self.lbl_speed = ttk.Label(frm, text="Скорость: —")
        self.lbl_speed.pack(anchor="w")

        # Индикатор скорости (#14)
        frm = ttk.LabelFrame(self.tab_copy, text="Скорость", padding=PAD)
        frm.pack(fill="x", pady=5)

        self.speed_bar = ttk.Progressbar(frm, mode="determinate", maximum=100)
        self.speed_bar.pack(fill="x", pady=(0, 3))
        self.lbl_speed_info = ttk.Label(
            frm, text="Текущая: 0.0 КБ/с | Лимит: — | Свободно: —")
        self.lbl_speed_info.pack(anchor="w")
        self.lbl_chunk = ttk.Label(
            frm, text=f"Блок: {fmt_size(self.chunk_sizer.chunk_size)}")
        self.lbl_chunk.pack(anchor="w")

        # Статус
        frm = ttk.LabelFrame(self.tab_copy, text="Статус", padding=PAD)
        frm.pack(fill="x", pady=5)
        self.lbl_status = ttk.Label(frm, text="Готово", wraplength=800)
        self.lbl_status.pack(anchor="w")

        # Кнопки
        frm = ttk.Frame(self.tab_copy, padding=PAD)
        frm.pack(fill="x", pady=5)

        self.btn_start = ttk.Button(frm, text="▶ Старт",
                                    command=self._start_copy)
        self.btn_start.pack(side="left", padx=5)

        self.btn_pause = ttk.Button(frm, text="⏸ Пауза",
                                    command=self._toggle_pause,
                                    state="disabled")
        self.btn_pause.pack(side="left", padx=5)

        self.btn_cancel = ttk.Button(frm, text="⏹ Отмена",
                                     command=self._cancel_copy,
                                     state="disabled")
        self.btn_cancel.pack(side="left", padx=5)

        self.btn_retry = ttk.Button(frm, text="🔄 Повторить (сеть)",
                                     command=self._retry_network,
                                     state="disabled")
        self.btn_retry.pack(side="left", padx=20)

        ttk.Separator(frm, orient="vertical").pack(
            side="left", fill="y", padx=10)

        self.btn_about = ttk.Button(frm, text="ℹ О программе",
                                     command=self._show_about)
        self.btn_about.pack(side="right")

    # ---------- Вкладка «История» ----------

    def _build_history_tab(self):
        PAD = 8

        f = ttk.Frame(self.tab_history, padding=PAD)
        f.pack(fill="x", pady=5)
        ttk.Button(f, text="📁 Экспорт CSV",
                   command=self._history_export_csv).pack(side="left", padx=3)
        ttk.Button(f, text="🗑 Очистить",
                   command=self._history_clear).pack(side="left", padx=3)

        cols = ("dt", "src", "dst", "sz", "st", "spd", "int", "md5_src", "md5_dst")
        self.hist_tree = ttk.Treeview(self.tab_history, columns=cols,
                                       show="headings", height=18)
        self.hist_tree.heading("dt", text="Дата/Время")
        self.hist_tree.heading("src", text="Источник")
        self.hist_tree.heading("dst", text="Назначение")
        self.hist_tree.heading("sz", text="Размер")
        self.hist_tree.heading("st", text="Статус")
        self.hist_tree.heading("spd", text="Ср. скорость")
        self.hist_tree.heading("int", text="Обрывы")
        self.hist_tree.heading("md5_src", text="MD5 источника")
        self.hist_tree.heading("md5_dst", text="MD5 приёмника")

        self.hist_tree.column("dt", width=130)
        self.hist_tree.column("src", width=160)
        self.hist_tree.column("dst", width=160)
        self.hist_tree.column("sz", width=80)
        self.hist_tree.column("st", width=80)
        self.hist_tree.column("spd", width=90)
        self.hist_tree.column("int", width=50)
        self.hist_tree.column("md5_src", width=180)
        self.hist_tree.column("md5_dst", width=180)

        sb = ttk.Scrollbar(self.tab_history, orient="vertical",
                           command=self.hist_tree.yview)
        self.hist_tree.configure(yscrollcommand=sb.set)
        self.hist_tree.pack(side="left", fill="both", expand=True, padx=PAD, pady=PAD)
        sb.pack(side="right", fill="y")

        self.hist_tree.bind("<Double-Button-1>", self._history_double_click)
        self.hist_tree.bind("<Button-3>", self._history_right_click)

        # Контекстное меню
        self.hist_menu = tk.Menu(self.root, tearoff=0)
        self.hist_menu.add_command(label="Повторить копирование", command=self._history_menu_retry)
        self.hist_menu.add_command(label="Открыть папку с файлом", command=self._history_menu_open_folder)

    # ======================== Выбор файлов ========================

    def _show_about(self):
        """Окно «О программе»."""
        about_text = (
            "SMB-Downloader v3.1\n"
            "═══════════════════\n\n"
            "Программа для надёжного копирования файлов\n"
            "с сетевых дисков (SMB, \\server\\share) на локальный компьютер.\n\n"
            "Возможности:\n"
            "  •  Возобновление копирования после обрыва связи или выключения ПК\n"
            "  •  Ограничение скорости (КБ/с) для слабых каналов\n"
            "  •  Прогресс-бар, ETA, отображение скорости\n"
            "  •  Предварительный расчёт MD5 источника до копирования\n"
            "  •  Проверка целостности MD5 после завершения\n"
            "  •  Раздельные записи в истории для MD5 и копирования\n"
            "  •  Автоматическая подстройка размера блока\n"
            "  •  Экспоненциальная задержка при потере сети\n"
            "  •  Автосохранение прогресса каждые 30 секунд\n"
            "  •  История копирований с экспортом в CSV\n"
            "  •  Контекстное меню истории (повтор, открыть папку)\n\n"
            "═══════════════════\n"
            "Разработано Selebren\n"
            "в содружестве с Qwen Coder"
        )
        messagebox.showinfo("О программе", about_text)

    def _choose_src(self):
        p = filedialog.askopenfilename(title="Выберите файл", initialdir=r"\\")
        if p:
            self.var_src.set(p)
            self.btn_md5_src.config(state="normal")
            self._src_md5 = None  # сброс при выборе нового файла
            logger.info(f"Source: {p}")

    def _calc_src_md5(self):
        """Рассчитать MD5 исходного файла и записать в историю."""
        src = self.var_src.get().strip()
        if not src or not os.path.exists(src):
            messagebox.showerror("Ошибка", "Сначала выберите исходный файл.")
            return

        # Запуск в отдельном потоке чтобы не морозить UI
        def _do():
            self.btn_md5_src.config(state="disabled", text="⏳ Считается…")
            self.lbl_status.config(text=f"Расчёт MD5 источника: 0%")
            try:
                md5 = compute_md5(
                    src,
                    callback=lambda r, t: self.root.after(
                        0, lambda: self.lbl_status.config(
                            text=f"Расчёт MD5 источника: {r*100//t}%")
                    )
                )
                self._src_md5 = md5
                # Создать НОВУЮ запись в истории (не обновлять существующую)
                dst_dir = self.var_dst.get().strip()
                if dst_dir:
                    dst_path = os.path.join(dst_dir, os.path.basename(src))
                else:
                    dst_path = os.path.basename(src)

                size_str = fmt_size(os.path.getsize(src))

                self._history_index = self.history_mgr.add({
                    "src": src,
                    "dst": dst_path,
                    "size": size_str,
                    "datetime": datetime.now().strftime("%Y-%m-%d %H:%M"),
                    "status": "MD5 рассчитан",
                    "avg_speed_kbps": "—",
                    "interruptions": 0,
                    "md5_src": md5,
                    "md5_dst": "—",
                })
                self.root.after(0, self._refresh_history_ui)
                self.root.after(0, lambda: self.lbl_status.config(
                    text=f"MD5 источника: {md5}"))
                self.root.after(0, lambda: self.btn_md5_src.config(
                    state="normal", text="🔒 MD5 ✓"))
            except Exception as exc:
                self.root.after(0, lambda: messagebox.showerror(
                    "Ошибка MD5", f"Не удалось рассчитать MD5:\n{exc}"))
                self.root.after(0, lambda: self.btn_md5_src.config(
                    state="normal", text="🔒 MD5"))

        Thread(target=_do, daemon=True).start()

    def _choose_dst(self):
        p = filedialog.askdirectory(title="Папка назначения",
                                    initialdir=self.var_dst.get())
        if p:
            self.var_dst.set(p)
            logger.info(f"Dst: {p}")

    # ======================== Управление ========================

    def _start_copy(self):
        src = self.var_src.get().strip()
        dst_dir = self.var_dst.get().strip()

        if not src:
            messagebox.showerror("Ошибка", "Не выбран исходный файл.")
            return
        if not dst_dir:
            messagebox.showerror("Ошибка", "Не выбрана папка назначения.")
            return
        if not os.path.exists(src):
            messagebox.showerror("Ошибка", f"Файл не найден:\n{src}")
            return

        # Если предыдущий поток ещё жив — дождаться его завершения
        if self.copier_thread and self.copier_thread.is_alive():
            self.lbl_status.config(text="Завершение предыдущей операции…")
            self.copier_thread.join(timeout=5)
            if self.copier_thread.is_alive():
                logger.warning("Previous thread didn't stop in 5s.")

        dst_path = os.path.join(dst_dir, os.path.basename(src))

        # Проверяем, есть ли сохранённый прогресс (возобновление)
        meta = load_meta(dst_path + META_EXTENSION)
        pmeta = load_meta(dst_path + PARTIAL_META_EXTENSION)
        saved_pos = max(meta.get("copied_bytes", 0),
                        pmeta.get("copied_bytes", 0))
        total_size = max(meta.get("total_size", 0),
                         pmeta.get("total_size", 0), 0)

        has_part = os.path.exists(dst_path + PART_EXTENSION)
        is_resume = (has_part and saved_pos > 0)

        if not is_resume:
            # Новое копирование — проверки
            total = 0
            try:
                total = os.path.getsize(src)
                free = self._free_space(dst_dir)
                if free is not None and total > free:
                    messagebox.showerror(
                        "Ошибка",
                        f"Нет места.\nНужно: {fmt_size(total)}, "
                        f"свободно: {fmt_size(free)}")
                    return
            except OSError as exc:
                messagebox.showerror("Ошибка", f"Размер файла: {exc}")
                return

            if os.path.exists(dst_path) and not has_part:
                if not messagebox.askyesno("Файл существует",
                                           f"{dst_path}\nПерезаписать?"):
                    return
            total = total if total else total_size
        else:
            # Возобновление
            total = total_size if total_size else 0
            logger.info(f"Resume: {src} -> {dst_path} "
                        f"from {fmt_size(saved_pos)} of {fmt_size(total)}")

        speed = self._parse_speed()
        if speed is None:
            return

        # Сброс событий ПЕРЕД запуском
        self.pause_event.clear()
        self.cancel_event.clear()

        self._set_buttons(running=True)
        self.btn_retry.config(state="disabled")

        if is_resume:
            pct = (saved_pos / total * 100) if total > 0 else 0
            self.progress_bar["value"] = pct
            self.lbl_status.config(
                text=f"Возобновление с {fmt_size(saved_pos)} из {fmt_size(total)}…")
            logger.info(f"RESUME: {fmt_size(saved_pos)}/{fmt_size(total)} "
                        f"({pct:.1f}%)")
        else:
            self.progress_bar["value"] = 0
            self.lbl_status.config(text="Запуск…")

        logger.info(f"Start: {src} -> {dst_path} (limit {speed} KB/s, "
                    f"resume={is_resume})")
        self._update_chunk_sizer()

        # Запись в историю — всегда НОВАЯ запись
        md5_src_str = self._src_md5 if self._src_md5 else "—"

        self._history_index = self.history_mgr.add({
            "src": src,
            "dst": dst_path,
            "size": fmt_size(total),
            "datetime": datetime.now().strftime("%Y-%m-%d %H:%M"),
            "status": STATUS_IN_PROGRESS,
            "avg_speed_kbps": "—",
            "interruptions": 0,
            "md5_src": md5_src_str,
            "md5_dst": "—",
        })
        self._refresh_history_ui()

        self.copier = FileCopier(
            src=src, dst=dst_path,
            speed_limit_kbps=speed,
            pause_event=self.pause_event,
            cancel_event=self.cancel_event,
            progress_cb=self._on_progress,
            status_cb=self._on_status,
            error_cb=self._on_error,
            complete_cb=self._on_complete,
            paused_cb=self._on_paused,
            network_status_cb=self._on_network_status,
            chunk_sizer=self.chunk_sizer,
            auto_save_interval_sec=self.config.get("auto_save_interval_sec",
                                                   AUTO_SAVE_INTERVAL_SEC),
            auto_save_interval_bytes=self.config.get("auto_save_interval_bytes",
                                                     AUTO_SAVE_INTERVAL_BYTES),
            network_retry_max=self._parse_retry_max(),
            network_retry_base=self._parse_retry_base(),
        )

        self.copier_thread = Thread(target=self.copier.run, daemon=True)
        self.copier_thread.start()
        logger.info("Copy thread started.")

    def _toggle_pause(self):
        """Остановить копирование с сохранением позиции.
        Поток завершится. Для возобновления — нажать «Старт»."""
        if not self.copier_thread or not self.copier_thread.is_alive():
            return
        self.pause_event.set()
        self.lbl_status.config(text="Остановка…")
        logger.info("Pause requested. Thread will save meta and exit.")

    def _cancel_copy(self):
        """Отменить: остановить поток, удалить .part и .meta файлы,
        очистить поля ввода."""
        if not self.copier_thread or not self.copier_thread.is_alive():
            return
        if not messagebox.askyesno("Отмена", "Отменить копирование?\nПрогресс будет потерян."):
            return

        self.cancel_event.set()
        self.lbl_status.config(text="Отмена…")
        logger.info("Cancel requested.")

        def _cleanup_after_cancel():
            if self.copier_thread and self.copier_thread.is_alive():
                self.copier_thread.join(timeout=5)
            # Удалить .part и .meta
            if self.copier:
                for p in (self.copier.part_path,
                          self.copier.meta_path,
                          self.copier.partial_meta_path):
                    if os.path.exists(p):
                        try:
                            os.remove(p)
                            logger.info(f"Removed {p} on cancel.")
                        except OSError:
                            pass
            # Очистить поля ввода
            self.var_src.set("")
            self.var_dst.set(self.config.get("dst_dir", ""))
            self.btn_md5_src.config(state="disabled", text="🔒 MD5")
            self._src_md5 = None
            self.progress_bar["value"] = 0
            self._set_buttons(running=False)
            if self._history_index is not None:
                self.history_mgr.update(self._history_index, {
                    "status": STATUS_CANCELLED,
                })
                self._refresh_history_ui()
            self.lbl_status.config(text="Отменено. Выберите файл.")

        self.root.after(100, _cleanup_after_cancel)

    def _retry_network(self):
        """После потери сети: если источник доступен — перезапустить."""
        if not self.copier:
            return
        self.btn_retry.config(state="disabled")

        if os.path.exists(self.copier.src):
            self.lbl_status.config(text="Сеть OK. Перезапуск…")
            logger.info("Network restored. Restarting copy from saved position.")
            # Перезапустить с теми же src/dst — FileCopier сам подхватит .meta
            self.root.after(500, self._start_copy)
        else:
            messagebox.showwarning("Сеть", "Источник недоступен.\n"
                                           "Проверьте сетевой диск.")

    # ======================== Callbacks из потока ========================

    def _on_progress(self, copied, total, speed_kbps, eta_sec):
        self.root.after(0, self._upd_progress, copied, total, speed_kbps, eta_sec)

    def _upd_progress(self, copied, total, speed_kbps, eta_sec):
        pct = (copied / total * 100) if total > 0 else 0
        self.progress_bar["value"] = pct
        self.lbl_progress_detail.config(
            text=f"Скопировано: {fmt_size(copied)} из {fmt_size(total)} ({pct:.1f}%)")

        if 0 < eta_sec < 86400 * 365:
            m, s = divmod(int(eta_sec), 60)
            h, m = divmod(m, 60)
            eta_str = f"{h} ч {m} мин" if h else f"{m} мин {s} с" if m else f"{s} с"
        else:
            eta_str = "—"
        self.lbl_eta.config(text=f"Осталось: {eta_str}")
        self.lbl_speed.config(text=f"Скорость: {speed_kbps:.1f} КБ/с")
        self._current_speed_kbps = speed_kbps

        if self.copier:
            self.lbl_chunk.config(
                text=f"Блок: {fmt_size(self.chunk_sizer.chunk_size)}")

        self._speed_indicator(speed_kbps)

    def _speed_indicator(self, speed_kbps: float):
        limit = self._parse_speed() or 0
        if limit > 0:
            pct = min(speed_kbps / limit * 100, 100)
            free_pct = max(0, 100 - pct)
            limit_str = f"{limit/1024:.1f} МБ/с" if limit >= 1024 else f"{limit:.0f} КБ/с"
        else:
            pct = min(speed_kbps / 100, 100)
            free_pct = "∞"
            limit_str = "∞"

        spd_str = f"{speed_kbps/1024:.1f} МБ/с" if speed_kbps >= 1024 else f"{speed_kbps:.0f} КБ/с"
        self.speed_bar["value"] = pct

        try:
            st = ttk.Style()
            if pct < 60:
                st.configure("sp.TProgressbar", background="#4CAF50")
            elif pct < 85:
                st.configure("sp.TProgressbar", background="#FFC107")
            else:
                st.configure("sp.TProgressbar", background="#F44336")
            self.speed_bar.configure(style="sp.TProgressbar")
        except Exception:
            pass

        free_s = "∞" if isinstance(free_pct, str) else f"{free_pct:.0f}%"
        self.lbl_speed_info.config(
            text=f"Текущая: {spd_str} | Лимит: {limit_str} | Свободно: {free_s}")

    def _on_status(self, msg):
        self.root.after(0, self.lbl_status.config, {"text": msg})

    def _on_network_status(self, msg):
        def _do():
            self.lbl_status.config(text=msg)
            if "потеряна" in msg.lower() or "попытка" in msg.lower():
                self.btn_retry.config(state="normal")
            else:
                self.btn_retry.config(state="disabled")
        self.root.after(0, _do)

    def _on_paused(self):
        """Вызывается в потоке копировщика при постановке на паузу."""
        def _do():
            self._set_buttons(running=False)
            # Обновить запись в истории — статус «пауза»
            if self._history_index is not None:
                self.history_mgr.update(self._history_index, {
                    "status": STATUS_PAUSED,
                    "avg_speed_kbps": f"{self._current_speed_kbps:.1f} КБ/с",
                    "md5_src": self._src_md5 if self._src_md5 else "—",
                })
                self._refresh_history_ui()
        self.root.after(0, _do)

    def _on_error(self, msg):
        def _do():
            self._set_buttons(running=False)
            self.btn_retry.config(state="normal")
            # Обновить историю
            if self._history_index is not None:
                self.history_mgr.update(self._history_index, {
                    "status": STATUS_ERROR,
                    "md5_src": self._src_md5 if self._src_md5 else "—",
                    "md5_dst": msg[:80],
                })
                self._refresh_history_ui()
            messagebox.showerror("Ошибка", msg)
        self.root.after(0, _do)

    def _on_complete(self, md5_match: bool, src_md5: str, dst_md5: str):
        def _do():
            self._set_buttons(running=False)
            self.progress_bar["value"] = 100

            total = self.copier._total_size if self.copier else 0
            ints = self.copier._interruption_count if self.copier else 0

            status = STATUS_DONE if md5_match else STATUS_ERROR

            if self._history_index is not None:
                self.history_mgr.update(self._history_index, {
                    "status": status,
                    "avg_speed_kbps":
                        f"{self.copier._current_speed_kbps:.1f} КБ/с"
                        if self.copier else "—",
                    "interruptions": ints,
                    "md5_src": src_md5,
                    "md5_dst": dst_md5,
                })
            else:
                self.history_mgr.add({
                    "src": self.copier.src if self.copier else "",
                    "dst": self.copier.dst if self.copier else "",
                    "size": fmt_size(total),
                    "datetime": datetime.now().strftime("%Y-%m-%d %H:%M"),
                    "status": status,
                    "avg_speed_kbps": "—",
                    "interruptions": ints,
                    "md5_src": src_md5,
                    "md5_dst": dst_md5,
                })
            self._refresh_history_ui()

            self.lbl_status.config(text="Готово!")

            if md5_match:
                messagebox.showinfo("Успех", "Файл скопирован!\nMD5 совпадает.")
            else:
                messagebox.showerror("Ошибка MD5",
                                     f"MD5 не совпадает!\n{src_md5} ≠ {dst_md5}")

        self.root.after(0, _do)

    def _set_buttons(self, running: bool):
        if running:
            self.btn_start.config(state="disabled")
            self.btn_pause.config(state="normal")
            self.btn_cancel.config(state="normal")
        else:
            self.btn_start.config(state="normal")
            self.btn_pause.config(state="disabled")
            self.btn_cancel.config(state="disabled")
            self.pause_event.clear()
            self.btn_pause.config(text="⏸ Пауза")

    # ======================== История ========================

    def _refresh_history_ui(self):
        for item in self.hist_tree.get_children():
            self.hist_tree.delete(item)

        for entry in reversed(self.history_mgr.entries):
            self.hist_tree.insert("", "end", values=(
                entry.get("datetime", ""),
                os.path.basename(entry.get("src", "")),
                os.path.basename(entry.get("dst", "")),
                entry.get("size", ""),
                entry.get("status", ""),
                entry.get("avg_speed_kbps", ""),
                entry.get("interruptions", ""),
                entry.get("md5_src", "")[:28],
                entry.get("md5_dst", "")[:28],
            ))

    def _history_double_click(self, event=None):
        """Двойной клик — открыть папку с файлом."""
        self._history_menu_open_folder()

    def _history_right_click(self, event=None):
        """Правый клик — показать контекстное меню."""
        sel = self.hist_tree.identify_row(event.y)
        if sel:
            self.hist_tree.selection_set(sel)
            self.hist_menu.post(event.x_root, event.y_root)

    def _get_selected_entry(self):
        """Получить выбранную запись из истории."""
        sel = self.hist_tree.selection()
        if not sel:
            return None
        idx = self.hist_tree.index(sel[0])
        if idx >= len(self.history_mgr.entries):
            return None
        return self.history_mgr.entries[idx]

    def _history_menu_open_folder(self):
        """Открыть папку с файлом."""
        entry = self._get_selected_entry()
        if not entry:
            return
        dst = entry.get("dst", "")
        dst_dir = os.path.dirname(dst)
        dst_file = os.path.basename(dst)

        # Если файл существует — открыть папку и выделить его
        full_path = dst
        if os.path.exists(full_path):
            subprocess.Popen(f'explorer /select,"{os.path.normpath(full_path)}"')
        elif os.path.isdir(dst_dir):
            os.startfile(dst_dir)
        else:
            messagebox.showwarning("Папка не найдена", f"Папка не существует:\n{dst_dir}")

    def _history_menu_retry(self):
        """Повторить копирование из выбранной записи."""
        entry = self._get_selected_entry()
        if not entry:
            return

        src = entry.get("src", "")
        dst = entry.get("dst", "")
        dst_dir = os.path.dirname(dst)
        status = entry.get("status", "")

        # Для записей «в процессе»/«пауза» — предложить докачку
        if status in (STATUS_IN_PROGRESS, STATUS_PAUSED):
            part_path = dst + PART_EXTENSION
            meta_path = dst + META_EXTENSION
            pmeta_path = dst + PARTIAL_META_EXTENSION

            has_partial = (os.path.exists(part_path) or
                           os.path.exists(meta_path) or
                           os.path.exists(pmeta_path))

            if has_partial:
                copied = 0
                total = entry.get("size", "0")
                for mp in (meta_path, pmeta_path):
                    m = load_meta(mp)
                    if m:
                        copied = m.get("copied_bytes", 0)
                        total = fmt_size(m.get("total_size", 0))
                        break

                if messagebox.askyesno(
                        "Возобновить",
                        f"Файл: {os.path.basename(src)}\n"
                        f"Скопировано: {fmt_size(copied)} из {total}\n\n"
                        f"Продолжить копирование?"
                ):
                    self.var_src.set(src)
                    self.var_dst.set(dst_dir)
                    self._start_copy()
            else:
                if messagebox.askyesno(
                        "Нет .part файла",
                        f"Временный файл не найден.\n"
                        f"Начать копирование заново?"
                ):
                    self.var_src.set(src)
                    self.var_dst.set(dst_dir)
                    self._start_copy()
            return

        # Для завершённых записей — повторить копирование
        if not os.path.exists(src):
            messagebox.showwarning("Повтор", f"Источник не найден:\n{src}")
            return
        if messagebox.askyesno(
                "Повторить",
                f"Скопировать заново?\n{os.path.basename(src)}"
        ):
            self.var_src.set(src)
            self.var_dst.set(dst_dir)
            self._start_copy()

    def _history_export_csv(self):
        p = filedialog.asksaveasfilename(
            title="Экспорт CSV", defaultextension=".csv",
            filetypes=[("CSV", "*.csv")],
            initialfile=f"history_{datetime.now():%Y%m%d_%H%M%S}.csv")
        if p:
            self.history_mgr.export_csv(p)
            messagebox.showinfo("Экспорт", f"Сохранено:\n{p}")

    def _history_clear(self):
        if not messagebox.askyesno("История", "Очистить историю?"):
            return
        self.history_mgr.clear()
        self._refresh_history_ui()

    # ======================== Настройки / Утилиты ========================

    def _update_chunk_sizer(self):
        self.chunk_sizer.mode = self.var_chunk_mode.get()
        try:
            self.chunk_sizer.manual_size = int(self.var_manual_chunk.get())
        except ValueError:
            pass

    def _parse_speed(self) -> float | None:
        try:
            v = float(self.var_speed.get())
            if v < 0:
                raise ValueError
            return v
        except ValueError:
            messagebox.showerror("Ошибка", "Лимит скорости >= 0")
            return None

    def _parse_retry_max(self) -> int:
        try:
            return max(1, min(int(self.var_retry_max.get()), 50))
        except ValueError:
            return NETWORK_RETRY_MAX

    def _parse_retry_base(self) -> int:
        try:
            return max(1, min(int(self.var_retry_base.get()), 60))
        except ValueError:
            return NETWORK_RETRY_BASE

    @staticmethod
    def _free_space(path: str):
        try:
            return shutil.disk_usage(path).free
        except Exception:
            return None

    # ======================== Автоопределение незавершённых ========================

    def _check_and_offer_resume(self):
        """При запуске найти .part файлы и синхронизировать с историей."""
        partials = detect_partials(self.config.get("dst_dir"))
        if not partials:
            return

        resumed_any = False
        for p in partials:
            src = p["src"]
            dst = p["dst"]
            copied = p["copied_bytes"]
            total = p["total_size"]

            # Найти существующую запись в истории
            hist_idx = self.history_mgr.find_in_progress(src, dst)

            if hist_idx is not None:
                # Обновить прогресс в существующей записи
                self.history_mgr.update(hist_idx, {
                    "status": STATUS_PAUSED,
                    "size": fmt_size(total),
                    "avg_speed_kbps": "—",
                    "md5_src": "—",
                    "md5_dst": "—",
                })
                resumed_any = True
                logger.info(f"Synced history entry for {os.path.basename(dst)}")
            else:
                # Создать новую запись в истории
                self.history_mgr.add({
                    "src": src,
                    "dst": dst,
                    "size": fmt_size(total),
                    "datetime": p.get("timestamp", "")[:16].replace("T", " "),
                    "status": STATUS_PAUSED,
                    "avg_speed_kbps": "—",
                    "interruptions": p.get("interruptions", 0),
                    "md5_src": "—",
                    "md5_dst": f"Частично: {fmt_size(copied)}",
                })
                resumed_any = True
                logger.info(f"Created history entry for {os.path.basename(dst)}")

        if resumed_any:
            self._refresh_history_ui()

        # Показать диалог если есть незавершённые
        lines = []
        for p in partials:
            name = os.path.basename(p["dst"])
            lines.append(
                f"  {name}: {fmt_size(p['copied_bytes'])} / "
                f"{fmt_size(p['total_size'])}"
            )

        msg = ("Найдены незавершённые файлы:\n\n" + "\n".join(lines) +
               "\n\nПродолжить копирование первого из списка?\n"
               "(Также можно дважды кликнуть по записи в вкладке «История»)")

        if messagebox.askyesno("Возобновить", msg):
            p = partials[0]
            self.var_src.set(p["src"])
            self.var_dst.set(os.path.dirname(p["dst"]))
            logger.info(f"Resume offered for {p['src']}")

    # ======================== Закрытие ========================

    def _on_close(self):
        """При закрытии: остановить копирование, сохранить мету и историю."""
        self._save_settings()

        if self.copier_thread and self.copier_thread.is_alive():
            logger.info("App closing — pausing copy…")
            # Пауза: копировальщик сохранит .meta и выйдет
            self.pause_event.set()
            self.copier_thread.join(timeout=5)
            if self.copier_thread.is_alive():
                logger.warning("Thread didn't stop in 5s, forcing cancel.")
                self.cancel_event.set()
                self.copier_thread.join(timeout=3)

        # Обновить историю независимо от того, был ли поток
        if self._history_index is not None:
            self.history_mgr.update(self._history_index, {
                "status": STATUS_PAUSED,
            })

        logger.info("Application closed.")
        self.root.destroy()

    def _save_settings(self):
        speed = self._parse_speed()
        if speed is not None:
            self.config["speed_limit_kbps"] = speed
        self.config["dst_dir"] = self.var_dst.get().strip()
        self.config["chunk_mode"] = self.var_chunk_mode.get()
        try:
            self.config["manual_chunk_size"] = int(self.var_manual_chunk.get())
        except ValueError:
            pass
        try:
            self.config["network_retry_max"] = int(self.var_retry_max.get())
        except ValueError:
            pass
        try:
            self.config["network_retry_base"] = int(self.var_retry_base.get())
        except ValueError:
            pass
        self.config["window_geometry"] = self.root.geometry()
        save_config(self.config)

# ===================================================================
# Entry point
# ===================================================================

def main():
    logger.info("Application started (v3.1).")
    root = tk.Tk()
    st = ttk.Style()
    try:
        st.theme_use("vista")
    except Exception:
        pass
    app = SMBDownloaderApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
