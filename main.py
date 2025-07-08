# -*- coding: utf-8 -*-

import tkinter as tk
from tkinter import ttk, messagebox, font
import json
import csv
from datetime import datetime, timedelta, date
import os
import math
import sys
import platform
import threading
import time
import logging
import random
from collections import defaultdict

# --- Application Configuration ---
CONFIG_FILE = "config.json"
LOG_FILE = "log.csv"
QUOTES_FILE = "quotes.json"
APP_LOG_FILE = "log.log"

# Default settings
DEFAULT_SETTINGS = {
    "session_duration_minutes": 45,
    "obstacle_limit_minutes": 10,
    "log_obstacle_details": True,
    "status_indicator_enabled": True,
    "obstacle_sound_enabled": True,
    "theme": "light",
    "last_backup_prompt_date": ""
}

# --- Theme Color Palettes ---
THEMES = {
    "light": {
        "bg": "#F5F5F5", "fg": "#212121", "bg_alt": "#FFFFFF", "fg_alt": "#616161",
        "accent": "#2196F3", "success": "#4CAF50", "warning": "#FFC107", "error": "#F44336",
        "green_dark": "#27AE60", "orange_dark": "#E67E22"
    },
    "dark": {
        "bg": "#212121", "fg": "#FFFFFF", "bg_alt": "#424242", "fg_alt": "#BDBDBD",
        "accent": "#448AFF", "success": "#66BB6A", "warning": "#FFEE58", "error": "#EF5350",
        "green_dark": "#66BB6A", "orange_dark": "#FFA726"
    }
}

class FocusSessionApp:
    def __init__(self, root_window):
        self.root = root_window
        self.settings = {}
        self.load_settings()

        # --- Font Definitions ---
        self.FONT_H1 = font.Font(family="Verdana", size=12, weight="bold")
        self.FONT_H2 = font.Font(family="Verdana", size=11, weight="bold")
        self.FONT_NORMAL = font.Font(family="Verdana", size=10)
        self.FONT_SMALL = font.Font(family="Verdana", size=9)
        self.FONT_BUTTON = font.Font(family="Verdana", size=10, weight="bold")
        self.FONT_TIMER = font.Font(family="Arial", size=28, weight="bold")
        self.FONT_QUOTE = font.Font(family="Verdana", size=9, slant="italic")
        self.FONT_STREAK = font.Font(family="Verdana", size=10, weight="bold")
        self.FONT_INDICATOR = font.Font(family="Helvetica", size=8, weight="bold")
        
        # --- Style and Theme Configuration ---
        self.style = ttk.Style(self.root)
        self.apply_theme()
        
        self.root.title("Focus")
        self.root.minsize(420, 500)
        self.root.geometry("420x500")

        self.setup_logging()

        # --- Application State ---
        self.state = "IDLE"
        self.current_task = ""
        self.session_start_time = None
        self.session_end_time = None
        self.obstacle_start_time = None
        self.time_left_in_session = timedelta(0)
        self.obstacle_count = 0
        self.total_obstacle_time = timedelta(0)
        
        self.status_indicator = None
        self.status_frame = None
        self.status_time_label = None
        
        ### ZMIANA: Inicjalizacja list na etykiety z gwiazdami ###
        self.idle_star_labels = []
        self.session_star_labels = []
        
        self.quotes = []
        self.available_quotes = []

        # --- Run startup tasks ---
        self._check_for_backup_reminder()
        self.load_quotes()
        self.setup_ui()
        
        self.update_session_counts()
        self.update_streak_display()
        self.update_stars_display()
        
        self.update_timer()
        self.root.protocol("WM_DELETE_WINDOW", self.on_closing)
        self.force_indicator_topmost_loop()

    def setup_logging(self):
        logging.basicConfig(level=logging.INFO, 
                            format='%(asctime)s - %(levelname)s - %(message)s',
                            handlers=[logging.FileHandler(APP_LOG_FILE, encoding='utf-8'), logging.StreamHandler()])
        self.logger = logging.getLogger(__name__)
        self.logger.info("Application started.")

    def _format_timedelta_hhmmss(self, td: timedelta) -> str:
        if not isinstance(td, timedelta) or td.total_seconds() < 0: return "00:00:00"
        seconds_total = int(td.total_seconds())
        return f"{seconds_total//3600:02d}:{(seconds_total%3600)//60:02d}:{seconds_total%60:02d}"

    def apply_theme(self):
        theme_name = self.settings.get("theme", "light")
        self.colors = THEMES[theme_name]
        
        self.root.configure(bg=self.colors['bg'])
        self.style.theme_use('clam')

        self.style.configure('.', background=self.colors['bg'], foreground=self.colors['fg'], font=self.FONT_NORMAL)
        self.style.configure('TFrame', background=self.colors['bg'])
        self.style.configure('TLabel', background=self.colors['bg'], foreground=self.colors['fg'], padding=5)
        self.style.configure('H1.TLabel', font=self.FONT_H1)
        self.style.configure('H2.TLabel', font=self.FONT_H2)
        self.style.configure('Quote.TLabel', font=self.FONT_QUOTE, foreground=self.colors['fg_alt'])
        self.style.configure('TButton', padding=8, font=self.FONT_BUTTON, borderwidth=0)
        self.style.map('TButton', background=[('active', self.colors['accent'])])
        self.style.configure('Success.TButton', background=self.colors['success'], foreground="#FFFFFF")
        self.style.map('Success.TButton', background=[('active', self.colors['green_dark'])])
        self.style.configure('Error.TButton', background=self.colors['error'], foreground="#FFFFFF")
        self.style.map('Error.TButton', background=[('active', '#C62828')])
        self.style.configure('TEntry', fieldbackground=self.colors['bg_alt'], foreground=self.colors['fg'], borderwidth=1, relief='flat')
        self.style.map('TEntry', bordercolor=[('focus', self.colors['accent'])])
        self.style.configure('TCheckbutton', background=self.colors['bg'], foreground=self.colors['fg'])
        self.style.map('TCheckbutton', indicatorbackground=[('selected', self.colors['accent'])])
        self.style.configure("Treeview", background=self.colors['bg_alt'], fieldbackground=self.colors['bg_alt'], foreground=self.colors['fg'], rowheight=25)
        self.style.map("Treeview", background=[('selected', self.colors['accent'])])
        self.style.configure("Treeview.Heading", background=self.colors['bg'], font=self.FONT_BUTTON)
        self.style.map("Treeview.Heading", background=[('active', self.colors['bg_alt'])])


    def setup_ui(self):
        main_frame = ttk.Frame(self.root, padding=(20, 15))
        main_frame.pack(fill=tk.BOTH, expand=True)
        main_frame.columnconfigure(0, weight=1)

        self.idle_frame = ttk.Frame(main_frame)
        self.idle_frame.grid(row=0, column=0, sticky="nsew")
        self.idle_frame.columnconfigure(0, weight=1)

        ttk.Label(self.idle_frame, text="What do you want to focus on now?", style='H1.TLabel').pack(pady=(10, 10))
        self.task_entry = ttk.Entry(self.idle_frame, width=40, font=self.FONT_NORMAL)
        self.task_entry.pack(fill=tk.X, ipady=6, pady=5)
        self.task_entry.bind("<Return>", lambda e: self.start_session())
        
        self.start_button = ttk.Button(self.idle_frame, text="▶ Start Session", command=self.start_session, style='Success.TButton')
        self.start_button.pack(pady=15, ipady=8, fill=tk.X)
        
        info_frame = ttk.Frame(self.idle_frame)
        info_frame.pack(pady=20, fill=tk.X, side=tk.BOTTOM)
        info_frame.columnconfigure(0, weight=1)
        info_frame.columnconfigure(1, weight=1)
        
        self.streak_label = ttk.Label(info_frame, text="🔥 Streak: 0 days", font=self.FONT_STREAK)
        self.streak_label.grid(row=0, column=0, sticky='w')
        self.sessions_count_label = ttk.Label(info_frame, text="Completed Today: 0", font=self.FONT_NORMAL)
        self.sessions_count_label.grid(row=0, column=1, sticky='e')

        ### ZMIANA: Stworzenie ramki i 5 etykiet dla gwiazd na ekranie głównym ###
        idle_stars_frame = ttk.Frame(info_frame)
        idle_stars_frame.grid(row=1, column=0, columnspan=2, pady=(5,0))
        for _ in range(5):
            lbl = ttk.Label(idle_stars_frame, text="☆", font=self.FONT_H2)
            lbl.pack(side=tk.LEFT, padx=1)
            self.idle_star_labels.append(lbl)

        self.session_frame = ttk.Frame(main_frame)
        self.session_frame.columnconfigure(0, weight=1)
        
        self.task_label = ttk.Label(self.session_frame, text="", wraplength=380, justify='center', style='H2.TLabel')
        self.task_label.pack(pady=5)
        
        ### ZMIANA: Stworzenie ramki i 5 etykiet dla gwiazd na ekranie sesji ###
        session_stars_frame = ttk.Frame(self.session_frame)
        session_stars_frame.pack(pady=(0, 5))
        for _ in range(5):
            lbl = ttk.Label(session_stars_frame, text="☆", font=self.FONT_H2)
            lbl.pack(side=tk.LEFT, padx=1)
            self.session_star_labels.append(lbl)

        self.timer_canvas = tk.Canvas(self.session_frame, width=220, height=220, bg=self.colors['bg'], highlightthickness=0)
        self.timer_canvas.pack(pady=10)
        
        self.obstacle_label = ttk.Label(self.session_frame, text="", foreground=self.colors['warning'], font=self.FONT_NORMAL)

        self.quote_label = ttk.Label(self.session_frame, text="", wraplength=380, justify='center', style='Quote.TLabel')
        self.quote_label.pack(side=tk.BOTTOM, pady=(10, 5))
        
        session_buttons_frame = ttk.Frame(self.session_frame)
        session_buttons_frame.pack(fill=tk.X, pady=10, expand=False, side=tk.BOTTOM)

        session_buttons_frame.columnconfigure(0, weight=1)
        session_buttons_frame.columnconfigure(1, weight=1)
        session_buttons_frame.rowconfigure(0, weight=1)
        session_buttons_frame.rowconfigure(1, weight=1)

        self.obstacle_button = ttk.Button(session_buttons_frame, text="⏸️ Obstacle", command=self.toggle_obstacle)
        self.obstacle_button.grid(row=0, column=0, sticky="ew", padx=5, pady=3)

        self.cancel_button = ttk.Button(session_buttons_frame, text="⏹️ Cancel", command=self.cancel_session, style='Error.TButton')
        self.cancel_button.grid(row=0, column=1, sticky="ew", padx=5, pady=3)

        self.plus_5m_button = ttk.Button(session_buttons_frame, text="+5 min", command=lambda: self.adjust_session_time(5))
        self.plus_5m_button.grid(row=1, column=0, sticky="ew", padx=5, pady=3)
        
        self.plus_1m_button = ttk.Button(session_buttons_frame, text="+1 min", command=lambda: self.adjust_session_time(1))
        self.plus_1m_button.grid(row=1, column=1, sticky="ew", padx=5, pady=3)
        
        menubar = tk.Menu(self.root)
        self.root.config(menu=menubar)
        file_menu = tk.Menu(menubar, tearoff=0)
        file_menu.add_command(label="⚙️ Settings", command=self.open_settings)
        file_menu.add_command(label="📊 Statistics (Last 14 Days)", command=self.show_statistics)
        file_menu.add_command(label="📁 Open Log File", command=self.open_log_file)
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self.on_closing)
        menubar.add_cascade(label="File", menu=file_menu)

    def _check_for_backup_reminder(self):
        """Checks if it's time to prompt the user for a backup."""
        today = date.today()
        last_prompt_str = self.settings.get("last_backup_prompt_date", "")

        if not last_prompt_str:
            self.settings["last_backup_prompt_date"] = today.isoformat()
            self.save_settings()
            return

        try:
            last_prompt_date = date.fromisoformat(last_prompt_str)
            days_since_last = (today - last_prompt_date).days

            if days_since_last >= 3:
                self.logger.info(f"Time for backup prompt. Days since last: {days_since_last}")
                self._show_backup_prompt(today)
        except (ValueError, TypeError) as e:
            self.logger.error(f"Could not parse last_backup_prompt_date: {e}")
            self.settings["last_backup_prompt_date"] = today.isoformat()
            self.save_settings()

    def _show_backup_prompt(self, today):
        """Displays the backup prompt and handles the user's choice."""
        title = "Backup Reminder"
        message = (
            "It's been 3 or more days. It's recommended to create a backup of your 'log.csv' file.\n\n"
            "Press OK to clear the log file for a new period.\n"
            "Press Cancel to be reminded later."
        )
        
        self.root.lift()
        user_choice_is_ok = messagebox.askokcancel(title, message)

        if user_choice_is_ok:
            self._clear_log_file()
            self.settings["last_backup_prompt_date"] = today.isoformat()
            self.save_settings()
            messagebox.showinfo("Log Cleared", "The log file has been cleared. The headers have been preserved.")
            self.update_session_counts()
            self.update_streak_display()

    def _clear_log_file(self):
        """Clears the content of the log file, but preserves the header row."""
        if not os.path.exists(LOG_FILE):
            self.logger.info("Log file does not exist. Nothing to clear.")
            return

        try:
            with open(LOG_FILE, 'r+', encoding='utf-8') as f:
                header = f.readline()
                f.seek(0)
                f.truncate()
                f.write(header)
            self.logger.info("Log file content has been cleared, header preserved.")
        except IOError as e:
            self.logger.error(f"Could not clear log file: {e}")
            messagebox.showerror("Error", f"Could not clear log file:\n{e}")
    
    def switch_view(self):
        if self.state in ["SESSION_RUNNING", "OBSTACLE_ACTIVE"]:
            self.idle_frame.grid_remove()
            self.session_frame.grid(row=0, column=0, sticky="nsew")
            if self.settings["status_indicator_enabled"]:
                self.create_status_indicator()
        else:
            self.session_frame.grid_remove()
            self.idle_frame.grid(row=0, column=0, sticky="nsew")
            self.quote_label.config(text="")
            self.destroy_status_indicator()

    def start_session(self):
        task = self.task_entry.get().strip()
        if not task: task = f"Task {datetime.now().strftime('%Y-%m-%d')}"
        self.current_task = task
        self.task_label.config(text=self.current_task)
        self.state = "SESSION_RUNNING"
        self.session_start_time = datetime.now()
        self.session_end_time = self.session_start_time + timedelta(minutes=self.settings["session_duration_minutes"])
        self.obstacle_count = 0
        self.total_obstacle_time = timedelta(0)
        if self.quotes:
            if not self.available_quotes:
                self.available_quotes = self.quotes.copy()
            chosen_quote = random.choice(self.available_quotes)
            self.available_quotes.remove(chosen_quote)
            self.quote_label.config(text=f"\"{chosen_quote}\"")
        self.switch_view()

    def adjust_session_time(self, minutes_to_add):
        """Dodaje podaną liczbę minut do czasu zakończenia sesji."""
        if self.state == "SESSION_RUNNING":
            self.session_end_time += timedelta(minutes=minutes_to_add)
            self.logger.info(f"Added {minutes_to_add} minutes. New end time: {self.session_end_time.strftime('%H:%M:%S')}")

    def cancel_session(self):
        if messagebox.askyesno("Cancel Session", "Are you sure you want to cancel the current session? Progress will not be saved."):
            self.state = "IDLE"
            self.task_entry.delete(0, tk.END)
            self.switch_view()

    def toggle_obstacle(self):
        if self.state == "SESSION_RUNNING":
            self.state = "OBSTACLE_ACTIVE"
            self.time_left_in_session = self.session_end_time - datetime.now()
            self.obstacle_start_time = datetime.now()
            self.obstacle_count += 1
            self.obstacle_button.config(text="▶️ Resume", style='Success.TButton')
            self.obstacle_label.pack(pady=5, side=tk.BOTTOM)
        elif self.state == "OBSTACLE_ACTIVE":
            self.state = "SESSION_RUNNING"
            self.total_obstacle_time += datetime.now() - self.obstacle_start_time
            self.session_end_time = datetime.now() + self.time_left_in_session
            self.obstacle_button.config(text="⏸️ Obstacle", style='TButton')
            self.obstacle_label.pack_forget()

    def update_timer(self):
        display_time = None
        display_color = self.colors['bg_alt']
        if self.state == "SESSION_RUNNING":
            time_left = self.session_end_time - datetime.now()
            if time_left.total_seconds() <= 0:
                self.complete_session()
            else:
                total_duration = (self.session_end_time - self.session_start_time).total_seconds()
                progress = time_left.total_seconds() / total_duration if total_duration > 0 else 0
                self.draw_progress_circle(progress, self._format_timedelta_hhmmss(time_left), self.colors['green_dark'])
                display_time = time_left
                display_color = self.colors['green_dark']

        elif self.state == "OBSTACLE_ACTIVE":
            obstacle_time = datetime.now() - self.obstacle_start_time
            self.obstacle_label.config(text=f"Break duration: {self._format_timedelta_hhmmss(obstacle_time)}")
            self.draw_progress_circle(1, self._format_timedelta_hhmmss(self.time_left_in_session), self.colors['orange_dark'])
            display_time = self.time_left_in_session
            display_color = self.colors['orange_dark']

        self.update_status_indicator(display_time, display_color)
        self.root.after(1000, self.update_timer)

    def draw_progress_circle(self, progress_ratio, text, color):
        self.timer_canvas.delete("all")
        width, padding = 220, 15
        bounding_box = (padding, padding, width - padding, width - padding)
        self.timer_canvas.create_arc(bounding_box, start=90, extent=360, style=tk.ARC, outline=self.colors['bg_alt'], width=10)
        if progress_ratio > 0:
            self.timer_canvas.create_arc(bounding_box, start=90, extent=-progress_ratio * 359.9, style=tk.ARC, outline=color, width=11)
        self.timer_canvas.create_text(width / 2, width / 2, text=text, font=self.FONT_TIMER, fill=self.colors['fg'])

    def complete_session(self):
        self.state = "COMPLETING"
        messagebox.showinfo("Session Completed!", f"Congratulations! You have completed the session for:\n\n'{self.current_task}'")
        self.ask_for_habits()

    def ask_for_habits(self):
        dialog = tk.Toplevel(self.root)
        dialog.title("Session Summary")
        dialog.configure(bg=self.colors['bg'])
        dialog.transient(self.root)
        dialog.grab_set()
        dialog.resizable(False, False)
        main_frame = ttk.Frame(dialog, padding=20)
        main_frame.pack(fill=tk.BOTH, expand=True)
        ttk.Label(main_frame, text="Which good habits did you maintain?").pack(pady=10)
        mbs_var = tk.BooleanVar(value=True)
        bt_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(main_frame, text="mbs (music without lyrics)", variable=mbs_var).pack(anchor="w", padx=20, pady=5)
        ttk.Checkbutton(main_frame, text="bt (without phone)", variable=bt_var).pack(anchor="w", padx=20, pady=5)
        
        def on_save():
            self.log_session(mbs_checked=mbs_var.get(), bt_checked=bt_var.get())
            dialog.destroy()
            
        ttk.Button(main_frame, text="Save and Continue", command=on_save, style='Success.TButton').pack(pady=15, ipady=5, fill=tk.X)
        
        self.root.wait_window(dialog)
        
        self.finalize_session_completion()

    def finalize_session_completion(self):
        self.state = "IDLE"
        self.task_entry.delete(0, tk.END)
        
        self.update_session_counts()
        self.update_streak_display()
        self.update_stars_display()
        
        self.switch_view()

    def log_session(self, mbs_checked, bt_checked):
        file_exists = os.path.isfile(LOG_FILE) and os.path.getsize(LOG_FILE) > 0
        headers = ["timestamp", "task_completed", "mbs", "bt", "is_pre_noon", "obstacle_count", "total_obstacle_time_min"]
        with open(LOG_FILE, 'a', newline='', encoding='utf-8') as f:
            writer = csv.writer(f)
            if not file_exists:
                writer.writerow(headers)
            completion_time = datetime.now()
            row_data = [
                completion_time.strftime("%Y-%m-%d %H:%M:%S"), self.current_task,
                1 if mbs_checked else 0, 1 if bt_checked else 0,
                1 if completion_time.hour < 12 else 0, self.obstacle_count,
                round(self.total_obstacle_time.total_seconds() / 60, 2)
            ]
            writer.writerow(row_data)

    def _calculate_streak(self):
        if not os.path.exists(LOG_FILE): return 0
        try:
            with open(LOG_FILE, 'r', newline='', encoding='utf-8') as f:
                reader = csv.DictReader(f)
                session_dates = {datetime.strptime(row['timestamp'], "%Y-%m-%d %H:%M:%S").date() for row in reader}
            if not session_dates: return 0
            sorted_dates = sorted(list(session_dates), reverse=True)
            if sorted_dates[0] != date.today(): return 0
            streak = 0
            expected_date = date.today()
            for d in sorted_dates:
                if d == expected_date:
                    streak += 1
                    expected_date -= timedelta(days=1)
                elif d < expected_date:
                    break
            return streak
        except (IOError, KeyError, ValueError, IndexError):
            return 0

    def update_streak_display(self):
        streak = self._calculate_streak()
        self.streak_label.config(text=f"🔥 Streak: {streak} days")

    def _get_today_sessions_count(self):
        """Zwraca liczbę sesji ukończonych dzisiaj."""
        count = 0
        today_str = datetime.now().strftime("%Y-%m-%d")
        if os.path.exists(LOG_FILE):
            try:
                with open(LOG_FILE, 'r', newline='', encoding='utf-8') as f:
                    reader = csv.reader(f)
                    header = next(reader)
                    date_col_idx = header.index('timestamp')
                    for row in reader:
                        if row and row[date_col_idx].startswith(today_str):
                            count += 1
            except (IOError, StopIteration, ValueError, IndexError):
                pass
        return count

    def update_session_counts(self):
        """Aktualizuje etykietę z liczbą ukończonych dzisiaj sesji."""
        count = self._get_today_sessions_count()
        self.sessions_count_label.config(text=f"Completed Today: {count}")

    ### ZMIANA: Przebudowana funkcja do aktualizacji gwiazd ###
    def update_stars_display(self):
        """Aktualizuje 5 etykiet z gwiazdami, zmieniając ich tekst i kolor."""
        count = self._get_today_sessions_count()
        
        all_labels = self.idle_star_labels + self.session_star_labels

        for i in range(5):
            # Ustalanie wyglądu dla i-tej gwiazdy
            if i < count:
                star_text = '⭐'
                star_color = self.colors['warning']  # Żółty kolor dla zapełnionej gwiazdy
            else:
                star_text = '☆'
                star_color = self.colors['fg']  # Domyślny kolor tekstu dla pustej gwiazdy

            # Aktualizacja i-tej gwiazdy na obu ekranach
            if len(self.idle_star_labels) > i:
                self.idle_star_labels[i].config(text=star_text, foreground=star_color)
            if len(self.session_star_labels) > i:
                self.session_star_labels[i].config(text=star_text, foreground=star_color)

    def load_settings(self):
        if os.path.exists(CONFIG_FILE):
            try:
                with open(CONFIG_FILE, 'r') as f: self.settings = json.load(f)
            except (json.JSONDecodeError, IOError): self.settings = {}
        for key, value in DEFAULT_SETTINGS.items():
            self.settings.setdefault(key, value)

    def load_quotes(self):
        if os.path.exists(QUOTES_FILE):
            try:
                with open(QUOTES_FILE, 'r', encoding='utf-8') as f:
                    data = json.load(f)
                self.quotes = data.get("quotes", [])
                self.available_quotes = self.quotes.copy()
            except (json.JSONDecodeError, IOError) as e:
                self.logger.error(f"Failed to load quotes file: {e}")
                self.quotes, self.available_quotes = [], []
        else:
            self.quotes, self.available_quotes = [], []

    def save_settings(self):
        try:
            with open(CONFIG_FILE, 'w') as f: json.dump(self.settings, f, indent=4)
        except IOError: messagebox.showerror("Error", "Could not save settings.")
    
    def open_settings(self):
        settings_window = tk.Toplevel(self.root)
        settings_window.title("Settings")
        settings_window.configure(bg=self.colors['bg'])
        main_frame = ttk.Frame(settings_window, padding=20)
        main_frame.pack(fill=tk.BOTH, expand=True)
        ttk.Label(main_frame, text="Application Theme:").grid(row=0, column=0, sticky='w', pady=5)
        theme_var = tk.StringVar(value=self.settings.get("theme", "light").capitalize())
        theme_combo = ttk.Combobox(main_frame, textvariable=theme_var, values=["Light", "Dark"], state="readonly")
        theme_combo.grid(row=0, column=1, sticky='ew', pady=5)
        indicator_var = tk.BooleanVar(value=self.settings.get("status_indicator_enabled", True))
        ttk.Checkbutton(main_frame, text="Enable corner status indicator", variable=indicator_var).grid(row=1, column=0, columnspan=2, sticky="w", pady=5)
        def save_and_close():
            self.settings["theme"] = theme_var.get().lower()
            self.settings["status_indicator_enabled"] = indicator_var.get()
            self.save_settings()
            self.apply_theme()
            if not self.settings["status_indicator_enabled"]:
                self.destroy_status_indicator()
            messagebox.showinfo("Saved", "Settings have been saved.")
            settings_window.destroy()
        ttk.Button(main_frame, text="Save and Close", command=save_and_close).grid(row=5, column=0, columnspan=2, pady=20)

    def show_statistics(self):
        stats_window = tk.Toplevel(self.root)
        stats_window.title("Statistics - Last 14 Days")
        stats_window.geometry("520x620")
        stats_window.resizable(False, False)
        stats_window.configure(bg=self.colors['bg'])
        main_frame = ttk.Frame(stats_window, padding=20)
        main_frame.pack(fill=tk.BOTH, expand=True)
        try:
            with open(LOG_FILE, 'r', newline='', encoding='utf-8') as f:
                reader = csv.DictReader(f)
                log_data = list(reader)
        except (FileNotFoundError, StopIteration):
            ttk.Label(main_frame, text="No data to display.\nLog file does not exist or is empty.").pack(pady=20)
            return
        fourteen_days_ago = date.today() - timedelta(days=14)
        recent_data = [row for row in log_data if datetime.strptime(row['timestamp'], "%Y-%m-%d %H:%M:%S").date() > fourteen_days_ago]
        if not recent_data:
            ttk.Label(main_frame, text="No sessions in the last 14 days.").pack(pady=20)
            return
        total_sessions = len(recent_data)
        total_minutes = total_sessions * self.settings.get("session_duration_minutes", 45)
        hours, minutes = divmod(total_minutes, 60)
        mbs_count = sum(1 for row in recent_data if row.get('mbs') == '1')
        bt_count = sum(1 for row in recent_data if row.get('bt') == '1')
        mbs_percent = (mbs_count / total_sessions) * 100 if total_sessions > 0 else 0
        bt_percent = (bt_count / total_sessions) * 100 if total_sessions > 0 else 0
        summary_frame = ttk.Frame(main_frame)
        summary_frame.pack(fill=tk.X, pady=5)
        summary_frame.columnconfigure(1, weight=1)
        def add_stat_row(row_index, label_text, value_text, color_key=None):
            ttk.Label(summary_frame, text=label_text).grid(row=row_index, column=0, sticky="w", pady=2)
            color = self.colors.get(color_key, self.colors['fg'])
            ttk.Label(summary_frame, text=value_text, foreground=color, font=self.FONT_NORMAL).grid(row=row_index, column=1, sticky="w", padx=10)
        add_stat_row(0, "Completed Sessions:", f"{total_sessions}", 'success')
        add_stat_row(1, "Total Focus Time:", f"{hours}h {minutes}m", 'accent')
        add_stat_row(2, "Habit 'mbs':", f"{mbs_count}/{total_sessions} ({mbs_percent:.1f}%)")
        add_stat_row(3, "Habit 'bt':", f"{bt_count}/{total_sessions} ({bt_percent:.1f}%)")
        ttk.Separator(main_frame, orient='horizontal').pack(fill='x', pady=15, padx=5)
        daily_stats = defaultdict(lambda: {'sessions': 0, 'mbs': 0, 'bt': 0})
        for row in recent_data:
            day_str = datetime.strptime(row['timestamp'], "%Y-%m-%d %H:%M:%S").strftime("%Y-%m-%d")
            daily_stats[day_str]['sessions'] += 1
            if row.get('mbs') == '1': daily_stats[day_str]['mbs'] += 1
            if row.get('bt') == '1': daily_stats[day_str]['bt'] += 1
        tree_frame = ttk.Frame(main_frame)
        tree_frame.pack(fill='both', expand=True)
        columns = ("sessions", "mbs", "bt")
        tree = ttk.Treeview(tree_frame, columns=columns)
        tree.pack(side='left', fill='both', expand=True)
        scrollbar = ttk.Scrollbar(tree_frame, orient="vertical", command=tree.yview)
        scrollbar.pack(side='right', fill='y')
        tree.configure(yscrollcommand=scrollbar.set)
        tree.column("#0", width=120, anchor=tk.W, stretch=tk.NO)
        tree.heading("#0", text="Day", anchor=tk.W)
        tree.column("sessions", width=100, anchor=tk.CENTER)
        tree.heading("sessions", text="Sessions")
        tree.column("mbs", width=100, anchor=tk.CENTER)
        tree.heading("mbs", text="MBS")
        tree.column("bt", width=100, anchor=tk.CENTER)
        tree.heading("bt", text="BT")
        for i in range(14):
            day = date.today() - timedelta(days=i)
            day_str = day.strftime("%Y-%m-%d")
            stats = daily_stats[day_str]
            tree.insert("", "end", text=day_str, values=(stats['sessions'], stats['mbs'], stats['bt']))
        ttk.Button(main_frame, text="Close", command=stats_window.destroy).pack(pady=(15,0), side=tk.BOTTOM)

    def open_log_file(self):
        if not os.path.exists(LOG_FILE):
            messagebox.showinfo("No Logs", "Log file does not exist.")
            return
        try:
            if platform.system() == "Windows": os.startfile(LOG_FILE)
            elif platform.system() == "Darwin": import subprocess; subprocess.call(["open", LOG_FILE])
            else: import subprocess; subprocess.call(["xdg-open", LOG_FILE])
        except Exception as e:
            messagebox.showerror("Error", f"Could not open file: {e}")

    def on_closing(self):
        if self.state != "IDLE":
            if not messagebox.askyesno("Exit?", "A session is in progress. Are you sure you want to exit?"):
                return
        self.destroy_status_indicator()
        self.root.destroy()
    
    def create_status_indicator(self):
        if self.status_indicator and self.status_indicator.winfo_exists():
            return
        self.status_indicator = tk.Toplevel(self.root)
        si = self.status_indicator
        si.overrideredirect(True)
        si.attributes("-topmost", True)
        si.attributes("-alpha", 0.8)
        size, offset_x, offset_y = 21, 15, 40
        x = self.root.winfo_screenwidth() - size - offset_x
        y = self.root.winfo_screenheight() - size - offset_y
        si.geometry(f"{size}x{size}+{x}+{y}")
        self.status_frame = tk.Frame(si, relief=tk.RAISED, bd=1)
        self.status_frame.pack(fill=tk.BOTH, expand=True)
        self.status_time_label = tk.Label(self.status_frame, text="", fg="white", font=self.FONT_INDICATOR)
        self.status_time_label.pack(expand=True)

    def update_status_indicator(self, time_delta, color):
        if not self.settings.get("status_indicator_enabled", True) or not self.status_indicator or not self.status_indicator.winfo_exists():
            return
        display_text = "--"
        if time_delta and time_delta.total_seconds() > 0:
            total_minutes = math.ceil(time_delta.total_seconds() / 60)
            display_text = str(total_minutes)
        self.status_frame.config(bg=color)
        self.status_time_label.config(bg=color, text=display_text)

    def destroy_status_indicator(self):
        if self.status_indicator:
            self.status_indicator.destroy()
            self.status_indicator = None

    def force_indicator_topmost_loop(self):
        if self.status_indicator and self.status_indicator.winfo_exists():
            try:
                self.status_indicator.attributes("-topmost", True)
            except tk.TclError:
                pass
        self.root.after(20000, self.force_indicator_topmost_loop)

if __name__ == "__main__":
    main_window = tk.Tk()
    app = FocusSessionApp(main_window)
    main_window.mainloop()