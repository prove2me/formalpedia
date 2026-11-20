-- Prove2me | Definitions.Def_Aggmetrics_DataStreamTemporal
-- name    : Aggmetrics_DataStreamTemporal
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T09:53:28.163408+00:00
-- url     : https://prove2.me/theorems/548e9766-8f12-4b1d-adb1-9f9e5f5db2f8
-- title:
--   Data Stream Temporal
-- statement:
--   Definitions and structural lemmas for Data Stream Temporal, from Ronaldo C. Prati and the Aggmetrics contributors's pinned Aggmetrics: data-stream metric aggregation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean

import Definitions.Def_Aggmetrics_Basic
set_option autoImplicit true
open Finset Matrix
namespace Aggmetrics.DataStream
def outer {m : ℕ} (y p : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun a b => y a * p b
def state {m n : ℕ} (w : Fin n → ℝ) (y p : Fin n → Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  ∑ k, w k • outer (y k) (p k)
def sel {m : ℕ} (j : Fin m) : Matrix (Fin 2) (Fin m) ℝ :=
  Matrix.of fun r l =>
    if r = 0 then (if l = j then 1 else 0) else (if l = j then 0 else 1)
def classTable {m : ℕ} (C : Matrix (Fin m) (Fin m) ℝ) (j : Fin m) : Matrix (Fin 2) (Fin 2) ℝ :=
  sel j * C * (sel j)ᵀ
def lin (a : Fin 4 → ℝ) (T : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  a 0 * T 0 0 + a 1 * T 0 1 + a 2 * T 1 0 + a 3 * T 1 1
noncomputable def measure (a b : Fin 4 → ℝ) (T : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  lin a T / lin b T
def fadeWeight (α : ℝ) (n k : ℕ) : ℝ := (1 - α) * α ^ (n - 1 - k)
def fadeState {m : ℕ} (α : ℝ) (y p : ℕ → Fin m → ℝ) : ℕ → Matrix (Fin m) (Fin m) ℝ
  | 0 => 0
  | n + 1 => α • fadeState α y p n + (1 - α) • outer (y n) (p n)
noncomputable def winWeight (W n k : ℕ) : ℝ := if n - W ≤ k then 1 / (W : ℝ) else 0
noncomputable def winState {m : ℕ} (W : ℕ) (y p : ℕ → Fin m → ℝ) (n : ℕ) :
    Matrix (Fin m) (Fin m) ℝ :=
  ∑ k ∈ range n, winWeight W n k • outer (y k) (p k)
noncomputable def omega {m : ℕ} (b : Fin 4 → ℝ) (C : Matrix (Fin m) (Fin m) ℝ) (j : Fin m) : ℝ :=
  lin b (classTable C j) / ∑ l, lin b (classTable C l)
end Aggmetrics.DataStream


