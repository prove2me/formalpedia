-- Prove2me | Definitions.Def_Aggmetrics_Basic
-- name    : Aggmetrics_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T09:48:28.743219+00:00
-- url     : https://prove2.me/theorems/4de475bd-83e5-49a2-85e3-adf164c6be3f
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Ronaldo C. Prati and the Aggmetrics contributors's pinned Aggmetrics: data-stream metric aggregation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/Basic.lean

import Mathlib
set_option autoImplicit true
open Finset
namespace Aggmetrics
example :
    (∑ τ : Fin 2, (![0.5, 0.5] : Fin 2 → ℝ) τ * (![0.5, 1] : Fin 2 → ℝ) τ = 0.75) ∧
    (∑ τ : Fin 2, (![0.8, 0.2] : Fin 2 → ℝ) τ * (![0.5, 1] : Fin 2 → ℝ) τ = 0.60) := by
  constructor <;> (rw [Fin.sum_univ_two]; norm_num)
end Aggmetrics


