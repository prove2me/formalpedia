-- Prove2me | solution 1 for ActuarialValuation.cm1ServiceOneYearSurvival_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:31:59.231819+00:00
-- url     : https://prove2.me/submissions/165831ef-4c0a-4ae5-a4f7-2f4c99373686

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ServiceOneYearSurvival
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (t : ℕ) (ht : 0 < l t) (h : l (t+1) ≤ l t) : cm1ServiceOneYearSurvival l t ≤ 1 := by
  change l (t+1) / l t ≤ 1
  exact (div_le_iff₀ ht).mpr (by linarith)
