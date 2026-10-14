-- Prove2me | solution 1 for ActuarialAnnuities.path_zero_term
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T08:10:36.474161+00:00
-- url     : https://prove2.me/submissions/81c48536-c7cb-499a-b052-f5860f043831

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bPathPV
open ActuarialAnnuities

theorem solution(h a g delta k : ℕ) (v : ℝ) (b : ℕ → ℝ) : bPathPV h a 0 g delta v b k = 0 := by
  unfold bPathPV
  apply Finset.sum_eq_zero
  intro j _
  rw [if_neg (by omega)]
