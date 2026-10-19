-- Prove2me | solution 1 for ActuarialAnnuities.deferred_temp_split
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:08:01.734447+00:00
-- url     : https://prove2.me/submissions/86f6ad58-a996-4a9a-b9b9-902d6087d8f4

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bSurvivalPV

open ActuarialAnnuities

theorem solution (h a n m delta : ℕ) (v : ℝ) (b p : ℕ → ℝ) (ha : a+n+m ≤ h) : bSurvivalPV h a (n+m) 0 delta v b p = bSurvivalPV h a n 0 delta v b p+bSurvivalPV h (a+n) m 0 delta v b p := by
  unfold bSurvivalPV; rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro j _
  split_ifs <;> first | (exfalso; omega) | ring1 | simp_all


