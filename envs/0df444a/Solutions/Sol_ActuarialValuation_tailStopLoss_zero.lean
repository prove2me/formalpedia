-- Prove2me | solution 1 for ActuarialValuation.tailStopLoss_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:57:19.808008+00:00
-- url     : https://prove2.me/submissions/f7b90cab-ad8c-454f-9cd8-190acf765e0e

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_tailStopLoss
open ActuarialValuation

theorem solution(p : ℕ → ℝ) (t : ℝ) (ht : 0 ≤ t) : tailStopLoss p 0 t = 0 := by
  unfold tailStopLoss tailExcess
  simp only [zero_add, Finset.sum_range_one, Nat.cast_zero]
  rw [max_eq_right (by linarith)]
  ring
