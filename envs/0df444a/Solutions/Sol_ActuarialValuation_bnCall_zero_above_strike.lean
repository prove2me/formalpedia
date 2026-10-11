-- Prove2me | solution 1 for ActuarialValuation.bnCall_zero_above_strike
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T08:26:52.278988+00:00
-- url     : https://prove2.me/submissions/95594726-d558-4dfa-81fc-9804bb4d96fc

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnCall
open ActuarialValuation

theorem solution(s k : ℝ) (h : s ≤ k) : bnCall s k = 0 := by
  unfold bnCall
  exact max_eq_right (by linarith)
