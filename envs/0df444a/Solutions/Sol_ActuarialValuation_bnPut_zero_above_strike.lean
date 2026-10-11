-- Prove2me | solution 1 for ActuarialValuation.bnPut_zero_above_strike
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T07:10:52.092644+00:00
-- url     : https://prove2.me/submissions/f0322536-829a-43bf-a0ce-72bdc110f4f4

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnPut
open ActuarialValuation

theorem solution(s k : ℝ) (h : k ≤ s) : bnPut s k = 0 := by
  unfold bnPut
  exact max_eq_right (by linarith)
