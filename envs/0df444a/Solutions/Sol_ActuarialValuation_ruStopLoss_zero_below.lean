-- Prove2me | solution 1 for ActuarialValuation.ruStopLoss_zero_below
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T08:31:14.591883+00:00
-- url     : https://prove2.me/submissions/22119a5a-a1e2-4dd7-97b8-7985acb9eff0

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruStopLoss
open ActuarialValuation

theorem solution(x d : ℝ) (h : x ≤ d) : ruStopLoss x d = 0 := by
  unfold ruStopLoss
  exact max_eq_left (by linarith)
