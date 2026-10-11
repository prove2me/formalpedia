-- Prove2me | solution 1 for ActuarialValuation.bnCall_positive_below_strike
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T09:54:22.66746+00:00
-- url     : https://prove2.me/submissions/37f9293b-e575-4014-bc6e-71a14c92795b

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnCall
open ActuarialValuation

theorem solution(s k : ℝ) (h : k ≤ s) : bnCall s k = s-k := by
  unfold bnCall
  exact max_eq_left (by linarith)
