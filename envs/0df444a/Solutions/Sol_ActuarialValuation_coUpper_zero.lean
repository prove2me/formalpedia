-- Prove2me | solution 1 for ActuarialValuation.coUpper_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:01:58.857851+00:00
-- url     : https://prove2.me/submissions/e8b41968-4bb9-4389-9a62-79f5f8e484e2

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_coUpper
open ActuarialValuation

theorem solution(u : ℝ) (h : 0≤u) : coUpper u 0=0 := by
  unfold coUpper
  exact min_eq_right h
