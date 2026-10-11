-- Prove2me | solution 1 for ActuarialValuation.coUpper_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T06:15:24.772442+00:00
-- url     : https://prove2.me/submissions/4ff028f4-05a9-4578-960d-c5939844ecc4

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_coUpper
open ActuarialValuation

theorem solution(u : ℝ) (h0 : 0≤u) (h1 : u≤1) : coUpper u 1=u := by
  unfold coUpper
  exact min_eq_left h1
