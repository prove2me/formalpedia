-- Prove2me | solution 1 for ActuarialValuation.exBase_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:31:44.068923+00:00
-- url     : https://prove2.me/submissions/be9ea0f8-92bc-46f3-915a-a2d90df00c50

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_exBase

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (xi sigma x y : ℝ) (hxi : 0≤xi) (hs : 0<sigma) (h : x≤y) : exBase xi sigma x≤exBase xi sigma y := by
  unfold exBase
  have hxy : 0 ≤ y - x := sub_nonneg.mpr h
  have hmul : 0 ≤ xi * (y - x) := mul_nonneg hxi hxy
  have hdiv : 0 ≤ xi * (y - x) / sigma := div_nonneg hmul (le_of_lt hs)
  have heq : (1 + xi * y / sigma) - (1 + xi * x / sigma) = xi * (y - x) / sigma := by ring
  linarith
