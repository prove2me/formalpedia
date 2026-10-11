-- Prove2me | solution 1 for ActuarialValuation.exQuantile_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T09:52:55.55348+00:00
-- url     : https://prove2.me/submissions/11f092ba-5a1a-45fd-86d2-b2d2e9d982e2

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_exQuantile
open ActuarialValuation

theorem solution(xi sigma : ℝ) (hxi : xi≠0) : exQuantile xi sigma 0=0 := by
  simp [exQuantile, Real.rpow_eq_pow]
