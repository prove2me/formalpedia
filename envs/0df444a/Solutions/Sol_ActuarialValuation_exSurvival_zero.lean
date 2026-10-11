-- Prove2me | solution 1 for ActuarialValuation.exSurvival_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T09:53:15.66614+00:00
-- url     : https://prove2.me/submissions/7dea1ef9-4ee9-4a23-b71e-6258ab4d6a09

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_exSurvival
open ActuarialValuation

theorem solution(xi sigma : ℝ) (hxi : xi≠0) : exSurvival xi sigma 0=1 := by
  simp [exSurvival, exBase, Real.rpow_eq_pow]
