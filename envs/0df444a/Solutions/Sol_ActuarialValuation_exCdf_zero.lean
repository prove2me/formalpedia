-- Prove2me | solution 1 for ActuarialValuation.exCdf_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T06:43:28.512214+00:00
-- url     : https://prove2.me/submissions/493a1429-42b4-4aa6-a36a-d405394d49b3

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_exCdf
open ActuarialValuation

theorem solution(xi sigma : ℝ) (hxi : xi≠0) : exCdf xi sigma 0=0 := by
  simp [exCdf, exSurvival, exBase]
