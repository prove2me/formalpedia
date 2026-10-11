-- Prove2me | solution 1 for ActuarialValuation.exMax_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T06:41:10.366001+00:00
-- url     : https://prove2.me/submissions/a4f82cd2-344c-4f34-9133-e596d602cfca

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_exMaxOfIndependent
open ActuarialValuation

theorem solution(F : ℝ → ℝ) (x : ℝ) : exMaxOfIndependent F 0 x=1 := by
  simp [exMaxOfIndependent]
