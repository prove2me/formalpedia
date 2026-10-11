-- Prove2me | solution 1 for ActuarialValuation.exMax_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T06:47:38.765186+00:00
-- url     : https://prove2.me/submissions/d38a64ed-1633-48bc-8765-9a1420df6dc3

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_exMaxOfIndependent
open ActuarialValuation

theorem solution(F : ℝ → ℝ) (x : ℝ) : exMaxOfIndependent F 1 x=F x := by
  simp [exMaxOfIndependent]
