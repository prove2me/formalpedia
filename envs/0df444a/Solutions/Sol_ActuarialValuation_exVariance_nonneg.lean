-- Prove2me | solution 1 for ActuarialValuation.exVariance_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:11:05.451268+00:00
-- url     : https://prove2.me/submissions/6334a71b-5ec8-4c32-8488-cb31433b1784

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_exVariance
open ActuarialValuation

theorem solution(xi sigma : ℝ) (hxi : xi < 1/2) : 0≤exVariance xi sigma := by
  unfold exVariance
  apply div_nonneg (sq_nonneg _)
  apply mul_nonneg (sq_nonneg _)
  linarith
