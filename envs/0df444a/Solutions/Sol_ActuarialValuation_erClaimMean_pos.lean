-- Prove2me | solution 1 for ActuarialValuation.erClaimMean_pos
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T07:09:24.541002+00:00
-- url     : https://prove2.me/submissions/022ca6c4-2fb1-4e0f-921f-773054d35cb5

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erClaimMean
open ActuarialValuation

theorem solution(beta : ℝ) (hb : 0 < beta) : 0 < erClaimMean beta := by
  unfold erClaimMean
  positivity
