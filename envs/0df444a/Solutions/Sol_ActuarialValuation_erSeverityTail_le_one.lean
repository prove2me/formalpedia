-- Prove2me | solution 1 for ActuarialValuation.erSeverityTail_le_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T12:44:11.672991+00:00
-- url     : https://prove2.me/submissions/28a10f41-0a04-45fd-8045-57777bb21976

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erSeverityTail
open ActuarialValuation

theorem solution(beta x : ℝ) (hb : 0 ≤ beta) (hx : 0 ≤ x) : erSeverityTail beta x ≤ 1 := by
  unfold erSeverityTail
  apply Real.exp_le_one_iff.mpr
  nlinarith [mul_nonneg hb hx]
