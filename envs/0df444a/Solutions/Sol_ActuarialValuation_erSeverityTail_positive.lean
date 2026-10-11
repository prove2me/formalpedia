-- Prove2me | solution 1 for ActuarialValuation.erSeverityTail_positive
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T07:20:36.272896+00:00
-- url     : https://prove2.me/submissions/37a315d4-0bff-43a8-8d55-67877f8fd509

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erSeverityTail
open ActuarialValuation

theorem solution(beta x : ℝ) : 0 < erSeverityTail beta x := by
  unfold erSeverityTail
  exact Real.exp_pos _
