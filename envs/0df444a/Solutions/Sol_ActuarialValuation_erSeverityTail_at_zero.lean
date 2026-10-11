-- Prove2me | solution 1 for ActuarialValuation.erSeverityTail_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T06:44:35.991029+00:00
-- url     : https://prove2.me/submissions/5adf6531-8211-4aa8-a78e-54c0275ef147

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erSeverityTail
open ActuarialValuation

theorem solution(beta : ℝ) : erSeverityTail beta 0=1 := by
  simp [erSeverityTail]
