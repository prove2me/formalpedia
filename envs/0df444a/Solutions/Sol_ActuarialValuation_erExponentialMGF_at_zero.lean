-- Prove2me | solution 1 for ActuarialValuation.erExponentialMGF_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T11:09:42.245055+00:00
-- url     : https://prove2.me/submissions/eacd1509-1fb0-42bb-a98f-cd19a9be17b2

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erExponentialMGF
open ActuarialValuation

theorem solution(beta : ℝ) (hb : beta≠0) : erExponentialMGF beta 0=1 := by
  simp [erExponentialMGF, hb]
