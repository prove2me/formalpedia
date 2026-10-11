-- Prove2me | solution 1 for ActuarialValuation.erExpectedAggregate_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T11:36:12.539831+00:00
-- url     : https://prove2.me/submissions/cab0d9be-e5b3-4889-a314-d2c32ef83e59

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erExpectedAggregate
open ActuarialValuation

theorem solution(lambda beta : ℝ) : erExpectedAggregate lambda beta 0=0 := by
  simp [erExpectedAggregate]
