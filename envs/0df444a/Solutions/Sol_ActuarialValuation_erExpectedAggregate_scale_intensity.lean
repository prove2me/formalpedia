-- Prove2me | solution 1 for ActuarialValuation.erExpectedAggregate_scale_intensity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:06:02.052995+00:00
-- url     : https://prove2.me/submissions/2bdcbe2a-30df-48b4-b9cf-a5b80c1d6350

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erExpectedAggregate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (lambda beta t k : ℝ) :
    erExpectedAggregate (k * lambda) beta t = k * erExpectedAggregate lambda beta t := by
  unfold erExpectedAggregate
  ring
