-- Prove2me | solution 1 for ActuarialValuation.erExpectedAggregate_add_time
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:49:09.34579+00:00
-- url     : https://prove2.me/submissions/c9f73cd4-7389-42dd-b492-7f13115aadea

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erExpectedAggregate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (lambda beta s t : ℝ) :
    erExpectedAggregate lambda beta (s+t) =
      erExpectedAggregate lambda beta s + erExpectedAggregate lambda beta t := by
  unfold erExpectedAggregate
  ring
