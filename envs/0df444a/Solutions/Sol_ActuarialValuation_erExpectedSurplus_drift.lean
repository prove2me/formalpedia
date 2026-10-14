-- Prove2me | solution 1 for ActuarialValuation.erExpectedSurplus_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:00:28.229999+00:00
-- url     : https://prove2.me/submissions/f9ee4885-aa65-4be8-9a4a-e7e7ad7a4f5c

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erExpectedSurplus

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (u c lambda beta s t : ℝ) :
    erExpectedSurplus u c lambda beta (s + t) -
      erExpectedSurplus u c lambda beta s = t * (c - lambda / beta) := by
  unfold erExpectedSurplus erExpectedPremium erExpectedAggregate
  ring
