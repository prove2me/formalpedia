-- Prove2me | solution 1 for ActuarialValuation.erExpectedSurplus_issue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:09:30.029981+00:00
-- url     : https://prove2.me/submissions/4246f9c6-0b33-457e-bac6-f335067c2a92

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erExpectedSurplus

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (initial premium lambda beta : ℝ) :
    erExpectedSurplus initial premium lambda beta 0 = initial := by
  unfold erExpectedSurplus erExpectedPremium erExpectedAggregate
  ring
