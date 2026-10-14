-- Prove2me | solution 1 for ActuarialValuation.erExpectedAggregate_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:40:35.971155+00:00
-- url     : https://prove2.me/submissions/0f67464f-ada7-433a-b088-adf7ff9f5ffe

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erExpectedAggregate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (lambda beta t : ℝ) (hl : 0≤lambda) (hb : 0<beta) (ht : 0≤t) : 0≤erExpectedAggregate lambda beta t := by
  unfold erExpectedAggregate
  positivity
