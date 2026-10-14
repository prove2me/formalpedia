-- Prove2me | solution 1 for ActuarialValuation.erExpectedPremium_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:47:00.452675+00:00
-- url     : https://prove2.me/submissions/1daaced7-d53b-4366-afbc-3acfeb5f22f1

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erExpectedPremium

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (premium : ℝ) : erExpectedPremium premium 0=0 := by
  unfold erExpectedPremium
  ring
