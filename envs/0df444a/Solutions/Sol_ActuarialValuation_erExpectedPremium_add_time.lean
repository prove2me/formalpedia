-- Prove2me | solution 1 for ActuarialValuation.erExpectedPremium_add_time
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:45:09.173221+00:00
-- url     : https://prove2.me/submissions/efd020f7-7ad9-4138-ae8f-08ca4015c53a

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erExpectedPremium

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (premium s t : ℝ) : erExpectedPremium premium (s+t)=erExpectedPremium premium s+erExpectedPremium premium t := by
  unfold erExpectedPremium
  ring
