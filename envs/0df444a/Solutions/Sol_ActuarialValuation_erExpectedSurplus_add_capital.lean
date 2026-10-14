-- Prove2me | solution 1 for ActuarialValuation.erExpectedSurplus_add_capital
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:53:21.104825+00:00
-- url     : https://prove2.me/submissions/90eadf6c-e1d1-4a18-8a39-3c983867ef05

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erExpectedSurplus

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (u delta c lambda beta t : ℝ) :
    erExpectedSurplus (u + delta) c lambda beta t =
      erExpectedSurplus u c lambda beta t + delta := by
  unfold erExpectedSurplus
  ring
