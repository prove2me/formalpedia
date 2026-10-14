-- Prove2me | solution 1 for ActuarialValuation.erAdjustment_beta_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:18:21.650985+00:00
-- url     : https://prove2.me/submissions/d1242358-9a5d-453e-b962-e196ad32a96f

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erAdjustment

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (lambda c beta : ℝ) (hc : c≠0) : beta-erAdjustment lambda c beta=lambda/c := by
  unfold erAdjustment
  ring
