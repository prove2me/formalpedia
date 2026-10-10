-- Prove2me | solution 1 for ActuarialValuation.discreteStopLossPremium_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:21:06.56675+00:00
-- url     : https://prove2.me/submissions/3543a63e-3968-46a7-9f5e-f2ca84b564b1

import Mathlib
import Definitions.Def_actuarial_discreteStopLossPremium
import Definitions.Def_actuarial_discreteStopLossAggregateMean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (w : ℕ → ℝ) (bound : ℕ) :
  discreteStopLossPremium w bound 0 =
    discreteStopLossAggregateMean w bound := by
  simp [discreteStopLossPremium, discreteStopLossAggregateMean, discreteStopLossPayment]
