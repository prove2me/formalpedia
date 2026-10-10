-- Prove2me | solution 1 for ActuarialValuation.discreteStopLossLimitedMean_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:22:41.708739+00:00
-- url     : https://prove2.me/submissions/42205667-8be9-4653-a433-6245e9d95285

import Mathlib
import Definitions.Def_actuarial_discreteStopLossLimitedMean
import Definitions.Def_actuarial_discreteStopLossPremium
import Definitions.Def_actuarial_discreteStopLossAggregateMean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (w : ℕ → ℝ) (bound deductible : ℕ) :
  discreteStopLossLimitedMean w bound deductible +
    discreteStopLossPremium w bound deductible =
      discreteStopLossAggregateMean w bound := by
  unfold discreteStopLossLimitedMean discreteStopLossPremium
    discreteStopLossAggregateMean
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  have hp : min s deductible + discreteStopLossPayment s deductible = s := by
    simp only [discreteStopLossPayment]
    omega
  calc
    (min s deductible : ℝ) * w s +
        (discreteStopLossPayment s deductible : ℝ) * w s =
      ((min s deductible + discreteStopLossPayment s deductible : ℕ) : ℝ) * w s := by
        push_cast
        ring
    _ = (s : ℝ) * w s := by rw [hp]
