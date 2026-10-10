-- Prove2me | solution 1 for ActuarialValuation.layerExpectedCeded_stoploss_difference
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:49:27.257986+00:00
-- url     : https://prove2.me/submissions/0241ed73-c149-47f8-8abe-e1c65c783135

import Mathlib
import Definitions.Def_actuarial_layerExpectedCeded
import Definitions.Def_actuarial_layerExpectedExcess
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (w : ℕ → ℝ) (B d L : ℕ) :
  layerExpectedCeded w B d L =
    layerExpectedExcess w B d -
      layerExpectedExcess w B (d + L) := by
  unfold layerExpectedCeded layerExpectedExcess
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  have hp : layerExcessLoss x d =
      layerCededPayment x d L + layerExcessLoss x (d + L) := by
    dsimp [layerExcessLoss, layerCededPayment]
    omega
  have hpr : (layerExcessLoss x d : ℝ) =
      (layerCededPayment x d L : ℝ) + (layerExcessLoss x (d + L) : ℝ) := by
    exact_mod_cast hp
  rw [hpr]
  ring
