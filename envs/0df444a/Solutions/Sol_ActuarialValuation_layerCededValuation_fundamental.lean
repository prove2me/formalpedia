-- Prove2me | solution 1 for ActuarialValuation.layerCededValuation_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:49:33.822163+00:00
-- url     : https://prove2.me/submissions/2bcf7da2-2964-4c82-871f-d9b4a67869ae

import Mathlib
import Definitions.Def_actuarial_layerExcessLoss
import Definitions.Def_actuarial_layerCededPayment
import Definitions.Def_actuarial_layerHigherExcess
import Definitions.Def_actuarial_layerExpectedCeded
import Definitions.Def_actuarial_layerExpectedExcess
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (w : ℕ → ℝ) (B x d L : ℕ)
  (hw : ∀ k, 0 ≤ w k) :
  (layerExcessLoss x d =
    layerCededPayment x d L + layerHigherExcess x d L) ∧
  (layerExpectedCeded w B d L =
    layerExpectedExcess w B d -
      layerExpectedExcess w B (d + L)) ∧
  (0 ≤ layerExpectedCeded w B d L ∧
    layerExpectedCeded w B d L ≤ layerExpectedExcess w B d) := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [layerExcessLoss, layerCededPayment, layerHigherExcess]
    omega
  · unfold layerExpectedCeded layerExpectedExcess
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
  · constructor
    · unfold layerExpectedCeded
      apply Finset.sum_nonneg
      intro x hx
      exact mul_nonneg (by positivity) (hw x)
    · unfold layerExpectedCeded layerExpectedExcess
      apply Finset.sum_le_sum
      intro x hx
      have hp : layerCededPayment x d L ≤ layerExcessLoss x d := by
        dsimp [layerCededPayment]
        exact min_le_left _ _
      have hr : (layerCededPayment x d L : ℝ) ≤ (layerExcessLoss x d : ℝ) := by
        exact_mod_cast hp
      exact mul_le_mul_of_nonneg_right hr (hw x)
