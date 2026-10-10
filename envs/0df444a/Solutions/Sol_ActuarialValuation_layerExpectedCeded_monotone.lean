-- Prove2me | solution 1 for ActuarialValuation.layerExpectedCeded_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:49:20.234498+00:00
-- url     : https://prove2.me/submissions/57f563de-a810-4f3d-a5a3-1cf7ce00663b

import Mathlib
import Definitions.Def_actuarial_layerExpectedCeded
import Definitions.Def_actuarial_layerCededPayment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (w : ℕ → ℝ) (B d L1 L2 : ℕ)
  (hw : ∀ x, 0 ≤ w x) (h : L1 ≤ L2) :
  layerExpectedCeded w B d L1 ≤ layerExpectedCeded w B d L2 := by
  unfold layerExpectedCeded
  apply Finset.sum_le_sum
  intro x hx
  have hp : layerCededPayment x d L1 ≤ layerCededPayment x d L2 := by
    dsimp [layerCededPayment]
    omega
  have hr : (layerCededPayment x d L1 : ℝ) ≤ (layerCededPayment x d L2 : ℝ) := by
    exact_mod_cast hp
  exact mul_le_mul_of_nonneg_right hr (hw x)
