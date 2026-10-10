-- Prove2me | solution 1 for ActuarialValuation.layerExpectedCeded_le_full_stoploss
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:46:15.715893+00:00
-- url     : https://prove2.me/submissions/b3882281-9c81-4e6f-90f0-9857a681fb6c

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_layerExpectedCeded
import Definitions.Def_actuarial_layerExpectedExcess
import Definitions.Def_actuarial_layerCededPayment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (w : ℕ → ℝ) (B d L : ℕ) (hw : ∀ x, 0 ≤ w x) :
  layerExpectedCeded w B d L ≤ layerExpectedExcess w B d := by
  unfold layerExpectedCeded layerExpectedExcess
  apply Finset.sum_le_sum
  intro x hx
  have hp : layerCededPayment x d L ≤ layerExcessLoss x d := by
    dsimp [layerCededPayment]
    exact min_le_left _ _
  have hr : (layerCededPayment x d L : ℝ) ≤ (layerExcessLoss x d : ℝ) := by
    exact_mod_cast hp
  exact mul_le_mul_of_nonneg_right hr (hw x)
