-- Prove2me | solution 1 for ActuarialValuation.layerExpectedCeded_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:46:05.939207+00:00
-- url     : https://prove2.me/submissions/edcc24c9-0a94-4c45-8e31-989431189f7c

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_layerExpectedCeded
import Definitions.Def_actuarial_layerCededPayment
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (w : ℕ → ℝ) (B d L : ℕ) (hw : ∀ x, 0 ≤ w x) :
  0 ≤ layerExpectedCeded w B d L := by
  unfold layerExpectedCeded
  apply Finset.sum_nonneg
  intro x hx
  exact mul_nonneg (by positivity) (hw x)
