-- Prove2me | solution 1 for ActuarialValuation.aggregateDeductiblePremium_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:06:47.169109+00:00
-- url     : https://prove2.me/submissions/f0adf271-778a-4311-8dbc-29adf7fc6d4a

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_actuarial_aggregateDeductiblePremium

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (w : ℕ → ℝ) (x : ℕ → ℕ → ℕ) (B n d : ℕ)
  (hw : ∀ s, 0 ≤ w s) :
  0 ≤ aggregateDeductiblePremium w x B n d := by
  unfold aggregateDeductiblePremium
  apply Finset.sum_nonneg
  intro s hs
  exact mul_nonneg (Nat.cast_nonneg _) (hw s)
