-- Prove2me | solution 1 for ActuarialValuation.compoundPoissonPanjerStep_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:09:18.912714+00:00
-- url     : https://prove2.me/submissions/74324875-134c-4307-a97c-766f2f6d5241

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Cast.Order.Ring
import Definitions.Def_actuarial_compoundPoissonPanjerStep

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (rate : ℝ) (f g : ℕ → ℝ) (s : ℕ)
  (hr : 0 ≤ rate) (hs : 0 < s)
  (hf : ∀ j, 0 ≤ f j) (hg : ∀ j, 0 ≤ g j) :
  0 ≤ compoundPoissonPanjerStep rate f g s := by
  unfold compoundPoissonPanjerStep
  apply mul_nonneg (div_nonneg hr (Nat.cast_nonneg _))
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hf j)) (hg (s - j))
