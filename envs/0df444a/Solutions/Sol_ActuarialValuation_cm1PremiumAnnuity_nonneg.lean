-- Prove2me | solution 1 for ActuarialValuation.cm1PremiumAnnuity_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:33:25.738002+00:00
-- url     : https://prove2.me/submissions/34242c26-68b5-47ab-abe4-7a5c40d23e8a

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1PremiumAnnuity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (d p : ℕ → ℝ) (N : ℕ) (hd : ∀ t ∈ Finset.range N, 0 ≤ d t) (hp : ∀ t ∈ Finset.range N, 0 ≤ p t) : 0 ≤ cm1PremiumAnnuity d p N := by
  unfold cm1PremiumAnnuity
  apply Finset.sum_nonneg
  intro t ht
  exact mul_nonneg (hd t ht) (hp t ht)
