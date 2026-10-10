-- Prove2me | solution 1 for ActuarialValuation.cm1DiscountedProfitNPV_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:33:33.983008+00:00
-- url     : https://prove2.me/submissions/39871170-a40a-4afd-9e5c-a495eb9c36ea

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1DiscountedProfitNPV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (profits discount : ℕ → ℝ) (N : ℕ) (hp : ∀ t ∈ Finset.range N, 0 ≤ profits t) (hd : ∀ t ∈ Finset.range N, 0 ≤ discount t) : 0 ≤ cm1DiscountedProfitNPV profits discount N := by
  unfold cm1DiscountedProfitNPV
  apply Finset.sum_nonneg
  intro t ht
  exact mul_nonneg (hp t ht) (hd t ht)
