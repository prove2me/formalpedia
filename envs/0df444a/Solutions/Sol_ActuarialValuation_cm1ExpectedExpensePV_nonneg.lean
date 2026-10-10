-- Prove2me | solution 1 for ActuarialValuation.cm1ExpectedExpensePV_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:33:15.828216+00:00
-- url     : https://prove2.me/submissions/83ae8a49-598b-4661-ba83-df1fb2c62f91

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ExpectedExpensePV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (e d p : ℕ → ℝ) (N : ℕ) (he : ∀ t ∈ Finset.range N, 0 ≤ e t) (hd : ∀ t ∈ Finset.range N, 0 ≤ d t) (hp : ∀ t ∈ Finset.range N, 0 ≤ p t) : 0 ≤ cm1ExpectedExpensePV e d p N := by
  unfold cm1ExpectedExpensePV
  apply Finset.sum_nonneg
  intro t ht
  exact mul_nonneg (mul_nonneg (he t ht) (hd t ht)) (hp t ht)
