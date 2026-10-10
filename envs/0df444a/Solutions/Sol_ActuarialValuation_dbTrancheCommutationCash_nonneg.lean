-- Prove2me | solution 1 for ActuarialValuation.dbTrancheCommutationCash_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:18:43.440143+00:00
-- url     : https://prove2.me/submissions/570d3ab1-9f33-4a27-b51e-dde2afbf56e7

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_dbTrancheCommutationCash

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (factor reduction : ℕ → ℝ) (n : ℕ)
  (hf : ∀ i ∈ Finset.range n, 0 ≤ factor i)
  (hx : ∀ i ∈ Finset.range n, 0 ≤ reduction i) :
  0 ≤ dbTrancheCommutationCash factor reduction n := by
  unfold dbTrancheCommutationCash
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (hf i hi) (hx i hi)
