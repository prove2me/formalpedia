-- Prove2me | solution 1 for ActuarialValuation.scrPortfolioQuadratic_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:41:13.999135+00:00
-- url     : https://prove2.me/submissions/1c5da7fe-f09e-4c62-add0-809663c40f4c

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_scrPortfolioQuadratic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (c : ℕ → ℝ) (rho : ℕ → ℕ → ℝ) (n : ℕ) (hc : ∀ i ∈ Finset.range n, 0 ≤ c i) (hr : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n, 0 ≤ rho i j) : 0 ≤ scrPortfolioQuadratic c rho n := by
  unfold scrPortfolioQuadratic
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (mul_nonneg (hr i hi j hj) (hc i hi)) (hc j hj)
