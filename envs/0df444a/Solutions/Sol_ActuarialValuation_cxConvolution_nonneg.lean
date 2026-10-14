-- Prove2me | solution 1 for ActuarialValuation.cxConvolution_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:43:07.319558+00:00
-- url     : https://prove2.me/submissions/395fdf14-80e5-431d-a51a-b12a776b150e

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_actuarial_cxConvolution

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (f g : ℕ → ℝ) (k : ℕ) (hf : ∀ j ≤ k, 0 ≤ f j) (hg : ∀ j ≤ k, 0 ≤ g j) : 0 ≤ cxConvolution f g k := by
  unfold cxConvolution
  refine Finset.sum_nonneg ?_
  intro j hj
  have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  exact mul_nonneg (hf j hjk) (hg (k - j) (Nat.sub_le k j))
