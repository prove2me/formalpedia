-- Prove2me | solution 1 for ActuarialValuation.pgConvolve_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:40:11.851988+00:00
-- url     : https://prove2.me/submissions/d2467f15-d8ae-450c-877a-efdbcec7cf02

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_actuarial_pgConvolve

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (f g : ℕ → ℝ) (k : ℕ) (hf : ∀ i, 0 ≤ f i) (hg : ∀ j, 0 ≤ g j) : 0 ≤ pgConvolve f g k := by
  unfold pgConvolve
  refine Finset.sum_nonneg ?_
  intro j hj
  exact mul_nonneg (hf j) (hg (k - j))
