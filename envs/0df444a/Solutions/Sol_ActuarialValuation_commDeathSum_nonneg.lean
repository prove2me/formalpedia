-- Prove2me | solution 1 for ActuarialValuation.commDeathSum_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:12:38.296559+00:00
-- url     : https://prove2.me/submissions/cdec0f69-7562-4d8f-a020-3d1f8eea1b45

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commDiscountedDeaths
import Definitions.Def_actuarial_commDeathSum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (v : ℝ) (x n : ℕ) (h : ∀ k ∈ Finset.range n, 0 ≤ commDiscountedDeaths l v (x+k)) : 0 ≤ commDeathSum l v x n := by
  unfold commDeathSum
  apply Finset.sum_nonneg
  intro k hk
  exact h k hk
