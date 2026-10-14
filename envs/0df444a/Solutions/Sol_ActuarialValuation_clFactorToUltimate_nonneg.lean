-- Prove2me | solution 1 for ActuarialValuation.clFactorToUltimate_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:09:58.153661+00:00
-- url     : https://prove2.me/submissions/a679d9bd-097f-4963-b9d7-155b64abc470

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clFactorToUltimate
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (f : ℕ → ℝ) (j n : ℕ) (h : ∀ t ∈ Finset.range n, 0 ≤ f (j+t)) : 0 ≤ clFactorToUltimate f j n := by
  change 0 ≤ ∏ t ∈ Finset.range n, f (j + t)
  exact Finset.prod_nonneg (by intro t ht; exact h t ht)
