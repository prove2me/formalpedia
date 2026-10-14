-- Prove2me | solution 1 for ActuarialValuation.clLinkNumerator_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:07:26.803993+00:00
-- url     : https://prove2.me/submissions/10159c39-8d55-4cbc-8e73-790bba21cfa9

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_actuarial_clLinkNumerator

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : ℕ → ℕ → ℝ) (m j : ℕ) (h : ∀ i ∈ Finset.range m, 0 ≤ p i (j+1)) : 0 ≤ clLinkNumerator p m j := by
  change 0 ≤ ∑ i ∈ Finset.range m, p i (j + 1)
  exact Finset.sum_nonneg (by intro i hi; exact h i hi)
