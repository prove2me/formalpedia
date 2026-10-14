-- Prove2me | solution 1 for ActuarialValuation.mackNumerator_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:33:45.820268+00:00
-- url     : https://prove2.me/submissions/441f6421-f80f-40ae-9365-c305b4448b68

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackNumerator

import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (c : ℕ → ℕ → ℝ) (m j : ℕ) (h : ∀ i ∈ Finset.range m, 0 ≤ c i (j+1)) : 0 ≤ mackNumerator c m j := by
  unfold mackNumerator
  exact Finset.sum_nonneg (fun i hi => h i hi)
