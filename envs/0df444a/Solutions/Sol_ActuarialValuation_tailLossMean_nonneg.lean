-- Prove2me | solution 1 for ActuarialValuation.tailLossMean_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:18:11.11112+00:00
-- url     : https://prove2.me/submissions/e36c517e-9d4f-4d49-b122-9140eb7d45a6

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_actuarial_tailLossMean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : ℕ → ℝ) (n : ℕ)
    (h : ∀ k ∈ Finset.range (n+1), 0 ≤ p k) :
    0 ≤ tailLossMean p n := by
  unfold tailLossMean
  apply Finset.sum_nonneg
  intro k hk
  apply mul_nonneg
  · first
    | exact Nat.cast_nonneg _
    | positivity
  · exact h k hk
