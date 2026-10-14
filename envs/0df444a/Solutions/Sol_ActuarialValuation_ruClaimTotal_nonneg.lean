-- Prove2me | solution 1 for ActuarialValuation.ruClaimTotal_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T15:40:56.766683+00:00
-- url     : https://prove2.me/submissions/22392335-db57-4e1b-8e26-3ce7ccd89ba4

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruClaimTotal
open ActuarialValuation

theorem solution(x : ℕ → ℝ) (n : ℕ) (hx : ∀ k ∈ Finset.range n, 0 ≤ x k) : 0 ≤ ruClaimTotal x n := by
  unfold ruClaimTotal
  exact Finset.sum_nonneg hx
