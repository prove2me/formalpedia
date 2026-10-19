-- Prove2me | solution 1 for AggGameNet.Sync.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T07:23:55.333952+00:00
-- url     : https://prove2.me/submissions/42033081-1183-4202-aaf9-38cb923f7b86

import Mathlib
set_option autoImplicit false

theorem solution (ζ : ℕ → ℝ) (hζ : ∀ k, 0 ≤ ζ k)
    (hsum : Summable ζ) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    Summable (fun k => ∑ s ∈ Finset.range (k + 1), β ^ (k - s) * ζ s) := by
  have hg : Summable (fun n : ℕ => β ^ n) := summable_geometric_of_lt_one hβ0.le hβ1
  have h1 : Summable (fun n => ‖ζ n‖) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (hζ _)] using hsum
  have h2 : Summable (fun n : ℕ => ‖β ^ n‖) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hβ0.le _)] using hg
  have h := (summable_norm_sum_mul_antidiagonal_of_summable_norm h1 h2).of_norm
  refine (h.congr ?_)
  intro n
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => ζ i * β ^ j) n]
  refine Finset.sum_congr rfl ?_
  intro s _
  ring
