-- Prove2me | solution 1 for ActuarialValuation.aggregatePortfolioPMF_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T15:18:47.033788+00:00
-- url     : https://prove2.me/submissions/26534c05-bb46-4a8c-9b78-23a0f32e4c38

import Mathlib
import Definitions.Def_actuarial_aggregatePortfolioPMF
open ActuarialValuation

theorem solution (p : ℕ → ℝ) (b : ℕ → ℕ)
  (n s : ℕ) (h : ∀ i, i < n → 0 ≤ p i ∧ p i ≤ 1) :
  0 ≤ aggregatePortfolioPMF p b n s := by
  induction n generalizing s with
  | zero =>
    simp only [aggregatePortfolioPMF]
    split_ifs <;> norm_num
  | succ n ih =>
    simp only [aggregatePortfolioPMF, aggregateConvolution]
    refine Finset.sum_nonneg fun k _ => mul_nonneg
      (ih k (fun i hi => h i (Nat.lt_succ_of_lt hi))) ?_
    obtain ⟨h0, h1⟩ := h n (Nat.lt_succ_self n)
    simp only [aggregateBernoulliPMF]
    split_ifs <;> linarith
