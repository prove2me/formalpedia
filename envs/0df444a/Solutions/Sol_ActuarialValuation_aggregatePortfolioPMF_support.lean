-- Prove2me | solution 1 for ActuarialValuation.aggregatePortfolioPMF_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:13:47.759138+00:00
-- url     : https://prove2.me/submissions/2be6ae08-9e71-43e5-87ca-d159881929c5

import Mathlib
import Definitions.Def_actuarial_aggregatePortfolioPMF
import Definitions.Def_actuarial_aggregateMaximumClaim
import Definitions.Def_actuarial_aggregateConvolution
import Definitions.Def_actuarial_aggregateBernoulliPMF
import Theorems.Thm_ActuarialValuation_aggregateBernoulliPMF_support
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : ℕ → ℝ) (b : ℕ → ℕ)
    (n s : ℕ) (h : aggregateMaximumClaim b n < s) :
    aggregatePortfolioPMF p b n s = 0 := by
  induction n generalizing s with
  | zero =>
      have hs : s ≠ 0 := by
        have hmax : aggregateMaximumClaim b 0 = 0 := by
          simp [aggregateMaximumClaim]
        rw [hmax] at h
        omega
      simp [aggregatePortfolioPMF, hs]
  | succ n ih =>
      have hmax : aggregateMaximumClaim b (n + 1) =
          aggregateMaximumClaim b n + b n := by
        simp [aggregateMaximumClaim, Finset.sum_range_succ]
      rw [hmax] at h
      change aggregateConvolution (aggregatePortfolioPMF p b n)
        (aggregateBernoulliPMF (p n) (b n)) s = 0
      unfold aggregateConvolution
      apply Finset.sum_eq_zero
      intro k hk
      have hks : k ≤ s := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      by_cases hkbig : aggregateMaximumClaim b n < k
      · rw [ih k hkbig, zero_mul]
      · have hkle : k ≤ aggregateMaximumClaim b n := Nat.le_of_not_gt hkbig
        have hbs : b n < s - k := by omega
        rw [aggregateBernoulliPMF_support (p n) (b n) (s - k) hbs, mul_zero]
