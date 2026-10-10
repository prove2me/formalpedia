-- Prove2me | solution 1 for ActuarialValuation.aggregatePortfolio_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:40:54.660475+00:00
-- url     : https://prove2.me/submissions/70cba68d-0530-44fc-b0d9-07763bc2b901

import Mathlib
import Definitions.Def_actuarial_aggregatePortfolioPMF
import Definitions.Def_actuarial_aggregateMaximumClaim
import Definitions.Def_actuarial_aggregateFiniteMass
import Definitions.Def_actuarial_aggregateConvolution
import Definitions.Def_actuarial_aggregateBernoulliPMF
import Theorems.Thm_ActuarialValuation_aggregatePortfolioPMF_nonneg
import Theorems.Thm_ActuarialValuation_aggregatePortfolioPMF_support
import Theorems.Thm_ActuarialValuation_aggregateConvolution_mass
import Theorems.Thm_ActuarialValuation_aggregateBernoulliPMF_support
import Theorems.Thm_ActuarialValuation_aggregateBernoulliPMF_mass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : ℕ → ℝ) (b : ℕ → ℕ)
    (n : ℕ) (h : ∀ i, i < n → 0 ≤ p i ∧ p i ≤ 1) :
    (∀ s : ℕ, 0 ≤ aggregatePortfolioPMF p b n s) ∧
    aggregateFiniteMass (aggregatePortfolioPMF p b n)
      (aggregateMaximumClaim b n) = 1 ∧
    (∀ s : ℕ, aggregateMaximumClaim b n < s →
      aggregatePortfolioPMF p b n s = 0) := by
  have hmass : ∀ m : ℕ,
      aggregateFiniteMass (aggregatePortfolioPMF p b m)
        (aggregateMaximumClaim b m) = 1 := by
    intro m
    induction m with
    | zero =>
        simp [aggregateFiniteMass, aggregatePortfolioPMF,
          aggregateMaximumClaim]
    | succ m ih =>
        have hmax : aggregateMaximumClaim b (m + 1) =
            aggregateMaximumClaim b m + b m := by
          simp [aggregateMaximumClaim, Finset.sum_range_succ]
        rw [hmax]
        change aggregateFiniteMass
          (aggregateConvolution (aggregatePortfolioPMF p b m)
            (aggregateBernoulliPMF (p m) (b m)))
          (aggregateMaximumClaim b m + b m) = 1
        rw [aggregateConvolution_mass
          (aggregatePortfolioPMF p b m)
          (aggregateBernoulliPMF (p m) (b m))
          (aggregateMaximumClaim b m) (b m)
          (by
            intro k hk
            exact aggregatePortfolioPMF_support p b m k hk)
          (by
            intro k hk
            exact aggregateBernoulliPMF_support (p m) (b m) k hk)]
        rw [ih, aggregateBernoulliPMF_mass]
        all_goals ring
  refine ⟨?_, hmass n, ?_⟩
  · intro s
    exact aggregatePortfolioPMF_nonneg p b n s h
  · intro s hs
    exact aggregatePortfolioPMF_support p b n s hs
