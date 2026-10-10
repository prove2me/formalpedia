-- Prove2me | solution 2 for ActuarialValuation.aggregatePortfolio_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:41:14.510173+00:00
-- url     : https://prove2.me/submissions/9f5bed47-54fd-44af-bc3e-03eea3874592

import Mathlib
import Definitions.Def_actuarial_aggregatePortfolioPMF
import Definitions.Def_actuarial_aggregateMaximumClaim
import Definitions.Def_actuarial_aggregateFiniteMass
import Theorems.Thm_ActuarialValuation_aggregatePortfolioPMF_nonneg
import Theorems.Thm_ActuarialValuation_aggregatePortfolioPMF_mass
import Theorems.Thm_ActuarialValuation_aggregatePortfolioPMF_support
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
  constructor
  · intro s
    exact aggregatePortfolioPMF_nonneg p b n s h
  constructor
  · exact aggregatePortfolioPMF_mass p b n
  · intro s hs
    exact aggregatePortfolioPMF_support p b n s hs
