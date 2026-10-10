-- Prove2me | solution 1 for ActuarialValuation.aggregatePortfolioPMF_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:32:11.111049+00:00
-- url     : https://prove2.me/submissions/a3f2daac-4782-4e0c-8e01-23d705daecb3

import Mathlib
import Definitions.Def_actuarial_aggregatePortfolioPMF
import Definitions.Def_actuarial_aggregateMaximumClaim
import Definitions.Def_actuarial_aggregateFiniteMass
import Definitions.Def_actuarial_aggregateConvolution
import Definitions.Def_actuarial_aggregateBernoulliPMF
import Theorems.Thm_ActuarialValuation_aggregateConvolution_mass
import Theorems.Thm_ActuarialValuation_aggregatePortfolioPMF_support
import Theorems.Thm_ActuarialValuation_aggregateBernoulliPMF_support
import Theorems.Thm_ActuarialValuation_aggregateBernoulliPMF_mass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : ℕ → ℝ) (b : ℕ → ℕ) (n : ℕ) :
    aggregateFiniteMass (aggregatePortfolioPMF p b n)
      (aggregateMaximumClaim b n) = 1 := by
  induction n with
  | zero =>
      simp [aggregateFiniteMass, aggregatePortfolioPMF, aggregateMaximumClaim]
  | succ n ih =>
      have hmax : aggregateMaximumClaim b (n + 1) =
          aggregateMaximumClaim b n + b n := by
        simp [aggregateMaximumClaim, Finset.sum_range_succ]
      rw [hmax]
      change aggregateFiniteMass
        (aggregateConvolution (aggregatePortfolioPMF p b n)
          (aggregateBernoulliPMF (p n) (b n)))
        (aggregateMaximumClaim b n + b n) = 1
      rw [aggregateConvolution_mass
        (aggregatePortfolioPMF p b n)
        (aggregateBernoulliPMF (p n) (b n))
        (aggregateMaximumClaim b n) (b n)
        (by
          intro k hk
          exact aggregatePortfolioPMF_support p b n k hk)
        (by
          intro k hk
          exact aggregateBernoulliPMF_support (p n) (b n) k hk)]
      rw [ih, aggregateBernoulliPMF_mass]
      all_goals ring
