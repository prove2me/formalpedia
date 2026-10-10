-- Prove2me | solution 1 for ActuarialValuation.aggregatePortfolioPMF_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:07:47.532824+00:00
-- url     : https://prove2.me/submissions/8b40941d-dd87-441e-a1cc-5a9eaf2a513f

import Mathlib
import Definitions.Def_actuarial_aggregatePortfolioPMF
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : ℕ → ℝ) (b : ℕ → ℕ) (n s : ℕ) :
    aggregatePortfolioPMF p b (n + 1) s =
      aggregateConvolution (aggregatePortfolioPMF p b n)
        (aggregateBernoulliPMF (p n) (b n)) s := by
  rfl
