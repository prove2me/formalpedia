-- Prove2me | solution 1 for ActuarialValuation.quotaShareQuadratic_square_completion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:06:18.881346+00:00
-- url     : https://prove2.me/submissions/35069867-aeb1-4e7c-87c3-e45fe1e7be67

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_quotaShareContinuousOptimum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (loading capital retention : ℝ)
    (hpos : loading + capital ≠ 0) :
    loading * (1 - retention) ^ 2 + capital * retention ^ 2 =
      (loading * capital / (loading + capital)) +
      (loading + capital) *
        (retention - quotaShareContinuousOptimum loading capital) ^ 2 := by
  dsimp [quotaShareContinuousOptimum]
  field_simp
  ring
