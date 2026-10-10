-- Prove2me | solution 1 for ActuarialValuation.cm1DiscountedProfitNPV_add_last
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:20:54.931843+00:00
-- url     : https://prove2.me/submissions/51cf73bc-ee14-4d57-bed6-6a4dad5b713d

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1DiscountedProfitNPV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (profits discount : ℕ → ℝ) (N : ℕ) : cm1DiscountedProfitNPV profits discount (N+1) = cm1DiscountedProfitNPV profits discount N + profits N*discount N := by
  simp only [cm1DiscountedProfitNPV, Finset.sum_range_succ]
