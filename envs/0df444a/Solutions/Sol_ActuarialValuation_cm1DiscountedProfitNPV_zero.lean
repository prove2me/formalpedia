-- Prove2me | solution 1 for ActuarialValuation.cm1DiscountedProfitNPV_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:20:47.372286+00:00
-- url     : https://prove2.me/submissions/c0f20bff-c9e9-4d1a-a1e0-dfaa6ce21964

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1DiscountedProfitNPV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (profits discount : ℕ → ℝ) : cm1DiscountedProfitNPV profits discount 0 = 0 := by
  simp [cm1DiscountedProfitNPV]
