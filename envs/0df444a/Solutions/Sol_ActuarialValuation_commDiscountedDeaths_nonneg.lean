-- Prove2me | solution 1 for ActuarialValuation.commDiscountedDeaths_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:11:01.668611+00:00
-- url     : https://prove2.me/submissions/245f2f67-b1b4-426c-b7ee-7fa5b00fad37

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commDiscountedDeaths

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (v : ℝ) (x : ℕ) (hv : 0 ≤ v) (hd : l (x+1) ≤ l x) : 0 ≤ commDiscountedDeaths l v x := by
  unfold commDiscountedDeaths commAnnualDeaths
  exact mul_nonneg (pow_nonneg hv _) (sub_nonneg.mpr hd)
