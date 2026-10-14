-- Prove2me | solution 1 for ActuarialValuation.pucProjectedBenefitPV_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:22:41.353012+00:00
-- url     : https://prove2.me/submissions/db0e8a57-6248-4b5e-b6fc-195663f80920

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pucTotalBenefit
import Definitions.Def_actuarial_pucProjectedBenefitPV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (u : ℕ → ℝ) (n m : ℕ) (f : ℝ) (h : 0 ≤ pucTotalBenefit u n m) (hf : 0 ≤ f) : 0 ≤ pucProjectedBenefitPV u n m f := by
  unfold pucProjectedBenefitPV
  exact mul_nonneg h hf
