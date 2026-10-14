-- Prove2me | solution 1 for ActuarialValuation.pucProjectedBenefitPV_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:21:38.350462+00:00
-- url     : https://prove2.me/submissions/75b7bfd5-6a7b-470f-95b0-c937a2e9e209

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pucProjectedBenefitPV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (u : ℕ → ℝ) (f : ℝ) : pucProjectedBenefitPV u 0 0 f = 0 := by
  simp [pucProjectedBenefitPV, pucTotalBenefit, pucAccruedBenefit, pucFutureBenefit]
