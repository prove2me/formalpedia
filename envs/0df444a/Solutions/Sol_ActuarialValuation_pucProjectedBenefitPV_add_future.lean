-- Prove2me | solution 1 for ActuarialValuation.pucProjectedBenefitPV_add_future
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:59:08.794064+00:00
-- url     : https://prove2.me/submissions/365e22f1-c65d-4ac5-bc31-04a7c6e6e920

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_pucNormalCost
import Definitions.Def_actuarial_pucProjectedBenefitPV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (u : ℕ → ℝ) (n m : ℕ) (f : ℝ) : pucProjectedBenefitPV u n (m+1) f = pucProjectedBenefitPV u n m f + pucNormalCost u (n+m) f := by
  simp only [pucProjectedBenefitPV, pucTotalBenefit, pucFutureBenefit,
    pucNormalCost, Finset.sum_range_succ]
  ring
