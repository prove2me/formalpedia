-- Prove2me | solution 1 for ActuarialValuation.pucProjectedBenefitPV_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:29:10.805507+00:00
-- url     : https://prove2.me/submissions/2686240f-e910-464b-8138-e53e757e5cba

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pucActuarialLiability
import Definitions.Def_actuarial_pucFutureNormalCost
import Definitions.Def_actuarial_pucProjectedBenefitPV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (u : ℕ → ℝ) (n m : ℕ) (f : ℝ) : pucProjectedBenefitPV u n m f = pucActuarialLiability u n f + pucFutureNormalCost u n m f := by
  simp only [pucProjectedBenefitPV, pucTotalBenefit,
    pucActuarialLiability, pucFutureNormalCost, add_mul]
