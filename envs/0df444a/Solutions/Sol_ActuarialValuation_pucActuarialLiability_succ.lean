-- Prove2me | solution 1 for ActuarialValuation.pucActuarialLiability_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:30:10.662971+00:00
-- url     : https://prove2.me/submissions/acb9a3df-38cc-4103-a98b-8e97145ce243

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pucActuarialLiability
import Definitions.Def_actuarial_pucNormalCost

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (u : ℕ → ℝ) (n : ℕ) (f : ℝ) : pucActuarialLiability u (n+1) f = pucActuarialLiability u n f + pucNormalCost u n f := by
  simp only [pucActuarialLiability, pucAccruedBenefit,
    pucNormalCost, Finset.sum_range_succ, add_mul]
