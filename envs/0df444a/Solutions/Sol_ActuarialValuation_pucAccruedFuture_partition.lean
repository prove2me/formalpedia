-- Prove2me | solution 1 for ActuarialValuation.pucAccruedFuture_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:28:53.201976+00:00
-- url     : https://prove2.me/submissions/b2108ecc-d57e-4501-b8fa-62c75df83b6a

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pucAccruedBenefit
import Definitions.Def_actuarial_pucTotalBenefit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (u : ℕ → ℝ) (n m : ℕ) : pucTotalBenefit u n m = pucAccruedBenefit u (n+m) := by
  simp only [pucTotalBenefit, pucAccruedBenefit, pucFutureBenefit]
  rw [Finset.sum_range_add]
