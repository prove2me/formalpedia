-- Prove2me | solution 1 for ActuarialValuation.pucFutureNormalCost_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:55:33.620157+00:00
-- url     : https://prove2.me/submissions/70d398f3-a7b7-4034-8a66-b8f63338e9a4

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pucNormalCost
import Definitions.Def_actuarial_pucFutureNormalCost

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (u : ℕ → ℝ) (n m : ℕ) (f : ℝ) : pucFutureNormalCost u n (m+1) f = pucFutureNormalCost u n m f + pucNormalCost u (n+m) f := by
  simp only [pucFutureNormalCost, pucFutureBenefit,
    pucNormalCost, Finset.sum_range_succ, add_mul]
