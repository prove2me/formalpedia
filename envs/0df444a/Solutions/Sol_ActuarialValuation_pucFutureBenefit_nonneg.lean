-- Prove2me | solution 1 for ActuarialValuation.pucFutureBenefit_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:08:09.964928+00:00
-- url     : https://prove2.me/submissions/6b3379fb-5837-4b27-8382-7e5707ee0bdc

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_actuarial_pucFutureBenefit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (u : ℕ → ℝ) (n m : ℕ) (hu : ∀ t ∈ Finset.range m, 0 ≤ u (n+t)) : 0 ≤ pucFutureBenefit u n m := by
  unfold pucFutureBenefit
  exact Finset.sum_nonneg (fun t ht => hu t ht)
