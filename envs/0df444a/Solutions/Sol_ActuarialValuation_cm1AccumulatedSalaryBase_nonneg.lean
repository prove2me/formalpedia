-- Prove2me | solution 1 for ActuarialValuation.cm1AccumulatedSalaryBase_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T08:03:13.941489+00:00
-- url     : https://prove2.me/submissions/2a689453-33c3-4513-9d70-8e934ff1889f

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_actuarial_cm1AccumulatedSalaryBase

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (salary growth : ℕ → ℝ) (n : ℕ)
    (hs : ∀ t ∈ Finset.range n, 0 ≤ salary t)
    (hg : ∀ t ∈ Finset.range n, 0 ≤ growth t) :
    0 ≤ cm1AccumulatedSalaryBase salary growth n := by
  unfold cm1AccumulatedSalaryBase
  exact Finset.sum_nonneg fun t ht => mul_nonneg (hs t ht) (hg t ht)
