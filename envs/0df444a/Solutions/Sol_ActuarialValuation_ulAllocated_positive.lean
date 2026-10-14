-- Prove2me | solution 1 for ActuarialValuation.ulAllocated_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:13:45.610026+00:00
-- url     : https://prove2.me/submissions/d6a0e7b0-e49c-4603-a500-5053f1eb60d1

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulAllocatedPremium

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (prem expense : ℝ) (hp : 0≤prem) (he0 : 0≤expense) (he1 : expense≤1) : 0≤ulAllocatedPremium prem expense := by
  change 0 ≤ prem * (1 - expense)
  exact mul_nonneg hp (sub_nonneg.mpr he1)
