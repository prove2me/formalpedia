-- Prove2me | solution 1 for ActuarialValuation.cm1AnnualAccrual_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T08:17:37.303394+00:00
-- url     : https://prove2.me/submissions/82bddc52-2684-41a1-8769-b8c8c1b5a1ce

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1AnnualAccrual

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (salary : ℕ → ℝ) (a : ℝ) (t : ℕ)
    (ha : 0 ≤ a) (hs : 0 ≤ salary t) :
    0 ≤ cm1AnnualAccrual salary a t := by
  simp only [cm1AnnualAccrual]
  exact mul_nonneg ha hs
