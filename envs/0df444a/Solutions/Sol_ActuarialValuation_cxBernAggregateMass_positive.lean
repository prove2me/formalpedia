-- Prove2me | solution 1 for ActuarialValuation.cxBernAggregateMass_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:39:11.114984+00:00
-- url     : https://prove2.me/submissions/11169df2-e5b6-4ac0-99f7-807b8cf1f18f

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxBernAggregateMass

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p0 p1 : ℝ) (f : ℕ → ℝ) (k : ℕ) (hk : k ≠ 0) : cxBernAggregateMass p0 p1 f k = p1*f k := by
  simp [cxBernAggregateMass, hk]
