-- Prove2me | solution 1 for ActuarialValuation.cm1CARELiability_add_last
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T08:16:57.317021+00:00
-- url     : https://prove2.me/submissions/857aa450-fb6b-481d-a0ae-0010c1270fb9

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1CARELiability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (salary revalue : ℕ → ℝ) (n : ℕ) (a annuity : ℝ) :
    cm1CARELiability salary revalue (n + 1) a annuity =
      cm1CARELiability salary revalue n a annuity +
        a * salary n * revalue n * annuity := by
  simp only [cm1CARELiability, cm1PensionCapitalValue, cm1AccruedCARE,
    Finset.sum_range_succ, mul_add, add_mul, mul_assoc]
