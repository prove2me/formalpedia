-- Prove2me | solution 1 for ActuarialValuation.cm1SalaryProjection_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T08:21:53.891751+00:00
-- url     : https://prove2.me/submissions/833ad087-25ed-4cd1-ba16-fece4039c519

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1SalaryProjection

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (base growth : ℝ) (t : ℕ) :
    cm1SalaryProjection base growth (t+1) =
      cm1SalaryProjection base growth t * (1+growth) := by
  simp [cm1SalaryProjection, pow_succ, mul_assoc]
