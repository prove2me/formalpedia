-- Prove2me | solution 1 for ActuarialValuation.cm1SalaryProjection_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:25:15.054625+00:00
-- url     : https://prove2.me/submissions/63aef104-743c-4059-9bd4-9955aaec2f35

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1SalaryProjection

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (base growth : ℝ) (t : ℕ) (hb : 0 ≤ base)
    (hg : -1 ≤ growth) : 0 ≤ cm1SalaryProjection base growth t := by
  have hfactor : 0 ≤ (1 + growth) := by
    have h := add_le_add_right hg (1 : ℝ)
    simpa [add_comm] using h
  simp only [cm1SalaryProjection]
  exact mul_nonneg hb (pow_nonneg hfactor t)
