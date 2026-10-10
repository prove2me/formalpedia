-- Prove2me | solution 1 for ActuarialValuation.cm1SalaryProjection_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:28:03.126683+00:00
-- url     : https://prove2.me/submissions/52775bed-e5d2-4337-99ff-7b3fe51e55e7

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1SalaryProjection

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (base growth : ℝ) (t : ℕ) (hb : 0 ≤ base)
    (hg : 0 ≤ growth) :
    cm1SalaryProjection base growth t ≤ cm1SalaryProjection base growth (t+1) := by
  have hfactor : 1 ≤ 1 + growth := by
    have h := add_le_add_left hg (1 : ℝ)
    simpa using h
  have hprojected : 0 ≤ base * (1 + growth) ^ t :=
    mul_nonneg hb (pow_nonneg (le_trans zero_le_one hfactor) t)
  simp only [cm1SalaryProjection, pow_succ]
  calc
    base * (1 + growth) ^ t = (base * (1 + growth) ^ t) * 1 := by simp
    _ ≤ (base * (1 + growth) ^ t) * (1 + growth) :=
      mul_le_mul_of_nonneg_left hfactor hprojected
    _ = base * ((1 + growth) ^ t * (1 + growth)) := mul_assoc _ _ _
