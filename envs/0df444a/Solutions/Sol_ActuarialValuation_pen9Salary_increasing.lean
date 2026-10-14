-- Prove2me | solution 1 for ActuarialValuation.pen9Salary_increasing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:01:22.086557+00:00
-- url     : https://prove2.me/submissions/c68a3f98-460c-4d00-ac3e-f28106a615c1

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9Salary

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (s growth : ℝ) (n : ℕ) (hs : 0 ≤ s) (hg : 0 ≤ growth) : pen9Salary s growth n ≤ pen9Salary s growth (n+1) := by
  simp only [pen9Salary, pow_succ]
  have hg1 : 0 ≤ 1 + growth := by linarith
  have hval : 0 ≤ s * (1 + growth) ^ n :=
    mul_nonneg hs (pow_nonneg hg1 n)
  have hdelta : 0 ≤ (s * (1 + growth) ^ n) * growth :=
    mul_nonneg hval hg
  nlinarith
