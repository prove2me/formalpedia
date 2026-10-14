-- Prove2me | solution 1 for ActuarialValuation.pen9AverageSalary_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:03:13.145206+00:00
-- url     : https://prove2.me/submissions/bd245138-ad9b-4b84-bf59-c9ff28626d91

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9AverageSalary

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (salary : ℕ → ℝ) (first : ℕ) : pen9AverageSalary salary first 1 = salary first := by
  simp [pen9AverageSalary]
