-- Prove2me | solution 1 for ActuarialValuation.pen9MidSalary_between
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:26:38.573249+00:00
-- url     : https://prove2.me/submissions/eb922c41-d768-4a5b-8f56-69914e951908

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9MidSalary

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b : ℝ) (h : a ≤ b) : a ≤ pen9MidSalary a b ∧ pen9MidSalary a b ≤ b := by
  unfold pen9MidSalary
  constructor <;> linarith
