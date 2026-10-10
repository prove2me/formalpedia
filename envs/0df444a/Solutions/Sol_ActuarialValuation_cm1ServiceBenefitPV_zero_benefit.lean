-- Prove2me | solution 1 for ActuarialValuation.cm1ServiceBenefitPV_zero_benefit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:27:23.627991+00:00
-- url     : https://prove2.me/submissions/785c7c34-9f49-425c-bda2-62f270b7d808

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ServiceBenefitPV
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (v : ℕ → ℝ) (d : ℕ → ℕ → ℝ) (l : ℕ → ℝ) (N m : ℕ) : cm1ServiceBenefitPV v (fun _ _ => 0) d l N m = 0 := by
  simp [cm1ServiceBenefitPV]
