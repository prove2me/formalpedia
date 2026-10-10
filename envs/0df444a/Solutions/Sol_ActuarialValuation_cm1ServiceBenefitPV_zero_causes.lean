-- Prove2me | solution 1 for ActuarialValuation.cm1ServiceBenefitPV_zero_causes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:26:54.010862+00:00
-- url     : https://prove2.me/submissions/691d3d43-07d8-4d3a-8326-7d119175a773

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

theorem solution (v : ℕ → ℝ) (b d : ℕ → ℕ → ℝ) (l : ℕ → ℝ) (N : ℕ) : cm1ServiceBenefitPV v b d l N 0 = 0 := by
  simp [cm1ServiceBenefitPV]
