-- Prove2me | solution 1 for ActuarialValuation.cm1ServiceBenefitPV_zero_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:26:46.773007+00:00
-- url     : https://prove2.me/submissions/a9d685a8-ffae-4b65-8ae9-794b38a88040

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

theorem solution (v : ℕ → ℝ) (b d : ℕ → ℕ → ℝ) (l : ℕ → ℝ) (m : ℕ) : cm1ServiceBenefitPV v b d l 0 m = 0 := by
  simp [cm1ServiceBenefitPV]
