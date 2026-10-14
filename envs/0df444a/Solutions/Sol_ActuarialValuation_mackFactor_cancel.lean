-- Prove2me | solution 1 for ActuarialValuation.mackFactor_cancel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:34:43.14617+00:00
-- url     : https://prove2.me/submissions/c84f0a3d-1658-44eb-a237-20326fcaed11

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackNumerator
import Definitions.Def_actuarial_mackDenominator
import Definitions.Def_actuarial_mackFactor

import Mathlib.Tactic.FieldSimp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (c : ℕ → ℕ → ℝ) (m j : ℕ) (h : mackDenominator c m j ≠ 0) : mackFactor c m j * mackDenominator c m j = mackNumerator c m j := by
  unfold mackFactor
  field_simp [h]
