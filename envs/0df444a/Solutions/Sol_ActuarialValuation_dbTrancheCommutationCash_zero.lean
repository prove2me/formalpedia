-- Prove2me | solution 1 for ActuarialValuation.dbTrancheCommutationCash_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:10:46.32729+00:00
-- url     : https://prove2.me/submissions/8f5caf2c-e746-43d7-b252-e80d703d48dc

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_dbTrancheCommutationCash

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (factor reduction : ℕ → ℝ) :
  dbTrancheCommutationCash factor reduction 0 = 0 := by
  simp [dbTrancheCommutationCash]
