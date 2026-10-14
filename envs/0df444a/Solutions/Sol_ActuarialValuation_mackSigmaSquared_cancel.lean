-- Prove2me | solution 1 for ActuarialValuation.mackSigmaSquared_cancel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:38:34.500713+00:00
-- url     : https://prove2.me/submissions/fd399e66-eae9-4b46-b4e7-624422f953d7

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackSigmaSquared

import Mathlib.Tactic.FieldSimp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (v df : ℝ) (hdf : df ≠ 0) : mackSigmaSquared v df * df = v := by
  unfold mackSigmaSquared
  field_simp [hdf]
