-- Prove2me | solution 1 for ActuarialValuation.bnTwoStep_const
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:02:37.161233+00:00
-- url     : https://prove2.me/submissions/d8201450-17f6-4e59-851a-6838b60228db

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnTwoStepPrice

import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (R q x : ℝ) (hR : R ≠ 0) : bnTwoStepPrice R q x x x x = x/(R*R) := by
  unfold bnTwoStepPrice
  field_simp [hR] <;> ring
