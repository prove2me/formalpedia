-- Prove2me | solution 1 for ActuarialValuation.bnTwoStep_backwards
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:02:26.953475+00:00
-- url     : https://prove2.me/submissions/112b0673-e38d-4a61-8df8-2aecead705a8

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnTwoStepBackward
import Definitions.Def_actuarial_bnTwoStepPrice

import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (R q uu ud du dd : ℝ) (hR : R ≠ 0) : bnTwoStepBackward R q uu ud du dd = bnTwoStepPrice R q uu ud du dd := by
  unfold bnTwoStepBackward bnTwoStepPrice bnOnePeriodPrice bnExpectedPayoff
  field_simp [hR] <;> ring
