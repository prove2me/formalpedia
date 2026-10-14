-- Prove2me | solution 1 for ActuarialValuation.bnRiskNeutralStock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:01:21.513978+00:00
-- url     : https://prove2.me/submissions/b285418c-0e1e-444f-b0d6-be167656691d

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnExpectedPayoff
import Definitions.Def_actuarial_bnRiskNeutralProb

import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (s u d R : ℝ) (h : u ≠ d) : bnExpectedPayoff (bnRiskNeutralProb u d R) (s*u) (s*d) = s*R := by
  unfold bnExpectedPayoff bnRiskNeutralProb
  field_simp [sub_ne_zero.mpr h] <;> ring
