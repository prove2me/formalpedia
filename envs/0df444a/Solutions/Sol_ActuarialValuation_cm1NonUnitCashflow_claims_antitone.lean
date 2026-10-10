-- Prove2me | solution 1 for ActuarialValuation.cm1NonUnitCashflow_claims_antitone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:20:29.722857+00:00
-- url     : https://prove2.me/submissions/8964793a-26cf-4d23-a079-46ec50a39c3d

import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1NonUnitCashflow

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (P C E B₁ B₂ : ℝ) (h : B₁ ≤ B₂) : cm1NonUnitCashflow P C E B₂ ≤ cm1NonUnitCashflow P C E B₁ := by
  unfold cm1NonUnitCashflow
  linarith
