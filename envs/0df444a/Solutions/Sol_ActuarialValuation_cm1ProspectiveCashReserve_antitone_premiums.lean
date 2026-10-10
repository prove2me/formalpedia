-- Prove2me | solution 1 for ActuarialValuation.cm1ProspectiveCashReserve_antitone_premiums
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:18:38.037213+00:00
-- url     : https://prove2.me/submissions/8a4e9fdf-3a06-4f04-ad8b-ad80e610d5f8

import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ProspectiveCashReserve

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (B E P₁ P₂ : ℝ) (h : P₁ ≤ P₂) : cm1ProspectiveCashReserve B E P₂ ≤ cm1ProspectiveCashReserve B E P₁ := by
  unfold cm1ProspectiveCashReserve
  linarith
