-- Prove2me | solution 1 for ActuarialValuation.cm1ProspectiveCashReserve_mono_benefits
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:18:31.593362+00:00
-- url     : https://prove2.me/submissions/42a5effe-c030-4484-8d99-c3951d784c5f

import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ProspectiveCashReserve

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (B₁ B₂ E P : ℝ) (h : B₁ ≤ B₂) : cm1ProspectiveCashReserve B₁ E P ≤ cm1ProspectiveCashReserve B₂ E P := by
  unfold cm1ProspectiveCashReserve
  linarith
