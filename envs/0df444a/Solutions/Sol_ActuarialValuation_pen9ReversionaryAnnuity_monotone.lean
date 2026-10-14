-- Prove2me | solution 1 for ActuarialValuation.pen9ReversionaryAnnuity_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:11:13.760021+00:00
-- url     : https://prove2.me/submissions/59784175-4756-401d-9436-c5f324d5e798

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9ReversionaryAnnuity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (member spouse r₁ r₂ : ℝ) (hs : 0 ≤ spouse) (hr : r₁ ≤ r₂) : pen9ReversionaryAnnuity member spouse r₁ ≤ pen9ReversionaryAnnuity member spouse r₂ := by
  unfold pen9ReversionaryAnnuity
  exact add_le_add_right (mul_le_mul_of_nonneg_right hr hs) member
