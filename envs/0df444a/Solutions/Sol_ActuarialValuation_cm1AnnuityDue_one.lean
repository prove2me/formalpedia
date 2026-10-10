-- Prove2me | solution 1 for ActuarialValuation.cm1AnnuityDue_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:14:39.781524+00:00
-- url     : https://prove2.me/submissions/27681918-8b7d-4348-88c5-8bbde1fbaa3a

import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1Accum
import Definitions.Def_actuarial_cm1AnnuityDue
import Definitions.Def_actuarial_cm1Discount
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (i : ℝ) : cm1AnnuityDue i 1 = 1 := by
  simp [cm1AnnuityDue, cm1Discount, cm1Accum]
