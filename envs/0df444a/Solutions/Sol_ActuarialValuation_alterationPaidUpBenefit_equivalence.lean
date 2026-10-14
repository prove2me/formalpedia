-- Prove2me | solution 1 for ActuarialValuation.alterationPaidUpBenefit_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:14:32.150977+00:00
-- url     : https://prove2.me/submissions/f3721791-ac5a-46f9-abb3-abd2d2ab45f7

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_alterationPaidUpBenefit
import Definitions.Def_actuarial_alterationPaidUpValue

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (V A : ℝ) (hA : A ≠ 0) : alterationPaidUpValue (alterationPaidUpBenefit V A) A = V := by
  unfold alterationPaidUpValue alterationPaidUpBenefit
  field_simp [hA] <;> ring
