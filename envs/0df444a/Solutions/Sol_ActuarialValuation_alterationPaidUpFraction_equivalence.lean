-- Prove2me | solution 1 for ActuarialValuation.alterationPaidUpFraction_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:16:55.98933+00:00
-- url     : https://prove2.me/submissions/1c503ae0-725b-4672-9386-63686baa5203

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_alterationPaidUpFraction
import Definitions.Def_actuarial_alterationPaidUpScaledValue

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (V B : ℝ) (hB : B ≠ 0) : alterationPaidUpScaledValue (alterationPaidUpFraction V B) B = V := by
  unfold alterationPaidUpScaledValue alterationPaidUpFraction
  field_simp [hB] <;> ring
