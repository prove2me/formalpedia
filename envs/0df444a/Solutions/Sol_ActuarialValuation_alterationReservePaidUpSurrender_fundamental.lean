-- Prove2me | solution 1 for ActuarialValuation.alterationReservePaidUpSurrender_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:18:55.988773+00:00
-- url     : https://prove2.me/submissions/0df15677-5397-4bfd-aea5-50d4ee250265

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_alterationProspectiveReserve
import Definitions.Def_actuarial_alterationRepricedPremium
import Definitions.Def_actuarial_alterationPremiumDifference
import Definitions.Def_actuarial_alterationPaidUpBenefit
import Definitions.Def_actuarial_alterationPaidUpValue
import Definitions.Def_actuarial_alterationSurrenderValue

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (B A P unitPV deduction : ℝ) (hA : A ≠ 0) (hu : 0 < unitPV) (hV : 0 ≤ alterationProspectiveReserve B A P) (hd : 0 ≤ deduction) (hle : deduction ≤ alterationProspectiveReserve B A P) : (alterationPremiumDifference (alterationRepricedPremium B A) P A = alterationProspectiveReserve B A P) ∧ (alterationPaidUpValue (alterationPaidUpBenefit (alterationProspectiveReserve B A P) unitPV) unitPV = alterationProspectiveReserve B A P) ∧ (0 ≤ alterationSurrenderValue (alterationProspectiveReserve B A P) deduction) ∧ (alterationSurrenderValue (alterationProspectiveReserve B A P) deduction ≤ alterationProspectiveReserve B A P) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold alterationPremiumDifference alterationRepricedPremium alterationProspectiveReserve
    field_simp [hA] <;> ring
  · unfold alterationPaidUpValue alterationPaidUpBenefit
    field_simp [ne_of_gt hu] <;> ring
  · unfold alterationSurrenderValue
    linarith
  · unfold alterationSurrenderValue
    linarith
