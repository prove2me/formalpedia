-- Prove2me | solution 1 for ActuarialValuation.alterationPremiumDifference_equivalent_reserve
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:13:55.146132+00:00
-- url     : https://prove2.me/submissions/eccd69d6-4140-4fb6-9d9f-3be58a187891

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_alterationProspectiveReserve
import Definitions.Def_actuarial_alterationRepricedPremium
import Definitions.Def_actuarial_alterationPremiumDifference

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (B A P : ℝ) (hA : A ≠ 0) : alterationPremiumDifference (alterationRepricedPremium B A) P A = alterationProspectiveReserve B A P := by
  unfold alterationPremiumDifference alterationRepricedPremium alterationProspectiveReserve
  field_simp [hA] <;> ring
