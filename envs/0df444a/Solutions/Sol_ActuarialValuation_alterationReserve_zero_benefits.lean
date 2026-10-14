-- Prove2me | solution 1 for ActuarialValuation.alterationReserve_zero_benefits
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:10:57.473984+00:00
-- url     : https://prove2.me/submissions/307f589a-beec-46fe-ac01-c7903baf79f7

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_alterationProspectiveReserve



set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (A P : ℝ) : alterationProspectiveReserve 0 A P = -(P*A) := by
  simp [alterationProspectiveReserve]
