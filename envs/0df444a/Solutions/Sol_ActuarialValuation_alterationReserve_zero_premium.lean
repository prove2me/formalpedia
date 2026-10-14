-- Prove2me | solution 1 for ActuarialValuation.alterationReserve_zero_premium
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:10:44.331648+00:00
-- url     : https://prove2.me/submissions/d76397ab-a6ad-4d3a-afc3-0e54fa20eb65

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_alterationProspectiveReserve



set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (B A : ℝ) : alterationProspectiveReserve B A 0 = B := by
  simp [alterationProspectiveReserve]
