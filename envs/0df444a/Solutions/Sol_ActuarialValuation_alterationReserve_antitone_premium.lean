-- Prove2me | solution 1 for ActuarialValuation.alterationReserve_antitone_premium
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:11:20.854667+00:00
-- url     : https://prove2.me/submissions/bf58db81-30ee-4962-a4c2-cba14491d0e0

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_alterationProspectiveReserve

import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (B A P1 P2 : ℝ) (hA : 0 ≤ A) (hP : P1 ≤ P2) : alterationProspectiveReserve B A P2 ≤ alterationProspectiveReserve B A P1 := by
  have hmul : P1 * A ≤ P2 * A := mul_le_mul_of_nonneg_right hP hA
  unfold alterationProspectiveReserve
  linarith
