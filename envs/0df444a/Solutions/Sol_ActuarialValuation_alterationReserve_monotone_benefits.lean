-- Prove2me | solution 1 for ActuarialValuation.alterationReserve_monotone_benefits
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:11:09.70452+00:00
-- url     : https://prove2.me/submissions/6bb9b0ef-cefc-4758-873a-ed7ccf51d726

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_alterationProspectiveReserve

import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (B1 B2 A P : ℝ) (h : B1 ≤ B2) : alterationProspectiveReserve B1 A P ≤ alterationProspectiveReserve B2 A P := by
  unfold alterationProspectiveReserve
  linarith
