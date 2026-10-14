-- Prove2me | solution 1 for ActuarialValuation.alterationRevisedReserve_delta
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:14:08.178224+00:00
-- url     : https://prove2.me/submissions/c8494cf6-c73f-49b7-8b62-a33aa736c15d

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_alterationRevisedReserve

import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (B A P1 P2 : ℝ) : alterationRevisedReserve B P2 A - alterationRevisedReserve B P1 A = (P1-P2)*A := by
  unfold alterationRevisedReserve
  ring
