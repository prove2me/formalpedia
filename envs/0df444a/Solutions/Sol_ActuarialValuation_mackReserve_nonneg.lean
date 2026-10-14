-- Prove2me | solution 1 for ActuarialValuation.mackReserve_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:39:59.213096+00:00
-- url     : https://prove2.me/submissions/825ec7a6-405a-4f2e-aa34-0680a36636c6

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackReserve

import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (projected current : ℝ) (h : current ≤ projected) : 0 ≤ mackReserve projected current := by
  unfold mackReserve
  linarith
