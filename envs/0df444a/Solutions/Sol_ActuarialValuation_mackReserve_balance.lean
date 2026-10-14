-- Prove2me | solution 1 for ActuarialValuation.mackReserve_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:39:48.176527+00:00
-- url     : https://prove2.me/submissions/f6e2797e-0b8a-441f-89c0-5aea44205ba0

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackReserve

import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (projected current : ℝ) : current + mackReserve projected current = projected := by
  unfold mackReserve
  ring
