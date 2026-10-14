-- Prove2me | solution 1 for ActuarialValuation.mackSquaredResidual_symm
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:35:32.757796+00:00
-- url     : https://prove2.me/submissions/2149c4e4-8389-45fa-9d5f-bc660b65da6d

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackSquaredResidual

import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b : ℝ) : mackSquaredResidual a b = mackSquaredResidual b a := by
  unfold mackSquaredResidual
  ring
