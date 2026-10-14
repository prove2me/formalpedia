-- Prove2me | solution 1 for ActuarialValuation.lcLogChange_reverse
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:19:29.290926+00:00
-- url     : https://prove2.me/submissions/4ca3cdb6-0e67-4c5e-8775-61b273814b24

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_lcLogChange

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (b k1 k2 : ℝ) :
    lcLogChange b k1 k2 = - lcLogChange b k2 k1 := by
  simp only [lcLogChange]
  ring
