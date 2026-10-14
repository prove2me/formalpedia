-- Prove2me | solution 1 for ActuarialValuation.lcLogRate_index_difference
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:18:32.990154+00:00
-- url     : https://prove2.me/submissions/5a447192-2303-4851-9c5a-bac4f76355e4

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_lcLogRate
import Definitions.Def_actuarial_lcLogChange

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b k1 k2 : ℝ) :
    lcLogRate a b k2 - lcLogRate a b k1 = lcLogChange b k1 k2 := by
  simp only [lcLogRate, lcLogChange]
  ring
