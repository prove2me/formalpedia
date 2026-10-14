-- Prove2me | solution 1 for ActuarialValuation.lcLogChange_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:20:24.798029+00:00
-- url     : https://prove2.me/submissions/fb891402-c375-493c-9130-6079d8cdc93d

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_lcLogChange

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (b k1 k2 k3 : ℝ) :
    lcLogChange b k1 k3 = lcLogChange b k1 k2 + lcLogChange b k2 k3 := by
  simp only [lcLogChange]
  ring
