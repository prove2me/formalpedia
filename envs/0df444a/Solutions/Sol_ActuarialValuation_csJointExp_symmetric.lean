-- Prove2me | solution 1 for ActuarialValuation.csJointExp_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:02:08.664995+00:00
-- url     : https://prove2.me/submissions/ce1effa2-85f2-4f6d-94e4-7d2b63df2138

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_csJointExp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b c s t : ℝ) :
    csJointExp a b c s t = csJointExp b a c t s := by
  unfold csJointExp
  congr 1
  rw [max_comm s t]
  ring
