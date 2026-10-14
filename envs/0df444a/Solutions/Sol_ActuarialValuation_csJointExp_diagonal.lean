-- Prove2me | solution 1 for ActuarialValuation.csJointExp_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:03:32.97354+00:00
-- url     : https://prove2.me/submissions/57fff2a6-6023-436f-aee8-1469a3cda0c4

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_csJointExp
import Definitions.Def_actuarial_csFirstExp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b c t : ℝ) :
    csJointExp a b c t t = csFirstExp a b c t := by
  simp only [csJointExp, csFirstExp, max_self]
  congr 1
  ring
