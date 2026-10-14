-- Prove2me | solution 1 for ActuarialValuation.csFirstSurvival_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:10:05.844996+00:00
-- url     : https://prove2.me/submissions/db1c5417-4d4e-4ea0-a606-5f02a69e1815

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_csFirstExp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b c t : ℝ) :
    csFirstExp a b c t =
      Real.exp (-a*t) * Real.exp (-b*t) * Real.exp (-c*t) := by
  unfold csFirstExp
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring
