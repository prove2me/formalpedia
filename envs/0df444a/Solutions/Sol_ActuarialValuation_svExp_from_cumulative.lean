-- Prove2me | solution 1 for ActuarialValuation.svExp_from_cumulative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:03:38.626984+00:00
-- url     : https://prove2.me/submissions/27be80a4-a5e4-4eca-913b-de29e62e67cd

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_svSurvivalFromCumulativeHazard
import Definitions.Def_actuarial_svExpCumulativeHazard
import Definitions.Def_actuarial_svExpSurvival

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (lambda t : ℝ) : svSurvivalFromCumulativeHazard (svExpCumulativeHazard lambda t) = svExpSurvival lambda t := by
  unfold svSurvivalFromCumulativeHazard svExpCumulativeHazard svExpSurvival
  congr 1
  ring
