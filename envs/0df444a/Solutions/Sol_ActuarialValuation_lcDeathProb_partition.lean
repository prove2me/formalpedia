-- Prove2me | solution 1 for ActuarialValuation.lcDeathProb_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:27:13.649054+00:00
-- url     : https://prove2.me/submissions/c0bd6c62-987d-4261-bdbd-1e177721d3d2

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_lcSurvivalProb
import Definitions.Def_actuarial_lcDeathProb

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (force : ℝ) :
    lcDeathProb force + lcSurvivalProb force = 1 := by
  simp only [lcDeathProb, lcSurvivalProb]
  ring
