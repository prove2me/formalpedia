-- Prove2me | solution 1 for ActuarialValuation.bdStatePV_empty
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:01:22.057364+00:00
-- url     : https://prove2.me/submissions/a78fa106-f6c4-4c39-a97b-71376ab0bac4

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdStatePV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (discount payoff : Fin 0 → ℝ) : bdStatePV (fun _ => 0) discount payoff = 0 := by
  simp [bdStatePV]
