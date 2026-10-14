-- Prove2me | solution 1 for ActuarialValuation.gmRelativity_transitive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:31:48.941603+00:00
-- url     : https://prove2.me/submissions/8fe19240-7f9f-4f1b-919c-c7b4169ebb8f

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_gmRelativity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b c : ℝ) :
    gmRelativity a c = gmRelativity a b * gmRelativity b c := by
  unfold gmRelativity
  rw [← Real.exp_add]
  congr 1
  ring
