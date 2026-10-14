-- Prove2me | solution 1 for ActuarialValuation.gmRelativity_reciprocal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:30:50.217777+00:00
-- url     : https://prove2.me/submissions/1452ecdc-b15a-4a9d-9f89-a72b24866c4a

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

theorem solution (a b : ℝ) : gmRelativity a b * gmRelativity b a = 1 := by
  unfold gmRelativity
  rw [← Real.exp_add]
  have h : a - b + (b - a) = (0 : ℝ) := by ring
  rw [h, Real.exp_zero]
