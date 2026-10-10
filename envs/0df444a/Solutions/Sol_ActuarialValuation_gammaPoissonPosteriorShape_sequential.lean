-- Prove2me | solution 1 for ActuarialValuation.gammaPoissonPosteriorShape_sequential
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:40:47.587839+00:00
-- url     : https://prove2.me/submissions/9c062cb7-c233-402b-8e99-a89e6f4db853

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_gammaPoissonPosteriorShape

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (a : ℝ) (c d : ℕ) :
  gammaPoissonPosteriorShape (gammaPoissonPosteriorShape a c) d =
    gammaPoissonPosteriorShape a (c + d) := by
  change (a + (c : ℝ)) + (d : ℝ) = a + ((c + d : ℕ) : ℝ)
  rw [Nat.cast_add]
  exact add_assoc a (c : ℝ) (d : ℝ)
