-- Prove2me | solution 1 for ActuarialValuation.gammaPoissonPosteriorMean_sequential
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:41:02.221304+00:00
-- url     : https://prove2.me/submissions/77e39d60-d487-453b-935f-5cf4b55b6460

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_gammaPoissonPosteriorMean
import Definitions.Def_actuarial_gammaPoissonPosteriorShape
import Definitions.Def_actuarial_gammaPoissonPosteriorRate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (a b e f : ℝ) (c d : ℕ) :
  gammaPoissonPosteriorMean
    (gammaPoissonPosteriorShape a c)
    (gammaPoissonPosteriorRate b e) f d =
  gammaPoissonPosteriorMean a b (e + f) (c + d) := by
  simp [gammaPoissonPosteriorMean, gammaPoissonPosteriorShape,
    gammaPoissonPosteriorRate, Nat.cast_add, add_assoc]
