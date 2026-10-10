-- Prove2me | solution 1 for ActuarialValuation.gammaPoissonPosteriorRate_sequential
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:40:55.007097+00:00
-- url     : https://prove2.me/submissions/f3cc1215-9e3f-478f-986c-b2a663359380

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_gammaPoissonPosteriorRate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (b e f : ℝ) :
  gammaPoissonPosteriorRate (gammaPoissonPosteriorRate b e) f =
    gammaPoissonPosteriorRate b (e + f) := by
  change (b + e) + f = b + (e + f)
  exact add_assoc b e f
