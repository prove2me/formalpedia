-- Prove2me | solution 1 for ActuarialValuation.gammaPoissonPosteriorMean_no_data
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:40:38.464085+00:00
-- url     : https://prove2.me/submissions/43549103-d372-4fbe-b8ff-a4c6e9d91f6e

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

theorem solution (a b : ℝ) :
  gammaPoissonPosteriorMean a b 0 0 = a / b := by
  simp [gammaPoissonPosteriorMean, gammaPoissonPosteriorShape,
    gammaPoissonPosteriorRate]
