-- Prove2me | solution 1 for ActuarialValuation.gammaPoissonPosteriorRate_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:40:07.094983+00:00
-- url     : https://prove2.me/submissions/33fa3af4-3c9f-42e9-b8e7-51d0e3e14add

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_gammaPoissonPosteriorRate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (b : ℝ) :
  gammaPoissonPosteriorRate b 0 = b := by
  simp [gammaPoissonPosteriorRate]
