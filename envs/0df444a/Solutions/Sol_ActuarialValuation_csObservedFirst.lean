-- Prove2me | solution 1 for ActuarialValuation.csObservedFirst
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:52:53.254685+00:00
-- url     : https://prove2.me/submissions/1a12101a-e11f-405f-ba5c-6f7c7a21c4b3

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_csFirstFailure
import Definitions.Def_actuarial_csFirstLife
import Definitions.Def_actuarial_csSecondLife

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {Ω : Type*} (U V Z : Ω → ℝ) (ω : Ω) :
    csFirstFailure U V Z ω =
      min (csFirstLife U Z ω) (csSecondLife V Z ω) := by
  simp [csFirstFailure, csFirstLife, csSecondLife,
    min_assoc, min_left_comm, min_comm]
