-- Prove2me | solution 1 for ActuarialValuation.finiteKernel_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T08:10:51.162985+00:00
-- url     : https://prove2.me/submissions/eb452696-a05e-4b19-99df-3c6fd1fdf1df

import Mathlib
import Definitions.Def_actuarial_isFiniteMarkovKernel
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {S : Type*} [Fintype S] (P : S → S → ℝ) (hP : isFiniteMarkovKernel P) (a b : S)
    :
    0 ≤ P a b := And.left hP a b
