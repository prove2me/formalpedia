-- Prove2me | solution 1 for ActuarialValuation.finiteKernel_row_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:15:12.371042+00:00
-- url     : https://prove2.me/submissions/7cca7d98-46ab-4edd-8dc7-77f4d8fa9923

import Mathlib
import Definitions.Def_actuarial_isFiniteMarkovKernel
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {S : Type*} [Fintype S] (P : S → S → ℝ) (hP : isFiniteMarkovKernel P) (a : S)
    :
    (∑ b : S, P a b) = 1 := hP.2 a
