-- Prove2me | solution 1 for ActuarialValuation.erNetLossMGF_add_time
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:37:32.4233+00:00
-- url     : https://prove2.me/submissions/36ebee2f-c71b-4ee0-97ab-e9e485623d7a

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erNetLossMGF

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (lambda premium beta r s t : ℝ) :
    erNetLossMGF lambda premium beta r (s+t) =
      erNetLossMGF lambda premium beta r s * erNetLossMGF lambda premium beta r t := by
  unfold erNetLossMGF
  rw [show (s+t) * erLundbergGap lambda premium beta r =
    s * erLundbergGap lambda premium beta r + t * erLundbergGap lambda premium beta r by ring,
    Real.exp_add]
