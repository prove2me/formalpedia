-- Prove2me | solution 1 for ActuarialValuation.erNetLossMGF_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T16:28:28.685115+00:00
-- url     : https://prove2.me/submissions/6f48e7b1-754e-470c-ab69-eb72088fce45

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erNetLossMGF
open ActuarialValuation

theorem solution(lambda premium beta t : ℝ) (hb : beta≠0) : erNetLossMGF lambda premium beta 0 t=1 := by
  unfold erNetLossMGF erLundbergGap erExponentialMGF
  simp [hb]
