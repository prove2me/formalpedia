-- Prove2me | solution 1 for ActuarialValuation.erLundbergGap_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T16:20:52.755095+00:00
-- url     : https://prove2.me/submissions/578d45df-e228-4073-ba42-4c8ad6a3bfa4

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erLundbergGap
open ActuarialValuation

theorem solution(lambda premium beta : ℝ) (hb : beta≠0) : erLundbergGap lambda premium beta 0=0 := by
  unfold erLundbergGap erExponentialMGF
  field_simp
  ring
