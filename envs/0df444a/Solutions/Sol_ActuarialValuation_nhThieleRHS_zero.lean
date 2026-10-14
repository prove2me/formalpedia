-- Prove2me | solution 1 for ActuarialValuation.nhThieleRHS_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:36:44.686974+00:00
-- url     : https://prove2.me/submissions/c082fabc-83bd-4a5e-b474-01cd25bf73fa

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_nhIntensity
import Definitions.Def_actuarial_nhCauseBenefit
import Definitions.Def_actuarial_nhThieleRHS

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b p δ B1 B2 t : ℝ) : nhThieleRHS a b p δ B1 B2 t 0 = -nhIntensity a b t*nhCauseBenefit p B1 B2 := by
  simp [nhThieleRHS]
