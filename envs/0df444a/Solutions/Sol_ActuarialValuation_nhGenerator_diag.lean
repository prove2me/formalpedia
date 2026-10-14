-- Prove2me | solution 1 for ActuarialValuation.nhGenerator_diag
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:33:23.860986+00:00
-- url     : https://prove2.me/submissions/bb04500a-02c6-4835-aff8-326b2e8c3cf4

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_nhIntensity
import Definitions.Def_actuarial_nhGenerator

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b p t : ℝ) : nhGenerator a b p t 0 0 = -nhIntensity a b t := by
  simp [nhGenerator]
