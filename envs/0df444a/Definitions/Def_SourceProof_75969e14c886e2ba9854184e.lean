-- Prove2me | Definitions.Def_SourceProof_75969e14c886e2ba9854184e
-- name    : SourceProof_75969e14c886e2ba9854184e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:14:24.762463+00:00
-- url     : https://prove2.me/theorems/5f8217e2-797b-4237-bf00-c33ef7cc7d32
-- title:
--   StochLean source theorem: ProbabilityTheory.CompoundPoisson.normalize_apply_zero_eq_zero

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_CompoundPoisson_F001
import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyMeasure_F001
import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyMeasure_F002
import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyMeasure_F003
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Probability.Distributions.Gaussian.Real

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Lévy triplets and the fixed truncation convention

This module fixes the data and truncation convention used by the real Lévy--Khintchine layer.  It
does not store an infinitely-divisible law or a representation theorem inside the triplet.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

namespace LevyTriplet

end LevyTriplet

namespace CompoundPoisson

theorem _root_.Prove2MeSourceProof.h_75969e14c886e2ba9854184e {ν : FiniteMeasure ℝ} (hν : ν ≠ 0)
    (hzero : (ν : Measure ℝ) {0} = 0) :
    (ν.normalize : Measure ℝ) {0} = 0 := by
  rw [ν.toMeasure_normalize_eq_of_nonzero hν]
  simp [Measure.smul_apply, hzero]
end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


