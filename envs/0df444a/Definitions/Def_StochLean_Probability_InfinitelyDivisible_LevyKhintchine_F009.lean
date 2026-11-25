-- Prove2me | Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F009
-- name    : StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F009
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:36:42.434992+00:00
-- url     : https://prove2.me/theorems/8a033221-669b-40e2-aac3-3215a1a7a3ec
-- title:
--   StochLean: Probability.InfinitelyDivisible.LevyKhintchine F009

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F005
import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F008
import Definitions.Def_SourceProof_3a5b9f54ddb8a807b6d720b1

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

noncomputable def weightedJumpMeasure (η : LevyTriplet) (s : ℝ) : Measure ℝ :=
    η.jumpMeasure.withDensity (fun x => (secondDifferenceWeight s x : ℝ≥0∞))
instance instFiniteWeightedJumpMeasure (η : LevyTriplet) (s : ℝ) :
    IsFiniteMeasure (weightedJumpMeasure η s) := by
  apply IsFiniteMeasure.mk
  simp only [weightedJumpMeasure,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  simpa [hasFiniteIntegral_iff_norm] using
    (_root_.Prove2MeSourceProof.h_3a5b9f54ddb8a807b6d720b1 η s).hasFiniteIntegral
noncomputable def secondDifferenceMeasure (η : LevyTriplet) (s : ℝ) : Measure ℝ :=
  ENNReal.ofReal ((η.gaussianVariance : ℝ) * s ^ 2) • Measure.dirac 0 +
    weightedJumpMeasure η s
instance instFiniteSecondDifferenceMeasure (η : LevyTriplet) (s : ℝ) :
    IsFiniteMeasure (secondDifferenceMeasure η s) := by
  apply IsFiniteMeasure.mk
  simp only [secondDifferenceMeasure, Measure.add_apply, Measure.smul_apply,
    MeasurableSet.univ]
  rw [ENNReal.add_lt_top]
  refine ⟨?_, measure_lt_top _ _⟩
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


