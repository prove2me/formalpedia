-- Prove2me | Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F013
-- name    : StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F013
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:20:38.853012+00:00
-- url     : https://prove2.me/theorems/dd26f517-a3c2-4d72-981f-cce755dbbf28
-- title:
--   StochLean: Probability.InfinitelyDivisible.LevyKhintchine F013

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

/-- The canonical probability-measure wrapper around Mathlib's real Gaussian law. -/
noncomputable def gaussianLaw (m : ℝ) (v : ℝ≥0) : ProbabilityMeasure ℝ :=
  ⟨gaussianReal m v, inferInstance⟩
end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


