-- Prove2me | Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F004
-- name    : StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F004
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:02:45.226559+00:00
-- url     : https://prove2.me/theorems/faa876d3-efbc-45e6-a335-150797dc564f
-- title:
--   StochLean: Probability.InfinitelyDivisible.LevyKhintchine F004

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

/-- Jump integrand written with an explicit admissible truncation. -/
noncomputable def levyExponentIntegrandWithTruncation (k : ℝ → ℝ) (t x : ℝ) : ℂ :=
  Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
    (((t * k x : ℝ) : ℂ) * Complex.I)
namespace LevyTriplet

end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


