-- Prove2me | Definitions.Def_StochLean_Probability_InfinitelyDivisible_Nonnegative_F001
-- name    : StochLean_Probability_InfinitelyDivisible_Nonnegative_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:58:24.183372+00:00
-- url     : https://prove2.me/theorems/1d339229-3ecb-4f38-9697-784238259daf
-- title:
--   StochLean: Probability.InfinitelyDivisible.Nonnegative F001

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_Basic_F000
import Mathlib.MeasureTheory.Group.IntegralConvolution

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Nonnegative convolution semigroups

Support propagation and rational-time approximation for real convolution semigroups.  These
results implement the nonnegative closure part of Klenke Exercises 14.4.3--14.4.4.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal MeasureTheory ProbabilityTheory Topology

namespace ProbabilityTheory

/-! ## Automatic continuity of nonnegative semigroups -/

/-- The Laplace transform at one.  This single value detects concentration at zero for laws
supported by the nonnegative half-line. -/
noncomputable def nonnegativeLaplace (μ : ProbabilityMeasure ℝ) : ℝ :=
  ∫ x, Real.exp (-x) ∂(μ : Measure ℝ)
end ProbabilityTheory


