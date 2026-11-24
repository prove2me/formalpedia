-- Prove2me | Definitions.Def_StochLean_Probability_InfinitelyDivisible_Nonnegative_F002
-- name    : StochLean_Probability_InfinitelyDivisible_Nonnegative_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:58:42.838685+00:00
-- url     : https://prove2.me/theorems/12804bf7-13d7-4787-8a28-269914afab6d
-- title:
--   StochLean: Probability.InfinitelyDivisible.Nonnegative F002

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

noncomputable def nonnegativeLaplaceDefect (μ : ProbabilityMeasure ℝ) : ℝ :=
  ∫ x, 1 - Real.exp (-x) ∂(μ : Measure ℝ)
end ProbabilityTheory


