-- Prove2me | Definitions.Def_StochLean_Probability_InfinitelyDivisible_Nonnegative_F000
-- name    : StochLean_Probability_InfinitelyDivisible_Nonnegative_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:58:42.144417+00:00
-- url     : https://prove2.me/theorems/dbace03f-54f3-4841-964b-d90e7f84d7d9
-- title:
--   StochLean: Probability.InfinitelyDivisible.Nonnegative F000

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

noncomputable def rationalFloorApprox (u t : ℝ≥0) (n : ℕ) : ℝ≥0 :=
  (⌊((n : ℝ≥0) + 1) * (t / u)⌋₊ : ℝ≥0) * (u / ((n : ℝ≥0) + 1))
/-! ## Automatic continuity of nonnegative semigroups -/

end ProbabilityTheory


