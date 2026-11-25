-- Prove2me | Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F019
-- name    : StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F019
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:21:52.365026+00:00
-- url     : https://prove2.me/theorems/3231014f-cfc2-4c54-b34e-9a513755cb52
-- title:
--   StochLean: Probability.InfinitelyDivisible.LevyKhintchine F019

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F005
import Definitions.Def_SourceProof_a0955a4e2c3724551cc21f56

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

/-- The fixed-truncation triplet of a compound Poisson law whose jump law has no atom at zero.
The drift is derived from the truncation convention rather than guessed. -/
noncomputable def triplet (r : ℝ≥0) (μ : ProbabilityMeasure ℝ)
    (hzero : (μ : Measure ℝ) {0} = 0) : LevyTriplet where
  gaussianVariance := 0
  drift := ∫ x, levyTruncation x ∂(r • (μ : Measure ℝ))
  jumpMeasure := r • (μ : Measure ℝ)
  isLevyMeasure_jumpMeasure := _root_.Prove2MeSourceProof.h_a0955a4e2c3724551cc21f56 (by
    simp [Measure.smul_apply, hzero])
end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


