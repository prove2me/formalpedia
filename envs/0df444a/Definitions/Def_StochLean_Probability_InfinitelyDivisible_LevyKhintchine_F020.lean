-- Prove2me | Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F020
-- name    : StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F020
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:21:53.983811+00:00
-- url     : https://prove2.me/theorems/762e58b0-1131-4269-981e-bd5cc03b578a
-- title:
--   StochLean: Probability.InfinitelyDivisible.LevyKhintchine F020

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

/-- Fixed-truncation triplet attached directly to a finite jump-intensity measure.  This entry
point is zero-safe and does not normalize the measure. -/
noncomputable def tripletOfFiniteMeasure (ν : FiniteMeasure ℝ)
    (hzero : (ν : Measure ℝ) {0} = 0) : LevyTriplet where
  gaussianVariance := 0
  drift := ∫ x, levyTruncation x ∂(ν : Measure ℝ)
  jumpMeasure := ν
  isLevyMeasure_jumpMeasure := _root_.Prove2MeSourceProof.h_a0955a4e2c3724551cc21f56 hzero
end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


