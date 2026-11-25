-- Prove2me | Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F016
-- name    : StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F016
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:21:16.024888+00:00
-- url     : https://prove2.me/theorems/595959c4-d5cd-4896-87cf-26c45b62b3a0
-- title:
--   StochLean: Probability.InfinitelyDivisible.LevyKhintchine F016

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F005
import Definitions.Def_SourceProof_2e36635525ca633ee728e144

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

/-- Nonnegative-real scaling of all triplet components. -/
noncomputable def nnrealSMul (r : ℝ≥0) (η : LevyTriplet) : LevyTriplet where
  gaussianVariance := r * η.gaussianVariance
  drift := (r : ℝ) * η.drift
  jumpMeasure := r • η.jumpMeasure
  isLevyMeasure_jumpMeasure := (_root_.Prove2MeSourceProof.h_2e36635525ca633ee728e144 η.isLevyMeasure_jumpMeasure) r
end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


