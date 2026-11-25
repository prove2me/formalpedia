-- Prove2me | Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F018
-- name    : StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F018
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:26:37.897187+00:00
-- url     : https://prove2.me/theorems/30280743-2fb4-4fcc-9d99-48429c5371ee
-- title:
--   StochLean: Probability.InfinitelyDivisible.LevyKhintchine F018

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F002
import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F005
import Definitions.Def_SourceProof_00a7b6b1fa0f42c97bc17007

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

/-- The canonical triplet of the positive affine image `a*X+d` under the fixed strict
truncation.  The integral term is essential: omitting it changes the characteristic exponent. -/
noncomputable def affine (η : LevyTriplet) (a d : ℝ) (ha : 0 < a) : LevyTriplet where
  gaussianVariance := (Real.toNNReal a) ^ 2 * η.gaussianVariance
  drift := a * η.drift + d + ∫ x, affineDriftIntegrand a x ∂η.jumpMeasure
  jumpMeasure := η.jumpMeasure.map (fun x => a * x)
  isLevyMeasure_jumpMeasure := (_root_.Prove2MeSourceProof.h_00a7b6b1fa0f42c97bc17007 η.isLevyMeasure_jumpMeasure) ha.ne'
end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


