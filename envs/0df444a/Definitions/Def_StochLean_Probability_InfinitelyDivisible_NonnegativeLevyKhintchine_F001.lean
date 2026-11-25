-- Prove2me | Definitions.Def_StochLean_Probability_InfinitelyDivisible_NonnegativeLevyKhintchine_F001
-- name    : StochLean_Probability_InfinitelyDivisible_NonnegativeLevyKhintchine_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:41:43.640994+00:00
-- url     : https://prove2.me/theorems/ed5c9d4b-a056-53d7-8e50-734781ff5ca9
-- title:
--   StochLean: Probability.InfinitelyDivisible.NonnegativeLevyKhintchine F001

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_NonnegativeLevyKhintchine_F000
import Definitions.Def_SourceProof_c597cf6ac1143ac927f99acf

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Nonnegative Levy--Khintchine parameters

The canonical parameters of a subordinator consist of a nonnegative deterministic part and a
positive jump measure integrating `min 1 x`.  This file embeds those parameters into StochLean's
fixed-truncation real Levy triplets and proves the constructive half of the nonnegative
Levy--Khintchine theorem, including nonnegative support of the resulting law.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace ProbabilityTheory

namespace NonnegativeLevyPair

noncomputable def toLevyTriplet (η : NonnegativeLevyPair) : LevyTriplet where
  gaussianVariance := 0
  drift := η.deterministicPart + ∫ x, levyTruncation x ∂η.jumpMeasure
  jumpMeasure := η.jumpMeasure
  isLevyMeasure_jumpMeasure := (_root_.Prove2MeSourceProof.h_c597cf6ac1143ac927f99acf η)
end NonnegativeLevyPair
end ProbabilityTheory


