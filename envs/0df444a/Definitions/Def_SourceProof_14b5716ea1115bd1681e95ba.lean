-- Prove2me | Definitions.Def_SourceProof_14b5716ea1115bd1681e95ba
-- name    : SourceProof_14b5716ea1115bd1681e95ba
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:05:10.174811+00:00
-- url     : https://prove2.me/theorems/6bbd2f3c-6592-4244-bce7-39556483f7b5
-- title:
--   StochLean source theorem: ProbabilityTheory.NonnegativeLevyPair.eq_of_represents

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_NonnegativeLevyKhintchine_F001
import Definitions.Def_SourceProof_c73060eb85da9035497d5cd7
import Definitions.Def_SourceProof_e13a0eab52f1bb428249d827

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


theorem _root_.Prove2MeSourceProof.h_14b5716ea1115bd1681e95ba {η ξ : NonnegativeLevyPair} {μ : ProbabilityMeasure ℝ}
    (hη : η.toLevyTriplet.Represents μ) (hξ : ξ.toLevyTriplet.Represents μ) : η = ξ :=
  _root_.Prove2MeSourceProof.h_e13a0eab52f1bb428249d827 ((_root_.Prove2MeSourceProof.h_c73060eb85da9035497d5cd7 hη) hξ)
end NonnegativeLevyPair
end ProbabilityTheory


