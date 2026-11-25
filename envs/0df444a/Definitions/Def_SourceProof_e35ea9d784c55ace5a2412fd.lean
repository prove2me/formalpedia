-- Prove2me | Definitions.Def_SourceProof_e35ea9d784c55ace5a2412fd
-- name    : SourceProof_e35ea9d784c55ace5a2412fd
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:50:45.837913+00:00
-- url     : https://prove2.me/theorems/f62c0756-5d0d-465e-a482-3010d097b3e1
-- title:
--   StochLean source theorem: ProbabilityTheory.NonnegativeLevyPair.toLevyTriplet_drift

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_NonnegativeLevyKhintchine_F001

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

theorem _root_.Prove2MeSourceProof.h_e35ea9d784c55ace5a2412fd (η : NonnegativeLevyPair) :
    η.toLevyTriplet.drift = η.deterministicPart +
      ∫ x, levyTruncation x ∂η.jumpMeasure := rfl
end NonnegativeLevyPair
end ProbabilityTheory


