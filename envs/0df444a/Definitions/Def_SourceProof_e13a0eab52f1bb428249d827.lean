-- Prove2me | Definitions.Def_SourceProof_e13a0eab52f1bb428249d827
-- name    : SourceProof_e13a0eab52f1bb428249d827
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:59:22.258842+00:00
-- url     : https://prove2.me/theorems/1085f9c5-d6af-4acb-b8a7-058c0b60cf15
-- title:
--   StochLean source theorem: ProbabilityTheory.NonnegativeLevyPair.eq_of_toLevyTriplet_eq

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_NonnegativeLevyKhintchine_F001
import Definitions.Def_SourceProof_e35ea9d784c55ace5a2412fd

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


theorem _root_.Prove2MeSourceProof.h_e13a0eab52f1bb428249d827 {η ξ : NonnegativeLevyPair}
    (h : η.toLevyTriplet = ξ.toLevyTriplet) : η = ξ := by
  have hjump : η.jumpMeasure = ξ.jumpMeasure :=
    congrArg ProbabilityTheory.LevyTriplet.jumpMeasure h
  have hdrift : η.toLevyTriplet.drift = ξ.toLevyTriplet.drift :=
    congrArg ProbabilityTheory.LevyTriplet.drift h
  have hdet : η.deterministicPart = ξ.deterministicPart := by
    apply NNReal.eq
    rw [_root_.Prove2MeSourceProof.h_e35ea9d784c55ace5a2412fd, _root_.Prove2MeSourceProof.h_e35ea9d784c55ace5a2412fd, hjump] at hdrift
    exact_mod_cast add_right_cancel hdrift
  cases η
  cases ξ
  simp_all
end NonnegativeLevyPair
end ProbabilityTheory


