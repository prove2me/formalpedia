-- Prove2me | Definitions.Def_SourceProof_ec94ee002a1dbd27a305ed82
-- name    : SourceProof_ec94ee002a1dbd27a305ed82
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:27:03.402671+00:00
-- url     : https://prove2.me/theorems/f4e77ffa-6af0-5524-ac6d-4e5d969013fa
-- title:
--   StochLean source theorem: ProbabilityTheory.NonnegativeLevyPair.integrable_levyTruncation

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_NonnegativeLevyKhintchine_F000
import Definitions.Def_SourceProof_7e961aa121c5246639f2cd81
import Definitions.Def_SourceProof_9d54591e608c50f52d7e3085
import Definitions.Def_SourceProof_a9854b69af6573818338f60b

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

theorem _root_.Prove2MeSourceProof.h_ec94ee002a1dbd27a305ed82 (η : NonnegativeLevyPair) :
    Integrable levyTruncation η.jumpMeasure := by
  apply η.integrable_min_one.mono (_root_.Prove2MeSourceProof.h_9d54591e608c50f52d7e3085.aestronglyMeasurable)
  filter_upwards [η.supportedPositive] with x hx
  by_cases hsmall : x < 1
  · have habs : |x| < 1 := by simpa [abs_of_pos hx] using hsmall
    rw [_root_.Prove2MeSourceProof.h_7e961aa121c5246639f2cd81 habs, Real.norm_eq_abs, abs_of_pos hx,
      min_eq_right hsmall.le, Real.norm_eq_abs, abs_of_pos hx]
  · have hone : 1 ≤ |x| := by simpa [abs_of_pos hx] using le_of_not_gt hsmall
    rw [_root_.Prove2MeSourceProof.h_a9854b69af6573818338f60b hone]
    simp
end NonnegativeLevyPair
end ProbabilityTheory


