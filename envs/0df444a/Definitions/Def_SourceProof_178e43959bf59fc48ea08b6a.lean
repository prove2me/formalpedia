-- Prove2me | Definitions.Def_SourceProof_178e43959bf59fc48ea08b6a
-- name    : SourceProof_178e43959bf59fc48ea08b6a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:34:24.34264+00:00
-- url     : https://prove2.me/theorems/77bd5c5c-4282-4f46-ba5f-8e47ee3e079f
-- title:
--   StochLean source theorem: ProbabilityTheory.NonnegativeLevyPair.nonnegative_restriction_integral_le

import Definitions.Def_SourceProof_ec94ee002a1dbd27a305ed82

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

theorem _root_.Prove2MeSourceProof.h_178e43959bf59fc48ea08b6a (η : NonnegativeLevyPair) (n : ℕ) :
    (∫ x, levyTruncation x ∂η.jumpMeasure.restrict (IsLevyMeasure.spanningLevel n)) ≤
      ∫ x, levyTruncation x ∂η.jumpMeasure := by
  apply integral_mono_measure Measure.restrict_le_self
  · filter_upwards [η.supportedPositive] with x hx
    simp only [ProbabilityTheory.levyTruncation]
    split <;> positivity
  · exact (_root_.Prove2MeSourceProof.h_ec94ee002a1dbd27a305ed82 η)
end NonnegativeLevyPair
end ProbabilityTheory


