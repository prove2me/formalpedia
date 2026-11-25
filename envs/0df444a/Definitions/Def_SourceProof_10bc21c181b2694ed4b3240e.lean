-- Prove2me | Definitions.Def_SourceProof_10bc21c181b2694ed4b3240e
-- name    : SourceProof_10bc21c181b2694ed4b3240e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:30:34.39377+00:00
-- url     : https://prove2.me/theorems/6e26ce86-9fc2-4258-913f-a87a3730ee29
-- title:
--   StochLean source theorem: ProbabilityTheory.NonnegativeLevyPair.atom_zero

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_NonnegativeLevyKhintchine_F000

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

theorem _root_.Prove2MeSourceProof.h_10bc21c181b2694ed4b3240e (η : NonnegativeLevyPair) : η.jumpMeasure {0} = 0 := by
  have hs := η.supportedPositive
  rw [ae_iff] at hs
  apply measure_mono_null (s := ({0} : Set ℝ)) (t := {x | ¬ 0 < x})
  · intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    simp
  · exact hs
end NonnegativeLevyPair
end ProbabilityTheory


