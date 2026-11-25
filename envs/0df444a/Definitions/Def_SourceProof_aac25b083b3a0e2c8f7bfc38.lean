-- Prove2me | Definitions.Def_SourceProof_aac25b083b3a0e2c8f7bfc38
-- name    : SourceProof_aac25b083b3a0e2c8f7bfc38
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:31:42.82147+00:00
-- url     : https://prove2.me/theorems/340689e9-4ce5-4617-9443-c1cbe5db7dff
-- title:
--   StochLean source theorem: ProbabilityTheory.denseWindowOscillation_ne_top_of_cadlag

import Definitions.Def_SourceProof_08d1413f21e139fa3b976ce1
import Definitions.Def_SourceProof_22fc639421ecd40a5854230f

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Measurable two-time short-window oscillations

The envelope uses two points of the existing clipped dense grid and an actual
order and strict-width guard. Countability makes it measurable. Two right-side
approximating sequences recover every strict window of a right-continuous
path; doubling a positive width also covers a closed-width window. Cadlag
compact boundedness proves finiteness before the real-valued bridge is used.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

theorem _root_.Prove2MeSourceProof.h_aac25b083b3a0e2c8f7bfc38 {X : ℝ≥0 → Ω → ℝ}
    {ω : Ω} (hX : IsCadlagPath (X · ω)) (T δ : ℝ≥0) :
    denseWindowOscillation X T δ ω ≠ ∞ := by
  obtain ⟨K, _, hK⟩ := (_root_.Prove2MeSourceProof.h_08d1413f21e139fa3b976ce1 hX) T
  apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
  apply _root_.Prove2MeSourceProof.h_22fc639421ecd40a5854230f (K := 2 * K)
  intro r s hrs hsT _
  have hr := hK r ⟨bot_le, hrs.trans hsT⟩
  have hs := hK s ⟨bot_le, hsT⟩
  have htri := norm_sub_le (X s ω) (X r ω)
  linarith only [htri, hr, hs]
end ProbabilityTheory


