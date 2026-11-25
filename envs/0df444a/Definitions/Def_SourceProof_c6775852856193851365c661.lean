-- Prove2me | Definitions.Def_SourceProof_c6775852856193851365c661
-- name    : SourceProof_c6775852856193851365c661
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:03:45.882837+00:00
-- url     : https://prove2.me/theorems/6c44e079-1dc7-47e5-b645-98127b679133
-- title:
--   StochLean source theorem: ProbabilityTheory.totalVariationProcess_eq_toReal

import Definitions.Def_StochLean_Probability_Process_FiniteVariation_Variation_F000
import Definitions.Def_SourceProof_82b057b5fc05c115d43ef115

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The adapted total-variation process

Variation is first kept in ENNReal, including infinite values. Right continuity,
not continuity, makes actual finite-partition sums converge to it. Real-valued
variation is the canonical Mathlib conversion; its finite-variation interpretation
requires the common-event locally BV hypothesis.
-/

@[expose] public section

open MeasureTheory StochLean Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

theorem _root_.Prove2MeSourceProof.h_c6775852856193851365c661 (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    totalVariationProcess X t ω = (eTotalVariationProcess X t ω).toReal :=
  _root_.Prove2MeSourceProof.h_82b057b5fc05c115d43ef115 _ t
end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

end MeasureTheory


