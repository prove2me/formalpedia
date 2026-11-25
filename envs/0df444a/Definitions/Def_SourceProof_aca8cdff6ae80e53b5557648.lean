-- Prove2me | Definitions.Def_SourceProof_aca8cdff6ae80e53b5557648
-- name    : SourceProof_aca8cdff6ae80e53b5557648
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:03:35.395002+00:00
-- url     : https://prove2.me/theorems/1b2f1b2e-a8bc-4b9c-b353-46a4871449eb
-- title:
--   StochLean source theorem: ProbabilityTheory.Indistinguishable.eTotalVariationProcess

import Definitions.Def_StochLean_Probability_Process_FiniteVariation_Variation_F000

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

namespace Indistinguishable
theorem _root_.Prove2MeSourceProof.h_aca8cdff6ae80e53b5557648 {X Y : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
    (h : Indistinguishable X Y P) :
    Indistinguishable (eTotalVariationProcess X) (eTotalVariationProcess Y) P := by
  filter_upwards [h] with ω hω t
  simp only [ProbabilityTheory.eTotalVariationProcess, hω]
end Indistinguishable

end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

end MeasureTheory


