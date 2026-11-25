-- Prove2me | Definitions.Def_SourceProof_51cff7b6f18c4ccd4d6713f8
-- name    : SourceProof_51cff7b6f18c4ccd4d6713f8
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:47:52.399713+00:00
-- url     : https://prove2.me/theorems/49532a30-71c7-4806-85cf-073708e1079c
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.norm_discreteCoefficient_le

import Definitions.Def_SourceProof_e9467b3633732e30e9243cd8

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The elementary integral as an existing discrete predictable integral

The coefficient at index `n + 1` is measurable at the original left stopping endpoint, even
when the integrator is stopped at a deterministic horizon. No deterministic bound on the
partition endpoints, or change to their sigma-fields, is imposed.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal ENNReal BigOperators

namespace ProbabilityTheory.SimplePredictableRep

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

theorem _root_.Prove2MeSourceProof.h_51cff7b6f18c4ccd4d6713f8 (H : SimplePredictableRep F) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ i ω, ‖H.coefficient i ω‖ ≤ C) (n : ℕ) (ω : Ω) :
    ‖H.discreteCoefficient n ω‖ ≤ C := by
  cases n with
  | zero => simpa only [_root_.Prove2MeSourceProof.h_e9467b3633732e30e9243cd8, Pi.zero_apply, norm_zero] using hC
  | succ n =>
    by_cases hn : n < H.partition.size
    · simpa only [ProbabilityTheory.SimplePredictableRep.discreteCoefficient, dif_pos hn] using hb ⟨n, hn⟩ ω
    · simpa only [ProbabilityTheory.SimplePredictableRep.discreteCoefficient, dif_neg hn, Pi.zero_apply, norm_zero] using hC
end ProbabilityTheory.SimplePredictableRep


