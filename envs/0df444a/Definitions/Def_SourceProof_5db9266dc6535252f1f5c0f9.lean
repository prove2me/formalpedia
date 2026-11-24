-- Prove2me | Definitions.Def_SourceProof_5db9266dc6535252f1f5c0f9
-- name    : SourceProof_5db9266dc6535252f1f5c0f9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:16:13.801803+00:00
-- url     : https://prove2.me/theorems/66c49d6d-d270-40f6-bd26-886f2a56ed90
-- title:
--   StochLean source theorem: ProbabilityTheory.StoppingTimePartition.splitAt_contains

import Definitions.Def_StochLean_Probability_Process_Partition_Refinement_F001
import Definitions.Def_SourceProof_cf64c9a6c7f0a6a27abe12f0

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Common refinements of finite stopping-time partitions

Refinement is pathwise endpoint inclusion, so random coincidences and repeated endpoints
are allowed. Splitting at one finite stopping time uses only minima and maxima of stopping
times. The witness construction is deliberately nonminimal; it requires no measurable sorting
choice and does not impose boundedness or additional conditions on the filtration.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory.StoppingTimePartition

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

theorem _root_.Prove2MeSourceProof.h_5db9266dc6535252f1f5c0f9 (π : StoppingTimePartition F) (τ : FiniteStoppingTime F) (ω : Ω) :
    ∃ j, (π.splitAt τ).point j ω = τ ω := by
  refine ⟨(0 : Fin (π.size + 1)).natAdd (π.size + 1), ?_⟩
  change Fin.append (α := ProbabilityTheory.FiniteStoppingTime F) _ _
    ((0 : Fin (π.size + 1)).natAdd (π.size + 1)) ω = _
  simp only [Fin.append_right, _root_.Prove2MeSourceProof.h_cf64c9a6c7f0a6a27abe12f0, π.first_eq_zero]
  exact max_eq_right bot_le
end ProbabilityTheory.StoppingTimePartition


