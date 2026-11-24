-- Prove2me | Definitions.Def_SourceProof_c1f91df6c360f9f8d687e8dd
-- name    : SourceProof_c1f91df6c360f9f8d687e8dd
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:58:23.588739+00:00
-- url     : https://prove2.me/theorems/c8a8b02b-b2bf-4006-8e70-8dfaf1da40ab
-- title:
--   StochLean source theorem: ProbabilityTheory.StoppingTimePartition.Refines.terminal_le

import Definitions.Def_StochLean_Probability_Process_Partition_Refinement_F000

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

namespace Refines
theorem _root_.Prove2MeSourceProof.h_c1f91df6c360f9f8d687e8dd {ρ π : StoppingTimePartition F} (h : ρ.Refines π) (ω : Ω) :
    π.terminal ω ≤ ρ.terminal ω := by
  obtain ⟨j, hj⟩ := h ω (Fin.last π.size)
  exact hj ▸ ρ.monotone_point ω (Fin.le_last j)
end Refines

end ProbabilityTheory.StoppingTimePartition


