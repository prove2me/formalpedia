-- Prove2me | Definitions.Def_SourceProof_15e5de2b6483fa8bd27008ef
-- name    : SourceProof_15e5de2b6483fa8bd27008ef
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:25:46.20187+00:00
-- url     : https://prove2.me/theorems/651ba420-540f-4e20-84ec-b684666b134b
-- title:
--   StochLean source theorem: ProbabilityTheory.StoppingTimePartition.exists_common_refinement

import Definitions.Def_StochLean_Probability_Process_Partition_Refinement_F000
import Definitions.Def_SourceProof_18bece8c82da2c8f12fd926b

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


theorem _root_.Prove2MeSourceProof.h_15e5de2b6483fa8bd27008ef (π κ : StoppingTimePartition F) :
    ∃ ρ : StoppingTimePartition F, ρ.Refines π ∧ ρ.Refines κ := by
  classical
  obtain ⟨ρ, hρ, hs⟩ := (_root_.Prove2MeSourceProof.h_18bece8c82da2c8f12fd926b π) (Finset.univ.image κ.point)
  exact ⟨ρ, hρ, fun ω i ↦ hs _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)) ω⟩
end ProbabilityTheory.StoppingTimePartition


