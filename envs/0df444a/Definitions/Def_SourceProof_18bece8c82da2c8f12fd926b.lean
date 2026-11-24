-- Prove2me | Definitions.Def_SourceProof_18bece8c82da2c8f12fd926b
-- name    : SourceProof_18bece8c82da2c8f12fd926b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:20:19.559288+00:00
-- url     : https://prove2.me/theorems/399364b1-080c-48a2-aee9-ea6a5e6e10ca
-- title:
--   StochLean source theorem: ProbabilityTheory.StoppingTimePartition.exists_refinement_containing

import Definitions.Def_StochLean_Probability_Process_Partition_Refinement_F001
import Definitions.Def_SourceProof_5db9266dc6535252f1f5c0f9
import Definitions.Def_SourceProof_a741dec55cf454b50f9420c0
import Definitions.Def_SourceProof_aa8bccb9399de6b4088d30d9
import Definitions.Def_SourceProof_d23ff5479f0301df9bb337e0

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

theorem _root_.Prove2MeSourceProof.h_18bece8c82da2c8f12fd926b (π : StoppingTimePartition F)
    (s : Finset (FiniteStoppingTime F)) :
    ∃ ρ : StoppingTimePartition F, ρ.Refines π ∧
      ∀ τ ∈ s, ∀ ω, ∃ j, ρ.point j ω = τ ω := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨π, _root_.Prove2MeSourceProof.h_d23ff5479f0301df9bb337e0 π, by simp⟩
  | @insert τ s _ ih =>
    obtain ⟨ρ, hρ, hs⟩ := ih
    refine ⟨ρ.splitAt τ, (_root_.Prove2MeSourceProof.h_aa8bccb9399de6b4088d30d9 ((_root_.Prove2MeSourceProof.h_a741dec55cf454b50f9420c0 ρ) τ)) hρ, ?_⟩
    intro σ hσ ω
    rcases Finset.mem_insert.mp hσ with hστ | hσ
    · subst σ
      exact (_root_.Prove2MeSourceProof.h_5db9266dc6535252f1f5c0f9 ρ) τ ω
    · obtain ⟨i, hi⟩ := hs σ hσ ω
      obtain ⟨j, hj⟩ := (_root_.Prove2MeSourceProof.h_a741dec55cf454b50f9420c0 ρ) τ ω i
      exact ⟨j, hj.trans hi⟩
end ProbabilityTheory.StoppingTimePartition


