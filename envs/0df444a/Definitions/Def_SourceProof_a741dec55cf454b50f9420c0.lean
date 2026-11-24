-- Prove2me | Definitions.Def_SourceProof_a741dec55cf454b50f9420c0
-- name    : SourceProof_a741dec55cf454b50f9420c0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:14:19.001155+00:00
-- url     : https://prove2.me/theorems/3b350cfe-1980-46ad-862c-5751cac84973
-- title:
--   StochLean source theorem: ProbabilityTheory.StoppingTimePartition.splitAt_refines

import Definitions.Def_StochLean_Probability_Process_Partition_Refinement_F000
import Definitions.Def_StochLean_Probability_Process_Partition_Refinement_F001
import Definitions.Def_SourceProof_136c18157609b41bd9beb303
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

theorem _root_.Prove2MeSourceProof.h_a741dec55cf454b50f9420c0 (π : StoppingTimePartition F) (τ : FiniteStoppingTime F) :
    (π.splitAt τ).Refines π := by
  intro ω i
  by_cases hi : π.point i ω ≤ τ ω
  · refine ⟨i.castAdd (π.size + 1), ?_⟩
    change Fin.append (α := ProbabilityTheory.FiniteStoppingTime F) _ _ (i.castAdd (π.size + 1)) ω = _
    simp only [Fin.append_left, _root_.Prove2MeSourceProof.h_136c18157609b41bd9beb303, min_eq_left hi]
  · refine ⟨i.natAdd (π.size + 1), ?_⟩
    change Fin.append (α := ProbabilityTheory.FiniteStoppingTime F) _ _ (i.natAdd (π.size + 1)) ω = _
    simp only [Fin.append_right, _root_.Prove2MeSourceProof.h_cf64c9a6c7f0a6a27abe12f0, max_eq_left (le_of_not_ge hi)]
end ProbabilityTheory.StoppingTimePartition


