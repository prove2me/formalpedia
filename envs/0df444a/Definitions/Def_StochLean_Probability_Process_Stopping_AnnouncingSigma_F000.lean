-- Prove2me | Definitions.Def_StochLean_Probability_Process_Stopping_AnnouncingSigma_F000
-- name    : StochLean_Probability_Process_Stopping_AnnouncingSigma_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:02:11.833541+00:00
-- url     : https://prove2.me/theorems/8e5e61f8-2a9d-5d69-9281-4ae1483f9d24
-- title:
--   StochLean: Probability.Process.Stopping.AnnouncingSigma F000

import Definitions.Def_StochLean_Probability_Process_Stopping_Announcing_F000
import Definitions.Def_SourceProof_7c6e147e93638a97c49079d1

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The sigma-field of an announcing sequence

Protter III.6 uses only initial completeness, not right continuity of the
filtration. Both inclusions handle the source almost-sure convergence using
that completeness. The zero-lifetime event is retained explicitly.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory.IsAnnouncingSequence

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
variable {P : Measure Ω} {τ : Ω → WithTop ℝ≥0} {σ : ℕ → Ω → WithTop ℝ≥0}

private theorem measurableSet_congr_of_complete {m : MeasurableSpace Ω}
    (hc : IsCompleteSubMeasurableSpace P m) {A B : Set Ω} (hA : MeasurableSet[m] A)
    (he : ∀ᵐ ω ∂P, ω ∈ A ↔ ω ∈ B) : MeasurableSet[m] B := by
  let N := {ω | ¬ (ω ∈ A ↔ ω ∈ B)}
  have hn : P N = 0 := ae_iff.mp he
  have heq : B = (A \ N) ∪ (B ∩ N) := by
    ext ω
    by_cases hω : ω ∈ A ↔ ω ∈ B <;> simp [N, hω]
  rw [heq]
  exact (hA.diff (hc N hn)).union ((_root_.Prove2MeSourceProof.h_7c6e147e93638a97c49079d1 hc) hn inter_subset_right)
end ProbabilityTheory.IsAnnouncingSequence


