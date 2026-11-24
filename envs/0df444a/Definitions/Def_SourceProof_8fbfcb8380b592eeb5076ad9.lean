-- Prove2me | Definitions.Def_SourceProof_8fbfcb8380b592eeb5076ad9
-- name    : SourceProof_8fbfcb8380b592eeb5076ad9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:46:06.073718+00:00
-- url     : https://prove2.me/theorems/3908a7f7-46d5-4ba6-a323-81a41514ef8f
-- title:
--   StochLean source theorem: ProbabilityTheory.IsAnnouncingSequence.min

import Definitions.Def_StochLean_Probability_Process_Stopping_Announcing_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Stability of announcing sequences

Capping each announcing term by its target preserves the source relation and
makes domination pointwise, even at exceptional zero-time samples. Finite
minima and maxima of predictable times are predictable. No claim about
decreasing limits or arbitrary stopped-event restrictions is made.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}
  {τ ρ : Ω → WithTop ℝ≥0} {σ π : ℕ → Ω → WithTop ℝ≥0}

namespace IsAnnouncingSequence
theorem _root_.Prove2MeSourceProof.h_8fbfcb8380b592eeb5076ad9 (h : IsAnnouncingSequence F P τ σ)
    (h' : IsAnnouncingSequence F P ρ π) :
    IsAnnouncingSequence F P (fun ω ↦ min (τ ω) (ρ ω))
      (fun n ω ↦ min (σ n ω) (π n ω)) := by
  refine ⟨fun n ↦ (h.isStoppingTime n).min (h'.isStoppingTime n),
    fun ω i j hij ↦ min_le_min (h.monotone ω hij) (h'.monotone ω hij),
    fun n ω ht ↦ ?_, ?_⟩
  · exact min_lt_min (h.strict n ω (lt_min_iff.mp ht).1)
      (h'.strict n ω (lt_min_iff.mp ht).2)
  · filter_upwards [h.tendsto, h'.tendsto] with ω hω hω'
    exact hω.min hω'
end IsAnnouncingSequence

end ProbabilityTheory


