-- Prove2me | Definitions.Def_SourceProof_511a81ac634ab9501a2b62a2
-- name    : SourceProof_511a81ac634ab9501a2b62a2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:27:00.166676+00:00
-- url     : https://prove2.me/theorems/2ca22373-4c59-4334-a6a6-fd03148476b1
-- title:
--   StochLean source theorem: ProbabilityTheory.IsAnnouncingSequence.cap_target

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
theorem _root_.Prove2MeSourceProof.h_511a81ac634ab9501a2b62a2 (h : IsAnnouncingSequence F P τ σ)
    (hτ : IsStoppingTime F τ) :
    IsAnnouncingSequence F P τ (fun n ω ↦ min (σ n ω) (τ ω)) := by
  refine ⟨fun n ↦ (h.isStoppingTime n).min hτ,
    fun ω i j hij ↦ min_le_min (h.monotone ω hij) le_rfl,
    fun n ω ht ↦ (min_le_left _ _).trans_lt (h.strict n ω ht), ?_⟩
  filter_upwards [h.tendsto] with ω hω
  simpa only [min_self] using hω.min (tendsto_const_nhds (x := τ ω))
end IsAnnouncingSequence

end ProbabilityTheory


