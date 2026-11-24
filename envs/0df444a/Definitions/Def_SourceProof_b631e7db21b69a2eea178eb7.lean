-- Prove2me | Definitions.Def_SourceProof_b631e7db21b69a2eea178eb7
-- name    : SourceProof_b631e7db21b69a2eea178eb7
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:45:02.041826+00:00
-- url     : https://prove2.me/theorems/e2189a35-1341-41e4-b601-bdc3bd6279bf
-- title:
--   StochLean source theorem: ProbabilityTheory.IsPredictableStoppingTime.exists_announcing_le

import Definitions.Def_SourceProof_511a81ac634ab9501a2b62a2

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

namespace IsPredictableStoppingTime
theorem _root_.Prove2MeSourceProof.h_b631e7db21b69a2eea178eb7
    (h : IsPredictableStoppingTime F τ P) :
    ∃ σ : ℕ → Ω → WithTop ℝ≥0, IsAnnouncingSequence F P τ σ ∧ ∀ n ω, σ n ω ≤ τ ω := by
  obtain ⟨σ, hs⟩ := h.2
  exact ⟨fun n ω ↦ min (σ n ω) (τ ω), (_root_.Prove2MeSourceProof.h_511a81ac634ab9501a2b62a2 hs) h.1, fun _ _ ↦ min_le_right _ _⟩
end IsPredictableStoppingTime

end ProbabilityTheory


