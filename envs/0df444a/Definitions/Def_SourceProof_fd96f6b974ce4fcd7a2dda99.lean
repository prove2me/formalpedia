-- Prove2me | Definitions.Def_SourceProof_fd96f6b974ce4fcd7a2dda99
-- name    : SourceProof_fd96f6b974ce4fcd7a2dda99
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:01:48.235611+00:00
-- url     : https://prove2.me/theorems/f2cfc4c9-70a3-4cbc-a47f-8a01dd4e5ad3
-- title:
--   StochLean source theorem: ProbabilityTheory.IsAnnouncingSequence.predictable

import Definitions.Def_StochLean_Probability_Process_Stopping_Announcing_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Announcing sequences and predictable stopping times

The source Protter III.2 convention allows zero and infinite lifetimes. An
announcing sequence is pointwise increasing, strictly below the lifetime on
its positive event, and converges almost surely. In particular, almost-sure
convergence is not silently replaced by everywhere convergence.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

namespace IsAnnouncingSequence

variable {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}
  {τ : Ω → WithTop ℝ≥0} {σ : ℕ → Ω → WithTop ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_fd96f6b974ce4fcd7a2dda99 (h : IsAnnouncingSequence F P τ σ) (hτ : IsStoppingTime F τ) :
    IsPredictableStoppingTime F τ P := ⟨hτ, σ, h⟩
end IsAnnouncingSequence

end ProbabilityTheory


