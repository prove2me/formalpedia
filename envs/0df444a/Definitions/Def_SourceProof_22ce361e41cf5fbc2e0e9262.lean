-- Prove2me | Definitions.Def_SourceProof_22ce361e41cf5fbc2e0e9262
-- name    : SourceProof_22ce361e41cf5fbc2e0e9262
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:21:15.467581+00:00
-- url     : https://prove2.me/theorems/95da1184-7638-4545-8acb-efda70944ae9
-- title:
--   StochLean source theorem: ProbabilityTheory.IsAnnouncingSequence.ae_le

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

theorem _root_.Prove2MeSourceProof.h_22ce361e41cf5fbc2e0e9262 (h : IsAnnouncingSequence F P τ σ) :
    ∀ᵐ ω ∂P, ∀ n, σ n ω ≤ τ ω := by
  filter_upwards [h.tendsto] with ω hω n
  exact (h.monotone ω).ge_of_tendsto hω n
end IsAnnouncingSequence

end ProbabilityTheory


