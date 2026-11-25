-- Prove2me | Definitions.Def_SourceProof_b1ffca32a537cf74dad808cc
-- name    : SourceProof_b1ffca32a537cf74dad808cc
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T07:59:47.029801+00:00
-- url     : https://prove2.me/theorems/525ead0a-4c32-58ea-80b1-9685e17090e8
-- title:
--   StochLean source theorem: ProbabilityTheory.IsAnnouncingSequence.ae_eq_zero_of_zero

import Definitions.Def_StochLean_Probability_Process_Stopping_Announcing_F000
import Definitions.Def_SourceProof_22ce361e41cf5fbc2e0e9262

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

theorem _root_.Prove2MeSourceProof.h_b1ffca32a537cf74dad808cc (h : IsAnnouncingSequence F P τ σ) :
    ∀ᵐ ω ∂P, τ ω = 0 → ∀ n, σ n ω = 0 := by
  filter_upwards [(_root_.Prove2MeSourceProof.h_22ce361e41cf5fbc2e0e9262 h)] with ω hω ht n
  exact le_antisymm (ht ▸ hω n) bot_le
end IsAnnouncingSequence

end ProbabilityTheory


