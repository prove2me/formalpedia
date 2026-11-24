-- Prove2me | Definitions.Def_SourceProof_76f262a7dcf49af74032efc9
-- name    : SourceProof_76f262a7dcf49af74032efc9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T19:17:23.438869+00:00
-- url     : https://prove2.me/theorems/74350877-3456-4e93-a7c1-a3277f856f09
-- title:
--   StochLean source theorem: ProbabilityTheory.stoppingTimeGraph_restricted

import Definitions.Def_StochLean_Probability_Process_Stopping_Restriction_F000
import Definitions.Def_SourceProof_f73bbc630aabc3c5fda26318

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Restricting a stopping time to an event

Protter III.2's `T_A` is `T` on `A` and infinity off `A`. Stopping requires
`A ∈ F_T`, not initial measurability. The graph restriction is an exact
finite-time identity, including the zero-time section.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*}

theorem _root_.Prove2MeSourceProof.h_76f262a7dcf49af74032efc9 (τ : Ω → WithTop ℝ≥0) (A : Set Ω) :
    stoppingTimeGraph (restrictedStoppingTime τ A) = stoppingTimeGraph τ ∩ (univ ×ˢ A) := by
  ext ⟨t, ω⟩
  by_cases hω : ω ∈ A
  · simp [ProbabilityTheory.restrictedStoppingTime, hω]
  · simp only [_root_.Prove2MeSourceProof.h_f73bbc630aabc3c5fda26318, ProbabilityTheory.restrictedStoppingTime, hω, ↓reduceIte,
      ENNReal.some_eq_coe', mem_inter_iff, mem_prod, mem_univ, and_false, iff_false]
    exact WithTop.top_ne_coe
end ProbabilityTheory

namespace MeasureTheory.IsStoppingTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {τ : Ω → WithTop ℝ≥0}

end MeasureTheory.IsStoppingTime


