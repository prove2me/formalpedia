-- Prove2me | Definitions.Def_SourceProof_0a28bfe8bb403463b49115a5
-- name    : SourceProof_0a28bfe8bb403463b49115a5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T19:16:33.306666+00:00
-- url     : https://prove2.me/theorems/d75bae87-0983-4eed-9da7-1eab68ede409
-- title:
--   StochLean source theorem: ProbabilityTheory.restrictedStoppingTime_of_mem

import Definitions.Def_StochLean_Probability_Process_Stopping_Restriction_F000

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

theorem _root_.Prove2MeSourceProof.h_0a28bfe8bb403463b49115a5 (τ : Ω → WithTop ℝ≥0) {A : Set Ω}
    {ω : Ω} (hω : ω ∈ A) : restrictedStoppingTime τ A ω = τ ω := by
  simp only [ProbabilityTheory.restrictedStoppingTime, if_pos hω]
end ProbabilityTheory

namespace MeasureTheory.IsStoppingTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {τ : Ω → WithTop ℝ≥0}

end MeasureTheory.IsStoppingTime


