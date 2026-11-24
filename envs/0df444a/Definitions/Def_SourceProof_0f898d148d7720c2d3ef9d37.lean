-- Prove2me | Definitions.Def_SourceProof_0f898d148d7720c2d3ef9d37
-- name    : SourceProof_0f898d148d7720c2d3ef9d37
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:47:44.754786+00:00
-- url     : https://prove2.me/theorems/c289e904-2a3b-4aa6-863d-b82fcfddb674
-- title:
--   StochLean source theorem: ProbabilityTheory.le_restrictedStoppingTime

import Definitions.Def_StochLean_Probability_Process_Stopping_Restriction_F000
import Definitions.Def_SourceProof_0a28bfe8bb403463b49115a5
import Definitions.Def_SourceProof_7a200839927b2232bfb83618

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

theorem _root_.Prove2MeSourceProof.h_0f898d148d7720c2d3ef9d37 (τ : Ω → WithTop ℝ≥0) (A : Set Ω) :
    τ ≤ restrictedStoppingTime τ A := by
  intro ω
  by_cases hω : ω ∈ A
  · rw [_root_.Prove2MeSourceProof.h_0a28bfe8bb403463b49115a5 τ hω]
  · rw [_root_.Prove2MeSourceProof.h_7a200839927b2232bfb83618 τ hω]
    exact le_top
end ProbabilityTheory

namespace MeasureTheory.IsStoppingTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {τ : Ω → WithTop ℝ≥0}

end MeasureTheory.IsStoppingTime


