-- Prove2me | Definitions.Def_SourceProof_7a200839927b2232bfb83618
-- name    : SourceProof_7a200839927b2232bfb83618
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T19:17:17.891095+00:00
-- url     : https://prove2.me/theorems/4e45e234-0a45-4bbd-9922-fc07541a4bda
-- title:
--   StochLean source theorem: ProbabilityTheory.restrictedStoppingTime_of_notMem

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

theorem _root_.Prove2MeSourceProof.h_7a200839927b2232bfb83618 (τ : Ω → WithTop ℝ≥0) {A : Set Ω}
    {ω : Ω} (hω : ω ∉ A) : restrictedStoppingTime τ A ω = ⊤ := by
  simp only [ProbabilityTheory.restrictedStoppingTime, if_neg hω]
end ProbabilityTheory

namespace MeasureTheory.IsStoppingTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {τ : Ω → WithTop ℝ≥0}

end MeasureTheory.IsStoppingTime


