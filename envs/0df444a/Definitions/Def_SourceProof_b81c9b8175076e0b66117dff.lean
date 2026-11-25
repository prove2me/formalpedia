-- Prove2me | Definitions.Def_SourceProof_b81c9b8175076e0b66117dff
-- name    : SourceProof_b81c9b8175076e0b66117dff
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:41:47.660681+00:00
-- url     : https://prove2.me/theorems/d35dfa70-b7e1-4455-ba56-684978dc91b9
-- title:
--   StochLean source theorem: MeasureTheory.StronglyMeasurable.isStronglyOptional_indicator_stoppingTime_le

import Definitions.Def_SourceProof_0a41c493088d6b6495e37e42
import Definitions.Def_SourceProof_30748602910a669fc7d80008
import Definitions.Def_SourceProof_7270b3ab7a1632573e0ea3ed

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Revealing stopped information at and after its stopping time

This is the source process used to prove Protter I.6. The coefficient is
measurable at the native stopped field, not prematurely at time zero. Its
activation path is cadlag, including zero and infinite lifetimes.
-/

@[expose] public section

open ProbabilityTheory Set
open scoped NNReal

namespace MeasureTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {τ : Ω → WithTop ℝ≥0} [TopologicalSpace E] [Zero E]

namespace StronglyMeasurable
theorem _root_.Prove2MeSourceProof.h_b81c9b8175076e0b66117dff
    (hτ : IsStoppingTime F τ) {Z : Ω → ℝ} (hZ : StronglyMeasurable[hτ.measurableSpace] Z) :
    IsStronglyOptional F (fun t : ℝ≥0 ↦ {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator Z) := by
  have ha : Adapted F (fun t : ℝ≥0 ↦ {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator Z) :=
    fun t ↦ ((fun p2mMethodArg0 => _root_.Prove2MeSourceProof.h_7270b3ab7a1632573e0ea3ed p2mMethodArg0 hZ) hτ t).measurable
  exact (_root_.Prove2MeSourceProof.h_0a41c493088d6b6495e37e42 ha) (_root_.Prove2MeSourceProof.h_30748602910a669fc7d80008 τ Z)
end StronglyMeasurable

end MeasureTheory


