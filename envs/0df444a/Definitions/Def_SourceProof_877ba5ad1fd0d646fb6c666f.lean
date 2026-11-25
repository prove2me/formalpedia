-- Prove2me | Definitions.Def_SourceProof_877ba5ad1fd0d646fb6c666f
-- name    : SourceProof_877ba5ad1fd0d646fb6c666f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:30:38.744692+00:00
-- url     : https://prove2.me/theorems/523d8db2-b2fb-438f-80eb-858ab09e1374
-- title:
--   StochLean source theorem: MeasureTheory.Adapted.isStoppingTime_hittingAfter_isOpen_of_leftContinuous

import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F000
import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001
import Definitions.Def_SourceProof_7fb17008e293021cfd3139b8
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Order.Compact

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Open-target hitting and exit bounds for left-continuous paths

Dense detection must include the initial time separately: a left-continuous path
on a half-line can have an isolated initial value. At a positive first exit the
norm remains bounded from above, unlike a cadlag first exit with jump overshoot.
-/

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open scoped NNReal Topology

namespace ProbabilityTheory

variable {E : Type*} [TopologicalSpace E]

end ProbabilityTheory

namespace MeasureTheory

variable {Ω E : Type*} [TopologicalSpace E] {X : ℝ≥0 → Ω → E}

variable {mΩ : MeasurableSpace Ω} [MeasurableSpace E] [OpensMeasurableSpace E]
  {F : Filtration ℝ≥0 mΩ}

namespace Adapted
theorem _root_.Prove2MeSourceProof.h_877ba5ad1fd0d646fb6c666f [F.IsRightContinuous]
    (hX : Adapted F X) (hl : ∀ ω, ProbabilityTheory.IsLeftContinuousPath (X · ω))
    {s : Set E} (hs : IsOpen s) (a : ℝ≥0) : IsStoppingTime F (hittingAfter X s a) :=
  isStoppingTime_of_measurableSet_lt_of_isRightContinuous
    ((_root_.Prove2MeSourceProof.h_7fb17008e293021cfd3139b8 hX) hl hs a)
end Adapted

end MeasureTheory

namespace MeasureTheory

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ}

end MeasureTheory


