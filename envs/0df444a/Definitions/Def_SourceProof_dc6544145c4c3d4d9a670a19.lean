-- Prove2me | Definitions.Def_SourceProof_dc6544145c4c3d4d9a670a19
-- name    : SourceProof_dc6544145c4c3d4d9a670a19
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:14:08.550068+00:00
-- url     : https://prove2.me/theorems/758ff21c-2166-5fe2-be12-09ef6c11fe27
-- title:
--   StochLean source theorem: MeasureTheory.Adapted.isStoppingTime_hittingAfter_isOpen

import Definitions.Def_StochLean_Probability_Process_Path_RightContinuous_F000
import Definitions.Def_SourceProof_93c9621d1627047440d7fc6f
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

/-! # Open-set hitting times for right-continuous processes

The owner is Mathlib's `hittingAfter`. Open hits strictly before a deterministic time
are detected on a fixed countable dense grid. Right continuity of the filtration then
gives the stopping-time property. At a finite hit the path belongs to the closure of
the target, not necessarily the open target itself.
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

theorem _root_.Prove2MeSourceProof.h_dc6544145c4c3d4d9a670a19 [F.IsRightContinuous]
    (hX : Adapted F X) (hr : ∀ ω, ProbabilityTheory.IsRightContinuousPath (X · ω))
    {s : Set E} (hs : IsOpen s) (a : ℝ≥0) : IsStoppingTime F (hittingAfter X s a) :=
  isStoppingTime_of_measurableSet_lt_of_isRightContinuous
    ((_root_.Prove2MeSourceProof.h_93c9621d1627047440d7fc6f hX) hr hs a)
end Adapted

end MeasureTheory


