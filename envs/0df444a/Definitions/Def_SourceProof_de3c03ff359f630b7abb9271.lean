-- Prove2me | Definitions.Def_SourceProof_de3c03ff359f630b7abb9271
-- name    : SourceProof_de3c03ff359f630b7abb9271
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:57:11.179954+00:00
-- url     : https://prove2.me/theorems/a71235ec-c722-43a0-b9d3-2468062fd4db
-- title:
--   StochLean source theorem: ProbabilityTheory.Indistinguishable.indicator

import Definitions.Def_StochLean_Probability_Process_Equivalence_F000
import Mathlib.Probability.Process.Adapted
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Bases
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.LeftRight

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Initial-event masks of adapted processes

An initial measurable event preserves adaptedness. Path properties and
indistinguishability need no measurability assumption on the masking event.
-/

@[expose] public section

open MeasureTheory Set

namespace MeasureTheory

end MeasureTheory

namespace ProbabilityTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [Zero E]
  {X Y : T → Ω → E}

namespace Indistinguishable
theorem _root_.Prove2MeSourceProof.h_de3c03ff359f630b7abb9271 (hXY : Indistinguishable X Y P) (s : Set Ω) :
    Indistinguishable (fun t ↦ s.indicator (X t)) (fun t ↦ s.indicator (Y t)) P := by
  filter_upwards [hXY] with ω hω t
  by_cases hs : ω ∈ s
  · simpa only [Set.indicator_of_mem hs] using hω t
  · simp only [Set.indicator_of_notMem hs]
end Indistinguishable

end ProbabilityTheory


