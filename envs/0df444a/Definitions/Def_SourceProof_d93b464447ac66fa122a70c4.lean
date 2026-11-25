-- Prove2me | Definitions.Def_SourceProof_d93b464447ac66fa122a70c4
-- name    : SourceProof_d93b464447ac66fa122a70c4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:15:34.75333+00:00
-- url     : https://prove2.me/theorems/8f0b8450-be36-48f5-be7d-d0594c5da0ec
-- title:
--   StochLean source theorem: ProbabilityTheory.HasCagladPaths.indicator

import Definitions.Def_StochLean_Probability_Process_Path_Caglad_F000
import Definitions.Def_SourceProof_50bef199e170152e0882c89e
import Mathlib.Probability.Process.Adapted
import Mathlib.Topology.Algebra.Monoid

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

namespace HasCagladPaths
theorem _root_.Prove2MeSourceProof.h_d93b464447ac66fa122a70c4 [LinearOrder T] [TopologicalSpace T]
    [TopologicalSpace E] (hX : HasCagladPaths X P) (s : Set Ω) :
    HasCagladPaths (fun t ↦ s.indicator (X t)) P := by
  filter_upwards [hX] with ω hω
  by_cases hs : ω ∈ s
  · simpa only [Set.indicator_of_mem hs] using hω
  · simp only [Set.indicator_of_notMem hs]
    exact _root_.Prove2MeSourceProof.h_50bef199e170152e0882c89e continuous_const
end HasCagladPaths

end ProbabilityTheory


