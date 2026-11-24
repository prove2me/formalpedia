-- Prove2me | Definitions.Def_SourceProof_96331e337c0a0b8560074745
-- name    : SourceProof_96331e337c0a0b8560074745
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T16:06:48.62095+00:00
-- url     : https://prove2.me/theorems/3e6502f8-029c-47bd-8c68-da3e86bc2d2b
-- title:
--   StochLean source theorem: MeasureTheory.Adapted.indicator_initial

import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.FiniteDimensionalLaws
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

namespace Adapted
theorem _root_.Prove2MeSourceProof.h_96331e337c0a0b8560074745 {T Ω E : Type*} [Preorder T] [OrderBot T]
    {mΩ : MeasurableSpace Ω} [MeasurableSpace E] [Zero E]
    {F : Filtration T mΩ} {X : T → Ω → E} (hX : Adapted F X)
    {s : Set Ω} (hs : MeasurableSet[F ⊥] s) :
    Adapted F (fun t ↦ s.indicator (X t)) :=
  fun t ↦ (hX t).indicator (F.mono bot_le s hs)
end Adapted

end MeasureTheory

namespace ProbabilityTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [Zero E]
  {X Y : T → Ω → E}

end ProbabilityTheory


