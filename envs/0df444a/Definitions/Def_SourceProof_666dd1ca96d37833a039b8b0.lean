-- Prove2me | Definitions.Def_SourceProof_666dd1ca96d37833a039b8b0
-- name    : SourceProof_666dd1ca96d37833a039b8b0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:15:19.59785+00:00
-- url     : https://prove2.me/theorems/60708086-c7af-43a9-b2ac-12e11b6ea6f7
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCagladPath.continuous_comp

import Definitions.Def_StochLean_Probability_Process_Path_Caglad_F000
import Mathlib.Topology.Algebra.Monoid

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Continuous operations on cadlag and caglad paths

The process statements intersect finitely many common full-measure events.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace ProbabilityTheory

variable {T Ω E G : Type*} [LinearOrder T] [TopologicalSpace T]
  [TopologicalSpace E] [TopologicalSpace G] {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} {X Y : T → Ω → E}

namespace IsCagladPath
theorem _root_.Prove2MeSourceProof.h_666dd1ca96d37833a039b8b0 {x : T → E} (hx : IsCagladPath x)
    {f : E → G} (hf : Continuous f) : IsCagladPath (f ∘ x) := by
  refine ⟨fun t ↦ hf.continuousAt.comp_continuousWithinAt (hx.1 t), ?_⟩
  intro t
  obtain ⟨y, hy⟩ := hx.2 t
  exact ⟨f y, hf.continuousAt.tendsto.comp hy⟩
end IsCagladPath

variable [OrderBot T]

end ProbabilityTheory


