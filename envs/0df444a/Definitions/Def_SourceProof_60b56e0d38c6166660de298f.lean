-- Prove2me | Definitions.Def_SourceProof_60b56e0d38c6166660de298f
-- name    : SourceProof_60b56e0d38c6166660de298f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:15:28.78307+00:00
-- url     : https://prove2.me/theorems/0083aea2-eec6-40d7-a812-57b722941c23
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.continuous_comp

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

variable [OrderBot T]

namespace IsCadlagPath
theorem _root_.Prove2MeSourceProof.h_60b56e0d38c6166660de298f {x : T → E} (hx : IsCadlagPath x)
    {f : E → G} (hf : Continuous f) : IsCadlagPath (f ∘ x) := by
  refine ⟨fun t ↦ hf.continuousAt.comp_continuousWithinAt (hx.1 t), ?_⟩
  intro t ht
  obtain ⟨y, hy⟩ := hx.2 t ht
  exact ⟨f y, hf.continuousAt.tendsto.comp hy⟩
end IsCadlagPath

end ProbabilityTheory


