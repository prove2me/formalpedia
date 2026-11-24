-- Prove2me | Definitions.Def_SourceProof_d80df7975aaa241a180afe6d
-- name    : SourceProof_d80df7975aaa241a180afe6d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:15:48.921811+00:00
-- url     : https://prove2.me/theorems/dcc3b265-5284-4826-b2cb-887a7e59f72e
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.add

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
theorem _root_.Prove2MeSourceProof.h_d80df7975aaa241a180afe6d [Add E] [ContinuousAdd E] {x y : T → E}
    (hx : IsCadlagPath x) (hy : IsCadlagPath y) : IsCadlagPath (x + y) := by
  refine ⟨fun t ↦ (hx.1 t).add (hy.1 t), ?_⟩
  intro t ht
  obtain ⟨a, ha⟩ := hx.2 t ht
  obtain ⟨b, hb⟩ := hy.2 t ht
  exact ⟨a + b, ha.add hb⟩
end IsCadlagPath

end ProbabilityTheory


