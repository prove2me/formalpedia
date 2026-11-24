-- Prove2me | Definitions.Def_SourceProof_2788bc818189572242b6cda6
-- name    : SourceProof_2788bc818189572242b6cda6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:15:40.347693+00:00
-- url     : https://prove2.me/theorems/6f4a7f2b-3de2-417a-85d8-2a681a0c0b29
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCagladPath.add

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
theorem _root_.Prove2MeSourceProof.h_2788bc818189572242b6cda6 [Add E] [ContinuousAdd E] {x y : T → E}
    (hx : IsCagladPath x) (hy : IsCagladPath y) : IsCagladPath (x + y) := by
  refine ⟨fun t ↦ (hx.1 t).add (hy.1 t), ?_⟩
  intro t
  obtain ⟨a, ha⟩ := hx.2 t
  obtain ⟨b, hb⟩ := hy.2 t
  exact ⟨a + b, ha.add hb⟩
end IsCagladPath

variable [OrderBot T]

end ProbabilityTheory


