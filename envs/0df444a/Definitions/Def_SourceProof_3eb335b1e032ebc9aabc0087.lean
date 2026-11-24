-- Prove2me | Definitions.Def_SourceProof_3eb335b1e032ebc9aabc0087
-- name    : SourceProof_3eb335b1e032ebc9aabc0087
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:07:23.880386+00:00
-- url     : https://prove2.me/theorems/15f99bdb-dbf8-4598-bf6a-cab6fc2be59a
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.sub

import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Monoid

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Subtraction of cadlag and caglad paths -/

@[expose] public section

open MeasureTheory Filter

namespace ProbabilityTheory

variable {T Ω E : Type*} [LinearOrder T] [TopologicalSpace T]
  [TopologicalSpace E] [Sub E] [ContinuousSub E] {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} {X Y : T → Ω → E}

namespace IsCadlagPath
theorem _root_.Prove2MeSourceProof.h_3eb335b1e032ebc9aabc0087 [OrderBot T] {x y : T → E}
    (hx : IsCadlagPath x) (hy : IsCadlagPath y) : IsCadlagPath (x - y) := by
  refine ⟨fun t ↦ (hx.1 t).sub (hy.1 t), ?_⟩
  intro t ht
  obtain ⟨a, ha⟩ := hx.2 t ht
  obtain ⟨b, hb⟩ := hy.2 t ht
  exact ⟨a - b, ha.sub hb⟩
end IsCadlagPath

end ProbabilityTheory


