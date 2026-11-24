-- Prove2me | Definitions.Def_SourceProof_923c456011a9fa9af1f50ea3
-- name    : SourceProof_923c456011a9fa9af1f50ea3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:46:07.807073+00:00
-- url     : https://prove2.me/theorems/938ad735-32bf-4722-b5cd-831a9664b78b
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCagladPath.sub

import Definitions.Def_StochLean_Probability_Process_Path_Caglad_F000
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

namespace IsCagladPath
theorem _root_.Prove2MeSourceProof.h_923c456011a9fa9af1f50ea3 {x y : T → E} (hx : IsCagladPath x) (hy : IsCagladPath y) :
    IsCagladPath (x - y) := by
  refine ⟨fun t ↦ (hx.1 t).sub (hy.1 t), ?_⟩
  intro t
  obtain ⟨a, ha⟩ := hx.2 t
  obtain ⟨b, hb⟩ := hy.2 t
  exact ⟨a - b, ha.sub hb⟩
end IsCagladPath

end ProbabilityTheory


