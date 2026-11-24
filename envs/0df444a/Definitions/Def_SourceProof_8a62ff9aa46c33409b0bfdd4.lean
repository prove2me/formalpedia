-- Prove2me | Definitions.Def_SourceProof_8a62ff9aa46c33409b0bfdd4
-- name    : SourceProof_8a62ff9aa46c33409b0bfdd4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:46:04.491968+00:00
-- url     : https://prove2.me/theorems/10742756-7fc1-4fb0-a998-55abd27963c1
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.mul

import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001
import Mathlib.Topology.Algebra.Monoid

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Products of regular paths -/

@[expose] public section

open MeasureTheory Filter

namespace ProbabilityTheory

variable {T Ω E : Type*} [LinearOrder T] [TopologicalSpace T]
  [TopologicalSpace E] [Mul E] [ContinuousMul E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y : T → Ω → E}

namespace IsCadlagPath
theorem _root_.Prove2MeSourceProof.h_8a62ff9aa46c33409b0bfdd4 [OrderBot T] {x y : T → E}
    (hx : IsCadlagPath x) (hy : IsCadlagPath y) : IsCadlagPath (x * y) := by
  refine ⟨fun t ↦ (hx.1 t).mul (hy.1 t), ?_⟩
  intro t ht
  obtain ⟨a, ha⟩ := hx.2 t ht
  obtain ⟨b, hb⟩ := hy.2 t ht
  exact ⟨a * b, ha.mul hb⟩
end IsCadlagPath

end ProbabilityTheory


