-- Prove2me | Definitions.Def_SourceProof_9917d1848d3898f6c6898753
-- name    : SourceProof_9917d1848d3898f6c6898753
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:31:39.319077+00:00
-- url     : https://prove2.me/theorems/4884b188-93ac-476c-a8e3-3eead389857c
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCagladPath.mul

import Definitions.Def_StochLean_Probability_Process_Path_Caglad_F000
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

namespace IsCagladPath
theorem _root_.Prove2MeSourceProof.h_9917d1848d3898f6c6898753 {x y : T → E} (hx : IsCagladPath x) (hy : IsCagladPath y) :
    IsCagladPath (x * y) := by
  refine ⟨fun t ↦ (hx.1 t).mul (hy.1 t), ?_⟩
  intro t
  obtain ⟨a, ha⟩ := hx.2 t
  obtain ⟨b, hb⟩ := hy.2 t
  exact ⟨a * b, ha.mul hb⟩
end IsCagladPath

end ProbabilityTheory


