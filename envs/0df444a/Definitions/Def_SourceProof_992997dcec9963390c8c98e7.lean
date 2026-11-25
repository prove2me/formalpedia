-- Prove2me | Definitions.Def_SourceProof_992997dcec9963390c8c98e7
-- name    : SourceProof_992997dcec9963390c8c98e7
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:30:33.860636+00:00
-- url     : https://prove2.me/theorems/cce0d040-d1c9-4a18-b553-a5f7fea6d882
-- title:
--   StochLean source theorem: ProbabilityTheory.HasCadlagPaths.mul

import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001
import Definitions.Def_SourceProof_8a62ff9aa46c33409b0bfdd4
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

namespace HasCadlagPaths
theorem _root_.Prove2MeSourceProof.h_992997dcec9963390c8c98e7 [OrderBot T]
    (hX : HasCadlagPaths X P) (hY : HasCadlagPaths Y P) : HasCadlagPaths (X * Y) P := by
  filter_upwards [hX, hY] with ω hx hy
  exact (_root_.Prove2MeSourceProof.h_8a62ff9aa46c33409b0bfdd4 hx) hy
end HasCadlagPaths

end ProbabilityTheory


