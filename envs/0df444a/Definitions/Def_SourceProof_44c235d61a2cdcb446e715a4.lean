-- Prove2me | Definitions.Def_SourceProof_44c235d61a2cdcb446e715a4
-- name    : SourceProof_44c235d61a2cdcb446e715a4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:15:17.244175+00:00
-- url     : https://prove2.me/theorems/d252c7a0-6a20-4777-a7a1-8cc06a6ce017
-- title:
--   StochLean source theorem: ProbabilityTheory.HasCadlagPaths.sub

import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001
import Definitions.Def_SourceProof_3eb335b1e032ebc9aabc0087
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

namespace HasCadlagPaths
theorem _root_.Prove2MeSourceProof.h_44c235d61a2cdcb446e715a4 [OrderBot T]
    (hX : HasCadlagPaths X P) (hY : HasCadlagPaths Y P) : HasCadlagPaths (X - Y) P := by
  filter_upwards [hX, hY] with ω hx hy
  exact (_root_.Prove2MeSourceProof.h_3eb335b1e032ebc9aabc0087 hx) hy
end HasCadlagPaths

end ProbabilityTheory


