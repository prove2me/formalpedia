-- Prove2me | Definitions.Def_SourceProof_523d7cde826eec51d63a0e17
-- name    : SourceProof_523d7cde826eec51d63a0e17
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:44:35.882713+00:00
-- url     : https://prove2.me/theorems/12ac7c15-49b5-4d2e-a425-eb86fea326c7
-- title:
--   StochLean source theorem: ProbabilityTheory.HasCagladPaths.mul

import Definitions.Def_StochLean_Probability_Process_Path_Caglad_F000
import Definitions.Def_SourceProof_9917d1848d3898f6c6898753
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

namespace HasCagladPaths
theorem _root_.Prove2MeSourceProof.h_523d7cde826eec51d63a0e17 (hX : HasCagladPaths X P) (hY : HasCagladPaths Y P) :
    HasCagladPaths (X * Y) P := by
  filter_upwards [hX, hY] with ω hx hy
  exact (_root_.Prove2MeSourceProof.h_9917d1848d3898f6c6898753 hx) hy
end HasCagladPaths

end ProbabilityTheory


