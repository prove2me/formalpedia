-- Prove2me | Definitions.Def_SourceProof_53bca36d7403deaa0689f5ec
-- name    : SourceProof_53bca36d7403deaa0689f5ec
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:25:58.378138+00:00
-- url     : https://prove2.me/theorems/5e1c5c2b-ae64-447e-845b-23a1fbbeb0cb
-- title:
--   StochLean source theorem: ProbabilityTheory.HasCagladPaths.hasCadlagPaths_rightLimitProcess

import Definitions.Def_StochLean_Probability_Process_Path_RightLimit_F000
import Definitions.Def_SourceProof_fff880ea6c6a7bb34bef28fb

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The right-limit process of a caglad input

Mathlib owns the strict-right-limit selector. Its limit and reconstruction identities
are proved on the caglad path domain. In general `H_(0+)` differs from `H_0`, so this
transformation is not a modification and does not normalize or overwrite the source initial value.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X Y : ℝ≥0 → Ω → ℝ}

namespace HasCagladPaths
theorem _root_.Prove2MeSourceProof.h_53bca36d7403deaa0689f5ec (hX : HasCagladPaths X P) :
    HasCadlagPaths (rightLimitProcess X) P :=
  hX.mono fun _ hω ↦ (_root_.Prove2MeSourceProof.h_fff880ea6c6a7bb34bef28fb hω)
end HasCagladPaths

end ProbabilityTheory


