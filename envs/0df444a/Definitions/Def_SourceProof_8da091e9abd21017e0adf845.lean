-- Prove2me | Definitions.Def_SourceProof_8da091e9abd21017e0adf845
-- name    : SourceProof_8da091e9abd21017e0adf845
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:14:00.597819+00:00
-- url     : https://prove2.me/theorems/6db9c2d0-b746-4832-8160-2b0fd97a8beb
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCagladPath.tendsto_rightLimitProcess_nhdsLT

import Definitions.Def_StochLean_Probability_Process_Path_RightLimit_F000
import Definitions.Def_SourceProof_f57c14a93ac13a6c23d17b04

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

namespace IsCagladPath
theorem _root_.Prove2MeSourceProof.h_8da091e9abd21017e0adf845 {ω : Ω}
    (hX : IsCagladPath (X · ω)) (t : ℝ≥0) :
    Tendsto (rightLimitProcess X · ω) (𝓝[<] t) (𝓝 (X t ω)) :=
  (_root_.Prove2MeSourceProof.h_f57c14a93ac13a6c23d17b04 (hX.1 t))
end IsCagladPath

end ProbabilityTheory


