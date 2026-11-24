-- Prove2me | Definitions.Def_SourceProof_fff880ea6c6a7bb34bef28fb
-- name    : SourceProof_fff880ea6c6a7bb34bef28fb
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:19:56.781781+00:00
-- url     : https://prove2.me/theorems/7d074d28-99df-4a01-9584-0d8e29f9b35f
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCagladPath.isCadlagPath_rightLimitProcess

import Definitions.Def_StochLean_Probability_Process_Path_RightLimit_F000
import Definitions.Def_SourceProof_1ba1a2c21f7033732d51d48a
import Definitions.Def_SourceProof_8da091e9abd21017e0adf845

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
theorem _root_.Prove2MeSourceProof.h_fff880ea6c6a7bb34bef28fb {ω : Ω}
    (hX : IsCagladPath (X · ω)) : IsCadlagPath (rightLimitProcess X · ω) := by
  constructor
  · intro t
    exact continuousWithinAt_rightLim_Ici ((_root_.Prove2MeSourceProof.h_1ba1a2c21f7033732d51d48a hX) t)
  · intro t _
    exact ⟨X t ω, (_root_.Prove2MeSourceProof.h_8da091e9abd21017e0adf845 hX) t⟩
end IsCagladPath

end ProbabilityTheory


