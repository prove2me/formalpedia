-- Prove2me | Definitions.Def_SourceProof_1ba1a2c21f7033732d51d48a
-- name    : SourceProof_1ba1a2c21f7033732d51d48a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:13:47.280088+00:00
-- url     : https://prove2.me/theorems/f8dcbbc5-208f-47ef-a81a-8eba37f27765
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCagladPath.tendsto_rightLimitProcess

import Definitions.Def_StochLean_Probability_Process_Path_RightLimit_F000

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
theorem _root_.Prove2MeSourceProof.h_1ba1a2c21f7033732d51d48a {ω : Ω} (hX : IsCagladPath (X · ω))
    (t : ℝ≥0) : Tendsto (X · ω) (𝓝[>] t) (𝓝 (rightLimitProcess X t ω)) :=
  tendsto_rightLim_of_tendsto (hX.2 t)
end IsCagladPath

end ProbabilityTheory


