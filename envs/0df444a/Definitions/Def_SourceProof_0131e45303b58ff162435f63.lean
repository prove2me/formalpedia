-- Prove2me | Definitions.Def_SourceProof_0131e45303b58ff162435f63
-- name    : SourceProof_0131e45303b58ff162435f63
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:26:59.356828+00:00
-- url     : https://prove2.me/theorems/5a743db7-1c40-46df-86cf-929d4ea27ce5
-- title:
--   StochLean source theorem: ProbabilityTheory.HasCadlagPaths.rightLimitProcess_leftLimitProcess

import Definitions.Def_StochLean_Probability_Process_Path_RightLimit_F000
import Definitions.Def_SourceProof_23cc5ae095ac1c85ae1e4bc7
import Definitions.Def_SourceProof_a3bc82106adf606a13e0e393

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Cadlag reconstruction from the right limits of source left limits

Although the source left limit is set to zero initially, its right limit at
zero recovers the original initial value of a right-continuous path.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : ℝ≥0 → Ω → ℝ}

namespace HasCadlagPaths
theorem _root_.Prove2MeSourceProof.h_0131e45303b58ff162435f63
    (hX : HasCadlagPaths X P) :
    Indistinguishable (rightLimitProcess (leftLimitProcess X)) X P :=
  hX.mono fun _ hω ↦ (_root_.Prove2MeSourceProof.h_23cc5ae095ac1c85ae1e4bc7 hω)
end HasCadlagPaths

end ProbabilityTheory


