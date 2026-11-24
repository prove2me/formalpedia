-- Prove2me | Definitions.Def_SourceProof_23cc5ae095ac1c85ae1e4bc7
-- name    : SourceProof_23cc5ae095ac1c85ae1e4bc7
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:21:10.865582+00:00
-- url     : https://prove2.me/theorems/f844152c-dbe4-4233-89f8-2d1a70910bf6
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.rightLimitProcess_leftLimitProcess

import Definitions.Def_SourceProof_a3bc82106adf606a13e0e393
import Definitions.Def_SourceProof_f17e21373c03eb2c377aaee1

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

namespace IsCadlagPath
theorem _root_.Prove2MeSourceProof.h_23cc5ae095ac1c85ae1e4bc7 {ω : Ω}
    (hX : IsCadlagPath (X · ω)) (t : ℝ≥0) :
    rightLimitProcess (leftLimitProcess X) t ω = X t ω := by
  apply rightLim_eq_of_tendsto
  apply (_root_.Prove2MeSourceProof.h_f17e21373c03eb2c377aaee1 (hX.1 t)).congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : s ≠ 0 := ne_of_gt ((show (0 : ℝ≥0) ≤ t from bot_le).trans_lt hs)
  simp only [ProbabilityTheory.leftLimitProcess, if_neg hs0]
end IsCadlagPath

end ProbabilityTheory


