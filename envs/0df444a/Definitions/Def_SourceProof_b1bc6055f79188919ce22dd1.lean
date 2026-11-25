-- Prove2me | Definitions.Def_SourceProof_b1bc6055f79188919ce22dd1
-- name    : SourceProof_b1bc6055f79188919ce22dd1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T08:00:15.885551+00:00
-- url     : https://prove2.me/theorems/c8873823-872a-42ac-8c27-473faa0bac39
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.leftLimitProcess_mul

import Definitions.Def_StochLean_Probability_Process_Path_LeftLimit_F000
import Definitions.Def_SourceProof_12d34a5d964556d97aab2788
import Definitions.Def_SourceProof_186a2772edad25f4bcf59290
import Definitions.Def_SourceProof_523d7cde826eec51d63a0e17
import Definitions.Def_SourceProof_992997dcec9963390c8c98e7
import Mathlib.Topology.Algebra.Group.Basic

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Multiplication of source left limits

Both source left limits vanish at zero, so multiplication commutes with the
left-limit operation at every time, not only at positive times.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {X Y : ℝ≥0 → Ω → ℝ} {ω : Ω}

namespace IsCadlagPath
theorem _root_.Prove2MeSourceProof.h_b1bc6055f79188919ce22dd1 (hX : IsCadlagPath (X · ω))
    (hY : IsCadlagPath (Y · ω)) (t : ℝ≥0) :
    leftLimitProcess (X * Y) t ω = leftLimitProcess X t ω * leftLimitProcess Y t ω := by
  by_cases ht : t = 0
  · subst t
    simp only [_root_.Prove2MeSourceProof.h_12d34a5d964556d97aab2788, Pi.zero_apply, mul_zero]
  · let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.mpr ht⟩
    rw [ProbabilityTheory.leftLimitProcess, if_neg ht]
    exact leftLim_eq_of_tendsto
      (((_root_.Prove2MeSourceProof.h_186a2772edad25f4bcf59290 hX) ht).mul ((_root_.Prove2MeSourceProof.h_186a2772edad25f4bcf59290 hY) ht))
end IsCadlagPath

end ProbabilityTheory


