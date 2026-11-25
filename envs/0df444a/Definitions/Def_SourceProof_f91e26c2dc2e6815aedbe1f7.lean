-- Prove2me | Definitions.Def_SourceProof_f91e26c2dc2e6815aedbe1f7
-- name    : SourceProof_f91e26c2dc2e6815aedbe1f7
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:57:14.04432+00:00
-- url     : https://prove2.me/theorems/b434377e-18df-4973-bc4f-98517c7612ec
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.leftLimitProcess_add

import Definitions.Def_StochLean_Probability_Process_Path_LeftLimit_F000
import Definitions.Def_SourceProof_12d34a5d964556d97aab2788
import Definitions.Def_SourceProof_186a2772edad25f4bcf59290
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Monoid

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Addition of source left limits and jumps, including time zero -/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {X Y : ℝ≥0 → Ω → ℝ} {ω : Ω}

namespace IsCadlagPath
theorem _root_.Prove2MeSourceProof.h_f91e26c2dc2e6815aedbe1f7 (hX : IsCadlagPath (X · ω))
    (hY : IsCadlagPath (Y · ω)) (t : ℝ≥0) :
    leftLimitProcess (X + Y) t ω = leftLimitProcess X t ω + leftLimitProcess Y t ω := by
  by_cases ht : t = 0
  · subst t
    simp only [_root_.Prove2MeSourceProof.h_12d34a5d964556d97aab2788, Pi.zero_apply, add_zero]
  · let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.mpr ht⟩
    rw [ProbabilityTheory.leftLimitProcess, if_neg ht]
    exact leftLim_eq_of_tendsto
      (((_root_.Prove2MeSourceProof.h_186a2772edad25f4bcf59290 hX) ht).add ((_root_.Prove2MeSourceProof.h_186a2772edad25f4bcf59290 hY) ht))
end IsCadlagPath

end ProbabilityTheory


