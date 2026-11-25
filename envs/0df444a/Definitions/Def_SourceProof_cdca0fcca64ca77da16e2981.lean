-- Prove2me | Definitions.Def_SourceProof_cdca0fcca64ca77da16e2981
-- name    : SourceProof_cdca0fcca64ca77da16e2981
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T14:34:47.515626+00:00
-- url     : https://prove2.me/theorems/968c74a9-c866-4455-8bcf-fdaa3f7b2e07
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.leftLimitProcess_sub

import Definitions.Def_SourceProof_12d34a5d964556d97aab2788
import Definitions.Def_SourceProof_186a2772edad25f4bcf59290
import Definitions.Def_SourceProof_44c235d61a2cdcb446e715a4
import Definitions.Def_SourceProof_60e710b522febb5ad2df8d23
import Definitions.Def_SourceProof_7c758b3f54acb965f59f9d0b

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Algebra of source left limits and jumps

Continuous scalar transformations must preserve zero to commute with the
source left limit at every time, including the special time-zero value.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {X Y : ℝ≥0 → Ω → ℝ} {ω : Ω}

namespace IsCadlagPath
theorem _root_.Prove2MeSourceProof.h_cdca0fcca64ca77da16e2981 (hX : IsCadlagPath (X · ω))
    (hY : IsCadlagPath (Y · ω)) (t : ℝ≥0) :
    leftLimitProcess (X - Y) t ω = leftLimitProcess X t ω - leftLimitProcess Y t ω := by
  by_cases ht : t = 0
  · subst t
    simp only [_root_.Prove2MeSourceProof.h_12d34a5d964556d97aab2788, Pi.zero_apply, sub_self]
  · let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.mpr ht⟩
    rw [ProbabilityTheory.leftLimitProcess, if_neg ht]
    exact leftLim_eq_of_tendsto
      (((_root_.Prove2MeSourceProof.h_186a2772edad25f4bcf59290 hX) ht).sub ((_root_.Prove2MeSourceProof.h_186a2772edad25f4bcf59290 hY) ht))
end IsCadlagPath

end ProbabilityTheory


