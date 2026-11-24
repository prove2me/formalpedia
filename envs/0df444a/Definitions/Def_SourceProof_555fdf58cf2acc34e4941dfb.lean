-- Prove2me | Definitions.Def_SourceProof_555fdf58cf2acc34e4941dfb
-- name    : SourceProof_555fdf58cf2acc34e4941dfb
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:13:46.633708+00:00
-- url     : https://prove2.me/theorems/78b828ec-adbb-40e2-9ad0-fac1891f14f6
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.leftLimitProcess_continuous_comp

import Definitions.Def_SourceProof_12d34a5d964556d97aab2788
import Definitions.Def_SourceProof_186a2772edad25f4bcf59290
import Definitions.Def_SourceProof_60e710b522febb5ad2df8d23
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Monoid

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
theorem _root_.Prove2MeSourceProof.h_555fdf58cf2acc34e4941dfb (hX : IsCadlagPath (X · ω))
    {f : ℝ → ℝ} (hf : Continuous f) (h0 : f 0 = 0) (t : ℝ≥0) :
    leftLimitProcess (fun s v ↦ f (X s v)) t ω = f (leftLimitProcess X t ω) := by
  by_cases ht : t = 0
  · subst t
    simp only [_root_.Prove2MeSourceProof.h_12d34a5d964556d97aab2788, Pi.zero_apply, h0]
  · let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.mpr ht⟩
    rw [ProbabilityTheory.leftLimitProcess, if_neg ht]
    exact leftLim_eq_of_tendsto (hf.continuousAt.tendsto.comp ((_root_.Prove2MeSourceProof.h_186a2772edad25f4bcf59290 hX) ht))
end IsCadlagPath

end ProbabilityTheory


