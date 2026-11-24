-- Prove2me | Definitions.Def_SourceProof_0cd12103eb000692396f52e4
-- name    : SourceProof_0cd12103eb000692396f52e4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:13:37.276326+00:00
-- url     : https://prove2.me/theorems/4079532e-1a33-40de-b20d-b27e962c2600
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.tendsto_min_const_nhdsLT

import Definitions.Def_SourceProof_186a2772edad25f4bcf59290
import Definitions.Def_SourceProof_60e710b522febb5ad2df8d23

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Left limits of finite stopped paths

At the stopping endpoint the strict-left limit is the original strict-left limit,
not the stopped value after its jump.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {X : ℝ≥0 → Ω → ℝ} {ω : Ω}

namespace IsCadlagPath
theorem _root_.Prove2MeSourceProof.h_0cd12103eb000692396f52e4 (hX : IsCadlagPath (X · ω))
    {t : ℝ≥0} (ht : t ≠ 0) (a : ℝ≥0) :
    Tendsto (fun s ↦ X (min a s) ω) (𝓝[<] t)
      (𝓝 (if a < t then X a ω else leftLimitProcess X t ω)) := by
  by_cases ha : a < t
  · rw [if_pos ha]
    apply tendsto_const_nhds.congr'
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds ha)] with s hs
    rw [min_eq_left hs.le]
  · rw [if_neg ha]
    apply ((_root_.Prove2MeSourceProof.h_186a2772edad25f4bcf59290 hX) ht).congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [min_eq_right (hs.le.trans (le_of_not_gt ha))]
end IsCadlagPath

end ProbabilityTheory


