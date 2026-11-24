-- Prove2me | Definitions.Def_SourceProof_2adad6656f12f977d8bc8198
-- name    : SourceProof_2adad6656f12f977d8bc8198
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:26:50.205923+00:00
-- url     : https://prove2.me/theorems/153996cd-26f0-4c4c-be35-f11295ede4a6
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.jumpProcess_stoppedProcess

import Definitions.Def_SourceProof_153a0472af900f281bd2d4a8

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Source jumps of stopped cadlag paths

The endpoint jump is included: the cutoff is `t <= tau`, not `t < tau`.
The original initial jump is retained, including when the stopping time is zero.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {ω : Ω}

namespace IsCadlagPath
theorem _root_.Prove2MeSourceProof.h_2adad6656f12f977d8bc8198 (hX : IsCadlagPath (X · ω))
    (τ : Ω → WithTop ℝ≥0) (t : ℝ≥0) :
    jumpProcess (MeasureTheory.stoppedProcess X τ) t ω =
      if (t : WithTop ℝ≥0) ≤ τ ω then jumpProcess X t ω else 0 := by
  cases hτ : τ ω with
  | top =>
    simp only [ProbabilityTheory.jumpProcess, Pi.sub_apply, ProbabilityTheory.leftLimitProcess, MeasureTheory.stoppedProcess,
      hτ, min_eq_left le_top, WithTop.untopA, WithTop.untopD_coe, if_pos le_top]
  | coe a =>
    simpa only [ProbabilityTheory.jumpProcess, Pi.sub_apply, ProbabilityTheory.leftLimitProcess, MeasureTheory.stoppedProcess,
      hτ, ← WithTop.coe_min, WithTop.untopA, WithTop.untopD_coe, WithTop.coe_le_coe]
      using (_root_.Prove2MeSourceProof.h_153a0472af900f281bd2d4a8 hX) a t
end IsCadlagPath

end ProbabilityTheory


