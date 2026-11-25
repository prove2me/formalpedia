-- Prove2me | Definitions.Def_SourceProof_0a747dfdc63dcf3edfcb5081
-- name    : SourceProof_0a747dfdc63dcf3edfcb5081
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:13:57.558491+00:00
-- url     : https://prove2.me/theorems/9d7cfee9-6496-4427-a2fb-38f77569c957
-- title:
--   StochLean source theorem: StochLean.TimePartition.tendstoUniformlyOn_leftStep

import Definitions.Def_SourceProof_1f1a39edad68d4f3bc6e94ca
import Definitions.Def_SourceProof_2ba9ae385eb9bd368051c43f
import Definitions.Def_SourceProof_4ffa320b02b60d0dbe7bd7da
import Definitions.Def_SourceProof_7ebcdf415b376e81ffc593ac
import Definitions.Def_SourceProof_8f7895612117943074291d58

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Left-endpoint step approximation on a finite partition

Cells are left-open and right-closed. Repeated endpoints are permitted: every
positive time before the horizon belongs to exactly one nonempty cell.
-/

@[expose] public section

open Filter Set
open scoped NNReal Topology

namespace StochLean.TimePartition

variable {T : ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_0a747dfdc63dcf3edfcb5081 {π : ℕ → TimePartition T} {f : ℝ≥0 → ℝ}
    (hf : ContinuousOn f (Icc 0 T))
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) :
    TendstoUniformlyOn (fun n ↦ (π n).leftStep f) f atTop (Icc 0 T) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) ε hε
  filter_upwards [hmesh.eventually_lt_const hδ] with n hn
  intro t ht
  by_cases ht0 : t = 0
  · subst t
    simpa only [_root_.Prove2MeSourceProof.h_4ffa320b02b60d0dbe7bd7da, dist_self] using hε
  · obtain ⟨i, hi⟩ := (_root_.Prove2MeSourceProof.h_8f7895612117943074291d58 (π n)) ⟨lt_of_le_of_ne bot_le (Ne.symm ht0), ht.2⟩
    rw [(_root_.Prove2MeSourceProof.h_1f1a39edad68d4f3bc6e94ca (π n)) f hi]
    exact hmod t ht ((π n).left i) ⟨bot_le, (_root_.Prove2MeSourceProof.h_2ba9ae385eb9bd368051c43f (π n)) _⟩
      (((_root_.Prove2MeSourceProof.h_7ebcdf415b376e81ffc593ac (π n)) hi).trans_lt hn)
end StochLean.TimePartition


