-- Prove2me | Definitions.Def_SourceProof_30748602910a669fc7d80008
-- name    : SourceProof_30748602910a669fc7d80008
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:15:24.056797+00:00
-- url     : https://prove2.me/theorems/5e5b7cf8-01ca-44ba-b007-d5dd5ffc8328
-- title:
--   StochLean source theorem: ProbabilityTheory.isCadlagPath_indicator_lifetime_le

import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F000
import Definitions.Def_SourceProof_1c5616a125ac7367f7f20567
import Definitions.Def_SourceProof_a2cb63993a652b5632791121

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Right-continuous step paths at finite and infinite lifetimes

A step at zero retains its new value at zero. An infinite lifetime has no
finite-time step. No terminal process value is introduced.
-/

@[expose] public section

open Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {E : Type*} [TopologicalSpace E] [Zero E]

theorem _root_.Prove2MeSourceProof.h_30748602910a669fc7d80008 {Ω : Type*} (τ : Ω → WithTop ℝ≥0)
    (Z : Ω → E) (ω : Ω) :
    IsCadlagPath (fun t : ℝ≥0 ↦ {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator Z ω) := by
  classical
  cases ht : τ ω with
  | top =>
    have he : (fun t : ℝ≥0 ↦ {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator Z ω) =
        fun _ ↦ 0 := by
      funext t
      simp only [Set.indicator_apply, mem_ofPred_eq, ht, WithTop.not_top_le_coe, if_false]
    rw [he]
    exact _root_.Prove2MeSourceProof.h_a2cb63993a652b5632791121 continuous_const
  | coe a =>
    simpa only [Set.indicator_apply, mem_ofPred_eq, ht, WithTop.coe_le_coe] using
      _root_.Prove2MeSourceProof.h_1c5616a125ac7367f7f20567 a (Z ω)
end ProbabilityTheory


