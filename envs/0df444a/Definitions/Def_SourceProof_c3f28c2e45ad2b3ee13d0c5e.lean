-- Prove2me | Definitions.Def_SourceProof_c3f28c2e45ad2b3ee13d0c5e
-- name    : SourceProof_c3f28c2e45ad2b3ee13d0c5e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:11:20.774606+00:00
-- url     : https://prove2.me/theorems/24292051-6241-418e-8c28-ec95da8b4e71
-- title:
--   StochLean source theorem: ProbabilityTheory.jumpProcess_indicator_lifetime_le

import Definitions.Def_StochLean_Probability_Process_Path_LeftLimit_F000
import Definitions.Def_SourceProof_efecaed902c122adaf137548
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Monoid

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Exact source jumps of lifetime step processes

A step activated on the closed lifetime event has left limit activated on the strict lifetime
event. Its jump is the coefficient on the lifetime graph and zero elsewhere. These formulas hold
also at zero, since the source convention is `leftLimitProcess X 0 = 0`, and an infinite lifetime
never activates at a finite time. Finite sums retain exactly the sum of their coincident jumps;
no disjointness assumption or artificial finite value for an infinite lifetime is needed.
-/

@[expose] public section

open Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*}


theorem _root_.Prove2MeSourceProof.h_c3f28c2e45ad2b3ee13d0c5e (τ : Ω → WithTop ℝ≥0) (Z : Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) :
    jumpProcess (fun s v ↦ {v | τ v ≤ (s : WithTop ℝ≥0)}.indicator Z v) t ω =
      {v | τ v = (t : WithTop ℝ≥0)}.indicator Z ω := by
  classical
  change {v | τ v ≤ (t : WithTop ℝ≥0)}.indicator Z ω -
    ProbabilityTheory.leftLimitProcess (fun s v ↦ {v | τ v ≤ (s : WithTop ℝ≥0)}.indicator Z v) t ω = _
  rw [_root_.Prove2MeSourceProof.h_efecaed902c122adaf137548]
  simp only [indicator_apply, mem_ofPred_eq]
  rcases lt_trichotomy (τ ω) (t : WithTop ℝ≥0) with ht | ht | ht
  · simp only [if_pos ht.le, if_pos ht, if_neg ht.ne, sub_self]
  · simp only [ht, le_refl, if_true, lt_self_iff_false, if_false, sub_zero]
  · simp only [if_neg (not_le_of_gt ht), if_neg (not_lt_of_ge ht.le),
      if_neg ht.ne', sub_self]
end ProbabilityTheory


