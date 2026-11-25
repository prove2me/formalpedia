-- Prove2me | Definitions.Def_SourceProof_efecaed902c122adaf137548
-- name    : SourceProof_efecaed902c122adaf137548
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:00:50.736565+00:00
-- url     : https://prove2.me/theorems/ed6c2bd3-adb4-4f77-8d6b-92b6000515c3
-- title:
--   StochLean source theorem: ProbabilityTheory.leftLimitProcess_indicator_lifetime_le

import Definitions.Def_StochLean_Probability_Process_Path_LeftLimit_F000
import Definitions.Def_SourceProof_f1eecfb482111cc086390a11
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


theorem _root_.Prove2MeSourceProof.h_efecaed902c122adaf137548 (τ : Ω → WithTop ℝ≥0) (Z : Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) :
    leftLimitProcess (fun s v ↦ {v | τ v ≤ (s : WithTop ℝ≥0)}.indicator Z v) t ω =
      {v | τ v < (t : WithTop ℝ≥0)}.indicator Z ω := by
  classical
  cases hτ : τ ω with
  | top =>
    have hc : Function.leftLim (fun _ : ℝ≥0 ↦ (0 : ℝ)) t = 0 :=
      (continuous_const : Continuous (fun _ : ℝ≥0 ↦ (0 : ℝ))).continuousWithinAt.leftLim_eq
    simp only [ProbabilityTheory.leftLimitProcess, indicator_apply, mem_ofPred_eq, hτ,
      WithTop.not_top_le_coe, not_top_lt, if_false, hc, ite_self]
  | coe a =>
    simpa only [ProbabilityTheory.leftLimitProcess, indicator_apply, mem_ofPred_eq, hτ,
      WithTop.coe_le_coe, WithTop.coe_lt_coe] using _root_.Prove2MeSourceProof.h_f1eecfb482111cc086390a11 a Z t ω
end ProbabilityTheory


