-- Prove2me | Definitions.Def_SourceProof_ecbfe96d629906d63863658f
-- name    : SourceProof_ecbfe96d629906d63863658f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:26:37.330885+00:00
-- url     : https://prove2.me/theorems/747764e6-e812-4ddd-966c-ffc6cafffa55
-- title:
--   StochLean source theorem: ProbabilityTheory.jumpProcess_finset_sum_indicator_lifetime_le

import Definitions.Def_StochLean_Probability_Process_Path_LeftLimit_F000
import Definitions.Def_SourceProof_8fce0112a64a331d62780b5e
import Definitions.Def_SourceProof_c3f28c2e45ad2b3ee13d0c5e
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


theorem _root_.Prove2MeSourceProof.h_ecbfe96d629906d63863658f {ι : Type*} (s : Finset ι)
    (τ : ι → Ω → WithTop ℝ≥0) (Z : ι → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    jumpProcess
      (fun u v ↦ ∑ i ∈ s, {v | τ i v ≤ (u : WithTop ℝ≥0)}.indicator (Z i) v) t ω =
      ∑ i ∈ s, {v | τ i v = (t : WithTop ℝ≥0)}.indicator (Z i) ω := by
  change (∑ i ∈ s, {v | τ i v ≤ (t : WithTop ℝ≥0)}.indicator (Z i) ω) -
    ProbabilityTheory.leftLimitProcess
      (fun u v ↦ ∑ i ∈ s, {v | τ i v ≤ (u : WithTop ℝ≥0)}.indicator (Z i) v) t ω = _
  rw [_root_.Prove2MeSourceProof.h_8fce0112a64a331d62780b5e, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hi := _root_.Prove2MeSourceProof.h_c3f28c2e45ad2b3ee13d0c5e (τ i) (Z i) t ω
  simpa only [ProbabilityTheory.jumpProcess, Pi.sub_apply, _root_.Prove2MeSourceProof.h_efecaed902c122adaf137548] using hi
end ProbabilityTheory


