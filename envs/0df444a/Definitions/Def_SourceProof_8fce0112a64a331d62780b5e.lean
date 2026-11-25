-- Prove2me | Definitions.Def_SourceProof_8fce0112a64a331d62780b5e
-- name    : SourceProof_8fce0112a64a331d62780b5e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:11:09.601357+00:00
-- url     : https://prove2.me/theorems/75d5edcc-65b9-5494-82f7-a66d08f17602
-- title:
--   StochLean source theorem: ProbabilityTheory.leftLimitProcess_finset_sum_indicator_lifetime_le

import Definitions.Def_SourceProof_12d34a5d964556d97aab2788
import Definitions.Def_SourceProof_186a2772edad25f4bcf59290
import Definitions.Def_SourceProof_30748602910a669fc7d80008
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


theorem _root_.Prove2MeSourceProof.h_8fce0112a64a331d62780b5e {ι : Type*} (s : Finset ι)
    (τ : ι → Ω → WithTop ℝ≥0) (Z : ι → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    leftLimitProcess
      (fun u v ↦ ∑ i ∈ s, {v | τ i v ≤ (u : WithTop ℝ≥0)}.indicator (Z i) v) t ω =
      ∑ i ∈ s, {v | τ i v < (t : WithTop ℝ≥0)}.indicator (Z i) ω := by
  classical
  by_cases ht : t = 0
  · subst t
    rw [_root_.Prove2MeSourceProof.h_12d34a5d964556d97aab2788]
    change 0 = _
    symm
    apply Finset.sum_eq_zero
    intro i _
    rw [indicator_of_notMem]
    change ¬ τ i ω < ((0 : ℝ≥0) : WithTop ℝ≥0)
    exact not_lt_of_ge bot_le
  · let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.mpr ht⟩
    rw [ProbabilityTheory.leftLimitProcess, if_neg ht]
    apply leftLim_eq_of_tendsto
    apply tendsto_finsetSum s
    intro i _
    have hi := (_root_.Prove2MeSourceProof.h_186a2772edad25f4bcf59290 (_root_.Prove2MeSourceProof.h_30748602910a669fc7d80008 (τ i) (Z i) ω)) ht
    simpa only [_root_.Prove2MeSourceProof.h_efecaed902c122adaf137548] using hi
end ProbabilityTheory


