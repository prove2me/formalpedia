-- Prove2me | Definitions.Def_SourceProof_d736afe46a7f9c7922c052c9
-- name    : SourceProof_d736afe46a7f9c7922c052c9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:01:30.306892+00:00
-- url     : https://prove2.me/theorems/121487bb-e5c8-4b30-a606-ce61e433f269
-- title:
--   StochLean source theorem: StochLean.summable_mul_of_summable_sq

import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Absolute summability of mixed products and square-sum polarization -/

@[expose] public section

namespace StochLean

variable {ι : Type*} {a b : ι → ℝ}

theorem _root_.Prove2MeSourceProof.h_d736afe46a7f9c7922c052c9 (ha : Summable (fun i ↦ (a i) ^ 2))
    (hb : Summable (fun i ↦ (b i) ^ 2)) : Summable (fun i ↦ a i * b i) := by
  apply (ha.add hb).of_norm_bounded
  intro i
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (a i - b i), sq_nonneg (a i + b i)]
end StochLean


