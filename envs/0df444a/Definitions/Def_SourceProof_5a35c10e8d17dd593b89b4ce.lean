-- Prove2me | Definitions.Def_SourceProof_5a35c10e8d17dd593b89b4ce
-- name    : SourceProof_5a35c10e8d17dd593b89b4ce
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T16:07:38.401298+00:00
-- url     : https://prove2.me/theorems/80a7fd76-24e5-4e03-ad4d-c67e7e74f25f
-- title:
--   StochLean source theorem: StochLean.summable_abs_mul_of_summable_sq

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

theorem _root_.Prove2MeSourceProof.h_5a35c10e8d17dd593b89b4ce (ha : Summable (fun i ↦ (a i) ^ 2))
    (hb : Summable (fun i ↦ (b i) ^ 2)) : Summable (fun i ↦ |a i * b i|) := by
  apply (ha.add hb).of_norm_bounded
  intro i
  rw [Real.norm_of_nonneg (abs_nonneg _)]
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (a i - b i), sq_nonneg (a i + b i)]
end StochLean


