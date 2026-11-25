-- Prove2me | Definitions.Def_SourceProof_c207270dc0d962c8e8bb99f9
-- name    : SourceProof_c207270dc0d962c8e8bb99f9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:45:34.411986+00:00
-- url     : https://prove2.me/theorems/d81d572f-0f9f-4560-a2c7-de5b4dcbdb53
-- title:
--   StochLean source theorem: StochLean.tsum_sq_add_of_summable_sq

import Definitions.Def_SourceProof_d736afe46a7f9c7922c052c9

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Absolute summability of mixed products and square-sum polarization -/

@[expose] public section

namespace StochLean

variable {ι : Type*} {a b : ι → ℝ}

theorem _root_.Prove2MeSourceProof.h_c207270dc0d962c8e8bb99f9 (ha : Summable (fun i ↦ (a i) ^ 2))
    (hb : Summable (fun i ↦ (b i) ^ 2)) :
    (∑' i, (a i + b i) ^ 2) = (∑' i, (a i) ^ 2) +
      2 * (∑' i, a i * b i) + (∑' i, (b i) ^ 2) := by
  have hab := _root_.Prove2MeSourceProof.h_d736afe46a7f9c7922c052c9 ha hb
  have heq : (fun i ↦ (a i + b i) ^ 2) =
      (fun i ↦ (a i) ^ 2 + 2 * (a i * b i) + (b i) ^ 2) := by
    funext i
    ring
  rw [heq, (ha.add (hab.mul_left 2)).tsum_add hb, ha.tsum_add (hab.mul_left 2),
    hab.tsum_mul_left 2]
end StochLean


