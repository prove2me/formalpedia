-- Prove2me | Definitions.Def_SourceProof_c000c5f373823d994f025530
-- name    : SourceProof_c000c5f373823d994f025530
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:45:19.510683+00:00
-- url     : https://prove2.me/theorems/a7a84feb-7cab-5fc6-8de1-e856d2aaa8c3
-- title:
--   StochLean source theorem: StochLean.exists_frechet_second_deriv_remainder

import Definitions.Def_SourceProof_0fe51407ad89eab1ae3224f6
import Definitions.Def_SourceProof_7fb89946b2de1262087bfc4c
import Definitions.Def_SourceProof_a8d5fcc354635df5d57d2952

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Second-order Taylor remainders along lines in real normed spaces

The scalar Lagrange remainder is applied to the actual line restriction.
No finite-dimensional assumption or globally bounded derivative is needed.
-/

@[expose] public section

open Set

namespace StochLean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}

theorem _root_.Prove2MeSourceProof.h_c000c5f373823d994f025530 (hf : ContDiff ℝ 2 f) (a b : E) :
    ∃ θ ∈ Icc (0 : ℝ) 1, f b - f a - fderiv ℝ f a (b - a) =
      (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) (a + θ • (b - a)) (b - a) (b - a) := by
  have hg : ContDiff ℝ 2 (fun r : ℝ ↦ f (a + r • (b - a))) :=
    hf.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  obtain ⟨θ, hθ, he⟩ := _root_.Prove2MeSourceProof.h_0fe51407ad89eab1ae3224f6 hg 0 1
  refine ⟨θ, by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hθ, ?_⟩
  rw [_root_.Prove2MeSourceProof.h_a8d5fcc354635df5d57d2952 (hf.differentiable (by decide)),
    _root_.Prove2MeSourceProof.h_7fb89946b2de1262087bfc4c hf] at he
  simpa only [zero_smul, one_smul, add_zero, add_sub_cancel, sub_zero, one_pow, mul_one,
    div_eq_mul_inv, mul_comm, one_mul] using he
end StochLean


