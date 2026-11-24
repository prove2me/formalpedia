-- Prove2me | Definitions.Def_SourceProof_7d2789077033a79150308442
-- name    : SourceProof_7d2789077033a79150308442
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:45:34.283215+00:00
-- url     : https://prove2.me/theorems/1cfa01ce-a4f3-4c11-8aea-439cc542bbe9
-- title:
--   StochLean source theorem: StochLean.exists_second_deriv_eq_quadraticTaylorSlope

import Definitions.Def_StochLean_ForMathlib_Analysis_QuadraticTaylorSlope_F000
import Definitions.Def_SourceProof_0fe51407ad89eab1ae3224f6
import Definitions.Def_SourceProof_1cf1f1d77236c2b817d0e363

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The continuous quadratic Taylor quotient of a real C2 function

The diagonal is filled with one half of the second derivative, not the
totalized quotient's zero value. This is the coefficient of squared increments
in the exact finite-cell Taylor identity used for Ito's formula.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_7d2789077033a79150308442 {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (a b : ℝ) :
    ∃ c ∈ uIcc a b, deriv (deriv f) c / 2 = quadraticTaylorSlope f a b := by
  by_cases h : a = b
  · subst b
    exact ⟨a, left_mem_uIcc, (_root_.Prove2MeSourceProof.h_1cf1f1d77236c2b817d0e363 f a).symm⟩
  · obtain ⟨c, hc, he⟩ := _root_.Prove2MeSourceProof.h_0fe51407ad89eab1ae3224f6 hf a b
    refine ⟨c, hc, ?_⟩
    rw [StochLean.quadraticTaylorSlope, if_neg h]
    exact (eq_div_iff (pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm h)))).mpr he.symm
end StochLean


