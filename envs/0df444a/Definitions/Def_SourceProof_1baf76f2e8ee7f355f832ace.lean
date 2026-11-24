-- Prove2me | Definitions.Def_SourceProof_1baf76f2e8ee7f355f832ace
-- name    : SourceProof_1baf76f2e8ee7f355f832ace
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T16:06:49.790803+00:00
-- url     : https://prove2.me/theorems/faef102b-b4d8-43b9-8a50-5e128fb1a5d2
-- title:
--   StochLean source theorem: StochLean.eq_zero_of_forall_int_affine_nonneg

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # A real affine function nonnegative at every integer has zero slope -/

@[expose] public section

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_1baf76f2e8ee7f355f832ace {a b : ℝ}
    (h : ∀ n : ℤ, 0 ≤ a + (n : ℝ) * b) : b = 0 := by
  by_contra hb
  rcases lt_or_gt_of_ne hb with hn | hp
  · obtain ⟨n, hlt⟩ := exists_int_gt (-a / b)
    have hm : (n : ℝ) * b < -a := (div_lt_iff_of_neg hn).mp hlt
    linarith [h n]
  · obtain ⟨n, hlt⟩ := exists_int_lt (-a / b)
    have hm : (n : ℝ) * b < -a := (lt_div_iff₀ hp).mp hlt
    linarith [h n]
end StochLean


