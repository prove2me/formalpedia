-- Prove2me | solution 1 for AssortRotation.Concealment.remark_1
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T18:50:19.347703+00:00
-- url     : https://prove2.me/submissions/709d28a3-19c4-4af8-974e-7b4bd6dbf2a6

import Mathlib
import Definitions.Def_AssortRotation_Concealment_Model

set_option autoImplicit false

open AssortRotation.Concealment

/-- Appending a nonnegative-price product cannot reduce revenue at any initial
purchase count. No restriction on the utility sequence or preceding prices is needed. -/
theorem seqRev_append_singleton_ge (v : ℕ → ℝ) (L : List (ℝ × ℝ))
    (a : ℝ × ℝ) (ha : 0 ≤ a.1) (k : ℕ) :
    seqRev v L k ≤ seqRev v (L ++ [a]) k := by
  induction L generalizing k with
  | nil =>
      simp only [List.nil_append, seqRev, add_zero]
      split_ifs
      · exact ha
      · exact le_refl 0
  | cons b L ih =>
      simp only [List.cons_append, seqRev]
      split_ifs
      · exact add_le_add le_rfl (ih (k + 1))
      · exact ih k

theorem solution (v : ℕ → ℝ) (hv : MarginalUtility v) (L : List (ℝ × ℝ))
    (a : ℝ × ℝ) (ha : 0 ≤ a.1) :
    seqRev v L 0 ≤ seqRev v (L ++ [a]) 0 := by
  exact seqRev_append_singleton_ge v L a ha 0
