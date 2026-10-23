-- Prove2me | solution 1 for AssortRotation.Concealment.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T19:07:36.776355+00:00
-- url     : https://prove2.me/submissions/ada6564c-49e2-4e4b-9287-a41e74e0647b

import Mathlib
import Definitions.Def_AssortRotation_Concealment_Model

set_option autoImplicit false

open AssortRotation.Concealment

theorem solution (v : ℕ → ℝ) (hv : MarginalUtility v) (L : List (ℝ × ℝ))
    (hp : ∀ a ∈ L, 0 ≤ a.1) (k : ℕ) :
    seqRev v L (k + 1) ≤ seqRev v L k ∧ seqRev v L k ≤ rhoStar L + seqRev v L (k + 1) := by
  induction L generalizing k with
  | nil => simp [seqRev, rhoStar]
  | cons a t ih =>
    have ha : 0 ≤ a.1 := hp a (List.mem_cons_self)
    have ht : ∀ b ∈ t, 0 ≤ b.1 := fun b hb => hp b (List.mem_cons_of_mem a hb)
    have hmono : v (k + 1) ≤ v k := hv.2 (Nat.le_succ k)
    have hprice : a.1 ≤ max a.1 (rhoStar t) := le_max_left _ _
    have htail : rhoStar t ≤ max a.1 (rhoStar t) := le_max_right _ _
    by_cases hk : 0 ≤ v k + a.2 - a.1
    · by_cases hk1 : 0 ≤ v (k + 1) + a.2 - a.1
      · obtain ⟨hlower, hupper⟩ := ih ht (k + 1)
        simp only [seqRev, if_pos hk, if_pos hk1, rhoStar]
        constructor <;> linarith
      · simp only [seqRev, if_pos hk, if_neg hk1, rhoStar]
        constructor <;> linarith
    · have hk1 : ¬ 0 ≤ v (k + 1) + a.2 - a.1 := by
        intro h
        apply hk
        linarith
      obtain ⟨hlower, hupper⟩ := ih ht k
      simp only [seqRev, if_neg hk, if_neg hk1, rhoStar]
      exact ⟨hlower, hupper.trans (add_le_add htail le_rfl)⟩
