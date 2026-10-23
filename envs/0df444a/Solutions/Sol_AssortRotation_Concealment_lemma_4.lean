-- Prove2me | solution 1 for AssortRotation.Concealment.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T19:08:23.94807+00:00
-- url     : https://prove2.me/submissions/177d535e-4397-430e-8c67-f63b2546b66e

import Mathlib
import Definitions.Def_AssortRotation_Concealment_Model

set_option autoImplicit false

open AssortRotation.Concealment

/-- One additional prior purchase can reduce tail revenue by at most a common
nonnegative upper bound on the tail prices. -/
private theorem tail_revenue_bound (v : ℕ → ℝ) (hv : Antitone v)
    (t : List (ℝ × ℝ)) (P : ℝ) (hP : 0 ≤ P)
    (ht : ∀ b ∈ t, b.1 ≤ P) (k : ℕ) :
    seqRev v t k ≤ P + seqRev v t (k + 1) := by
  induction t generalizing k with
  | nil => simpa [seqRev] using hP
  | cons a t ih =>
      have ha : a.1 ≤ P := ht a (by simp)
      have ht' : ∀ b ∈ t, b.1 ≤ P := fun b hb => ht b (by simp [hb])
      have hdec : v (k + 1) ≤ v k := hv (Nat.le_succ k)
      by_cases h0 : 0 ≤ v k + a.2 - a.1
      · by_cases h1 : 0 ≤ v (k + 1) + a.2 - a.1
        · simp only [seqRev, if_pos h0, if_pos h1]
          have hi := ih ht' (k + 1)
          linarith
        · simp only [seqRev, if_pos h0, if_neg h1]
          linarith
      · have h1 : ¬0 ≤ v (k + 1) + a.2 - a.1 := by linarith
        simpa only [seqRev, if_neg h0, if_neg h1] using ih ht' k

theorem solution (v : ℕ → ℝ) (hv : MarginalUtility v) (a₁ a₂ : ℝ × ℝ)
    (t : List (ℝ × ℝ))
    (hp : ∀ b ∈ a₁ :: a₂ :: t, 0 ≤ b.1) (h₂ : a₂.1 ≤ a₁.1)
    (ht : ∀ b ∈ t, b.1 ≤ a₁.1)
    (hX : a₁.2 - a₁.1 ≤ a₂.2 - a₂.1) :
    seqRev v (a₂ :: a₁ :: t) 0 ≤ seqRev v (a₁ :: a₂ :: t) 0 := by
  have hdec : v 1 ≤ v 0 := hv.2 (by omega)
  by_cases h10 : 0 ≤ v 0 + a₁.2 - a₁.1
  · have h20 : 0 ≤ v 0 + a₂.2 - a₂.1 := by linarith
    by_cases h11 : 0 ≤ v 1 + a₁.2 - a₁.1
    · have h21 : 0 ≤ v 1 + a₂.2 - a₂.1 := by linarith
      simp only [seqRev, if_pos h10, if_pos h20, Nat.reduceAdd,
        if_pos h11, if_pos h21]
      linarith
    · by_cases h21 : 0 ≤ v 1 + a₂.2 - a₂.1
      · simp only [seqRev, if_pos h10, if_pos h20, Nat.reduceAdd,
          if_neg h11, if_pos h21]
        have hb := tail_revenue_bound v hv.2 t a₁.1 (hp a₁ (by simp)) ht 1
        norm_num only at hb
        linarith
      · simp only [seqRev, if_pos h10, if_pos h20, Nat.reduceAdd,
          if_neg h11, if_neg h21]
        linarith
  · have h11 : ¬0 ≤ v 1 + a₁.2 - a₁.1 := by linarith
    by_cases h20 : 0 ≤ v 0 + a₂.2 - a₂.1
    · simp only [seqRev, if_neg h10, if_pos h20, Nat.reduceAdd, if_neg h11, le_refl]
    · simp only [seqRev, if_neg h10, if_neg h20, le_refl]
