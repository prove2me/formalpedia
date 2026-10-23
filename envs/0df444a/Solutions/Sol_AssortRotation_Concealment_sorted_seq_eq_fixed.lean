-- Prove2me | solution 1 for AssortRotation.Concealment.sorted_seq_eq_fixed
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T19:03:30.923367+00:00
-- url     : https://prove2.me/submissions/90741c1f-f522-45e5-aac3-a85fd6b2c16d

import Mathlib
import Definitions.Def_AssortRotation_Concealment_Model

set_option autoImplicit false

open AssortRotation.Concealment

/-- If every remaining product is rejected at the current purchase count, both
revenues vanish; decreasing marginal utility handles the advancing fixed index. -/
theorem rejected_revenues_zero (v : ℕ → ℝ) (hv : Antitone v)
    (L : List (ℝ × ℝ)) (k : ℕ)
    (h : ∀ a ∈ L, ¬ 0 ≤ v k + a.2 - a.1) :
    seqRev v L k = 0 ∧ fixedRevAux v L k = 0 := by
  induction L generalizing k with
  | nil => simp [seqRev, fixedRevAux]
  | cons a t ih =>
      have ha : ¬ 0 ≤ v k + a.2 - a.1 := h a (by simp)
      have ht : ∀ b ∈ t, ¬ 0 ≤ v k + b.2 - b.1 := by
        intro b hb
        exact h b (by simp [hb])
      have ht' : ∀ b ∈ t, ¬ 0 ≤ v (k + 1) + b.2 - b.1 := by
        intro b hb hn
        have hvk := hv (Nat.le_succ k)
        exact ht b hb (by linarith)
      constructor
      · simpa [seqRev, ha] using (ih k ht).1
      · simpa [fixedRevAux, ha] using (ih (k + 1) ht').2

/-- Equality holds at every common initial purchase count and fixed position. -/
theorem sorted_seq_eq_fixedAux (v : ℕ → ℝ) (hv : Antitone v)
    (L : List (ℝ × ℝ))
    (hL : L.Pairwise (fun a b => b.2 - b.1 ≤ a.2 - a.1)) (k : ℕ) :
    seqRev v L k = fixedRevAux v L k := by
  induction L generalizing k with
  | nil => rfl
  | cons a t ih =>
      obtain ⟨hat, ht⟩ := List.pairwise_cons.mp hL
      by_cases ha : 0 ≤ v k + a.2 - a.1
      · simpa [seqRev, fixedRevAux, ha] using
          congrArg (fun r : ℝ => a.1 + r) (ih ht (k + 1))
      · have hall : ∀ b ∈ a :: t, ¬ 0 ≤ v k + b.2 - b.1 := by
          intro b hb hn
          rcases List.mem_cons.mp hb with rfl | hb
          · exact ha hn
          · have hab := hat b hb
            exact ha (by linarith)
        obtain ⟨hs, hf⟩ := rejected_revenues_zero v hv (a :: t) k hall
        exact hs.trans hf.symm

theorem solution (v : ℕ → ℝ) (hv : MarginalUtility v) (L' : List (ℝ × ℝ))
    (hL' : L'.Pairwise (fun a b => b.2 - b.1 ≤ a.2 - a.1)) :
    seqRev v L' 0 = fixedRev v L' := by
  exact sorted_seq_eq_fixedAux v hv.2 L' hL' 0
