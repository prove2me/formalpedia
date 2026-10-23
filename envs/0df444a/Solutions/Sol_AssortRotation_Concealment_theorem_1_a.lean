-- Prove2me | solution 1 for AssortRotation.Concealment.theorem_1_a
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T19:08:41.694506+00:00
-- url     : https://prove2.me/submissions/386fc577-cbe7-4349-8c9a-727e9b73fa05

import Mathlib
import Definitions.Def_AssortRotation_Concealment_Model

set_option autoImplicit false

open AssortRotation.Concealment

/-- One extra prior purchase costs at most a common nonnegative upper bound
on the prices of the remaining products. -/
private theorem bridge_tail_bound (v : ℕ → ℝ) (hv : Antitone v)
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
      · have h1 : ¬ 0 ≤ v (k + 1) + a.2 - a.1 := by linarith
        simpa only [seqRev, if_neg h0, if_neg h1] using ih ht' k

/-- The highest-price product may be moved behind a product with at least
as large an adjusted valuation, without increasing revenue, at every count. -/
private theorem bridge_swap (v : ℕ → ℝ) (hv : Antitone v)
    (a b : ℝ × ℝ) (t : List (ℝ × ℝ)) (ha : 0 ≤ a.1)
    (hb : b.1 ≤ a.1) (ht : ∀ c ∈ t, c.1 ≤ a.1)
    (hX : a.2 - a.1 ≤ b.2 - b.1) (k : ℕ) :
    seqRev v (b :: a :: t) k ≤ seqRev v (a :: b :: t) k := by
  have hdec : v (k + 1) ≤ v k := hv (Nat.le_succ k)
  by_cases ha0 : 0 ≤ v k + a.2 - a.1
  · have hb0 : 0 ≤ v k + b.2 - b.1 := by linarith
    by_cases ha1 : 0 ≤ v (k + 1) + a.2 - a.1
    · have hb1 : 0 ≤ v (k + 1) + b.2 - b.1 := by linarith
      simp only [seqRev, if_pos ha0, if_pos hb0, if_pos ha1, if_pos hb1]
      linarith
    · by_cases hb1 : 0 ≤ v (k + 1) + b.2 - b.1
      · simp only [seqRev, if_pos ha0, if_pos hb0, if_neg ha1, if_pos hb1]
        have htail := bridge_tail_bound v hv t a.1 ha ht (k + 1)
        linarith
      · simp only [seqRev, if_pos ha0, if_pos hb0, if_neg ha1, if_neg hb1]
        linarith
  · have ha1 : ¬ 0 ≤ v (k + 1) + a.2 - a.1 := by linarith
    by_cases hb0 : 0 ≤ v k + b.2 - b.1
    · simp only [seqRev, if_neg ha0, if_pos hb0, if_neg ha1, le_refl]
    · simp only [seqRev, if_neg ha0, if_neg hb0, le_refl]

/-- Moving a highest-price product across a prefix of higher adjusted
valuations cannot increase revenue. The induction handles both possible
purchase counts after each common prefix head. -/
private theorem bridge_insert (v : ℕ → ℝ) (hv : Antitone v)
    (a : ℝ × ℝ) (ha : 0 ≤ a.1) (pre suf : List (ℝ × ℝ)) :
    (∀ b ∈ pre ++ suf, b.1 ≤ a.1) →
    (∀ b ∈ pre, a.2 - a.1 ≤ b.2 - b.1) →
    ∀ k : ℕ, seqRev v (pre ++ a :: suf) k ≤ seqRev v (a :: (pre ++ suf)) k := by
  induction pre with
  | nil =>
      intro hmax hscore k
      exact le_rfl
  | cons b pre ih =>
      intro hmax hscore k
      have hb : b.1 ≤ a.1 := hmax b (by simp)
      have ht : ∀ c ∈ pre ++ suf, c.1 ≤ a.1 := by
        intro c hc
        exact hmax c (by simp [hc])
      have hbX : a.2 - a.1 ≤ b.2 - b.1 := hscore b (by simp)
      have htX : ∀ c ∈ pre, a.2 - a.1 ≤ c.2 - c.1 := by
        intro c hc
        exact hscore c (by simp [hc])
      have hprefix :
          seqRev v (b :: (pre ++ a :: suf)) k ≤
            seqRev v (b :: a :: (pre ++ suf)) k := by
        by_cases hbuy : 0 ≤ v k + b.2 - b.1
        · simp only [seqRev, if_pos hbuy]
          exact add_le_add le_rfl (ih ht htX (k + 1))
        · simpa only [seqRev, if_neg hbuy] using ih ht htX k
      exact hprefix.trans (bridge_swap v hv a b (pre ++ suf) ha hb ht hbX k)

/-- Price order dominates every adjusted-valuation order of the same
multiset, including repeated products and ties, at every prior count. -/
private theorem bridge_ordered_seq (v : ℕ → ℝ) (hv : Antitone v)
    (L : List (ℝ × ℝ)) :
    (∀ a ∈ L, 0 ≤ a.1) →
    L.Pairwise (fun a b => b.1 ≤ a.1) →
    ∀ L' : List (ℝ × ℝ), L'.Perm L →
    L'.Pairwise (fun a b => b.2 - b.1 ≤ a.2 - a.1) →
    ∀ k : ℕ, seqRev v L' k ≤ seqRev v L k := by
  induction L with
  | nil =>
      intro hp hdec L' hperm hσ k
      have hnil : L' = [] := hperm.eq_nil
      subst L'
      exact le_rfl
  | cons a t ih =>
      intro hp hdec L' hperm hσ k
      obtain ⟨hmax, htdec⟩ := List.pairwise_cons.mp hdec
      have hamem : a ∈ L' := hperm.mem_iff.mpr (by simp)
      obtain ⟨pre, suf, rfl⟩ := List.append_of_mem hamem
      have htailperm : (pre ++ suf).Perm t := by
        have hfront : (a :: (pre ++ suf)).Perm (a :: t) :=
          List.perm_middle.symm.trans hperm
        exact hfront.cons_inv
      obtain ⟨hpre, hcons, hcross⟩ := List.pairwise_append.mp hσ
      have hσtail : (pre ++ suf).Pairwise (fun a b => b.2 - b.1 ≤ a.2 - a.1) := by
        apply List.pairwise_append.mpr
        refine ⟨hpre, (List.pairwise_cons.mp hcons).2, ?_⟩
        intro b hb c hc
        exact hcross b hb c (by simp [hc])
      have hptail : ∀ b ∈ t, 0 ≤ b.1 := fun b hb => hp b (by simp [hb])
      have htail : ∀ j : ℕ, seqRev v (pre ++ suf) j ≤ seqRev v t j :=
        ih hptail htdec (pre ++ suf) htailperm hσtail
      have hmax' : ∀ b ∈ pre ++ suf, b.1 ≤ a.1 := by
        intro b hb
        exact hmax b (htailperm.mem_iff.mp hb)
      have hscore : ∀ b ∈ pre, a.2 - a.1 ≤ b.2 - b.1 := by
        intro b hb
        exact hcross b hb a (by simp)
      have hinsert := bridge_insert v hv a (hp a (by simp)) pre suf hmax' hscore k
      refine hinsert.trans ?_
      by_cases hbuy : 0 ≤ v k + a.2 - a.1
      · simp only [seqRev, if_pos hbuy]
        exact add_le_add le_rfl (htail (k + 1))
      · simpa only [seqRev, if_neg hbuy] using htail k

/-- If every product is rejected at count k, increasing the fixed index
cannot make a product acceptable, and both revenues vanish. -/
private theorem bridge_rejected_zero (v : ℕ → ℝ) (hv : Antitone v)
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
        have hdec := hv (Nat.le_succ k)
        exact ht b hb (by linarith)
      constructor
      · simpa [seqRev, ha] using (ih k ht).1
      · simpa [fixedRevAux, ha] using (ih (k + 1) ht').2

private theorem bridge_sorted_eq (v : ℕ → ℝ) (hv : Antitone v)
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
        obtain ⟨hs, hf⟩ := bridge_rejected_zero v hv (a :: t) k hall
        exact hs.trans hf.symm

theorem solution (v : ℕ → ℝ) (hv : MarginalUtility v) (L : List (ℝ × ℝ))
    (hp : ∀ a ∈ L, 0 ≤ a.1) (hdec : L.Pairwise (fun a b => b.1 ≤ a.1)) (L' : List (ℝ × ℝ))
    (hperm : L'.Perm L) (hσ : L'.Pairwise (fun a b => b.2 - b.1 ≤ a.2 - a.1)) :
    fixedRev v L' ≤ seqRev v L 0 := by
  have heq : seqRev v L' 0 = fixedRev v L' := bridge_sorted_eq v hv.2 L' hσ 0
  rw [← heq]
  exact bridge_ordered_seq v hv.2 L hp hdec L' hperm hσ 0
