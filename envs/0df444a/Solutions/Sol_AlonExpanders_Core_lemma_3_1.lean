-- Prove2me | solution 1 for AlonExpanders.Core.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T05:48:34.210881+00:00
-- url     : https://prove2.me/submissions/e2e4f8eb-4290-429a-85cc-e917dc196f72

import Mathlib
import Definitions.Def_AlonExpanders_Core_IsStrongExpander
import Definitions.Def_AlonExpanders_Core_IsMagnifier



namespace AlonExpanders.Core

lemma l31_arith (n a b p m c : ℝ) (hn : 0 < n) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ n)
    (hc0 : 0 ≤ c) (hc3 : c ≤ 3) (hm0 : 0 ≤ m) (hmn : m ≤ n)
    (h1 : (1 + c * (1 - a / n)) * a ≤ p)
    (h2 : (1 + c * (1 - (n - m) / n)) * (n - m) ≤ n - b) :
    c / 16 * (a + b) ≤ p - b ∨ c / 16 * (a + b) ≤ m - a := by
  have e1 : (1 + c * (1 - a / n)) * a = a + c * a * (n - a) / n := by field_simp
  have e2 : (1 + c * (1 - (n - m) / n)) * (n - m) = (n - m) + c * m * (n - m) / n := by
    field_simp; ring
  rw [e1] at h1; rw [e2] at h2
  have h1' : c * a * (n - a) ≤ n * (p - a) := by
    have := h1; rw [show a + c * a * (n - a) / n = a + (c * a * (n - a)) / n from rfl] at this
    have h : c * a * (n - a) / n ≤ p - a := by linarith
    rw [div_le_iff₀ hn] at h; linarith
  have h2' : c * m * (n - m) ≤ n * (m - b) := by
    have h : c * m * (n - m) / n ≤ m - b := by linarith
    rw [div_le_iff₀ hn] at h; linarith
  rcases le_or_gt b a with hba | hba
  · left
    rcases le_or_gt (2 * a) n with han | han
    · -- c a (n-a) ≥ c a n / 2
      have : c * a * n ≤ 2 * (c * a * (n - a)) := by nlinarith [mul_nonneg (mul_nonneg hc0 ha) (sub_nonneg.2 han)]
      have h3 : c * a ≤ 2 * (p - a) := le_of_mul_le_mul_right (by linarith) hn
      nlinarith [mul_nonneg hc0 ha, mul_nonneg hc0 hb]
    · have hk : c * b * n ≤ 2 * (c * a * (n - a)) := by
        have : b ≤ n - a := by linarith
        nlinarith [mul_nonneg hc0 ha, mul_nonneg hc0 hb, mul_nonneg (mul_nonneg hc0 ha) (sub_nonneg.2 this)]
      have hpb : c * b ≤ 2 * (p - a) := le_of_mul_le_mul_right (by linarith) hn
      rcases le_or_gt c 2 with hc2 | hc2
      · nlinarith [mul_nonneg hc0 ha, mul_nonneg hc0 hb, mul_nonneg (sub_nonneg.2 hc2) (sub_nonneg.2 hba)]
      · nlinarith
  · right
    have hmb : b ≤ m := by
      have : 0 ≤ c * m * (n - m) := mul_nonneg (mul_nonneg hc0 hm0) (by linarith)
      nlinarith
    rcases le_or_gt (2 * m) n with hmn2 | hmn2
    · have : c * m * n ≤ 2 * (c * m * (n - m)) := by nlinarith [mul_nonneg (mul_nonneg hc0 hm0) (sub_nonneg.2 hmn2)]
      have : c * m ≤ 2 * (m - b) := le_of_mul_le_mul_right (by linarith) hn
      nlinarith [mul_nonneg hc0 (sub_nonneg.2 hmb)]
    · have hk : c * (n - m) * n ≤ 2 * (c * m * (n - m)) := by
        nlinarith [mul_nonneg (mul_nonneg hc0 (sub_nonneg.2 hmn)) (sub_nonneg.2 hmn2.le)]
      have hA0 : c * (n - m) ≤ 2 * (m - b) := le_of_mul_le_mul_right (by linarith) hn
      have hA : c * (n - m) / 2 ≤ m - a := by linarith
      have hB : b - (n - m) ≤ m - a := by linarith
      -- (c+2)(m-a) ≥ c b
      have : c * b ≤ (c + 2) * (m - a) := by nlinarith
      nlinarith

section comb
variable {I O : Type} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (G : SimpleGraph (I ⊕ O)) [DecidableRel G.Adj]

def l31NI (A : Finset I) : Finset O :=
  Finset.univ.filter (fun o => ∃ i ∈ A, G.Adj (Sum.inl i) (Sum.inr o))

def l31NO (B : Finset O) : Finset I :=
  Finset.univ.filter (fun i => ∃ o ∈ B, G.Adj (Sum.inr o) (Sum.inl i))

lemma l31_nbI (hbip : IsIOBipartite G) (A : Finset I) :
    AKSSorting.Core.neighbours G (A.map Function.Embedding.inl) =
      (((l31NI G A).map Function.Embedding.inr : Finset (I ⊕ O)) : Set (I ⊕ O)) := by
  ext v
  rcases v with i | o
  · simp only [AKSSorting.Core.neighbours, Set.mem_setOf_eq, Finset.mem_map,
      Function.Embedding.inl_apply, Finset.coe_map, Set.mem_image, Finset.mem_coe,
      Function.Embedding.inr_apply]
    constructor
    · rintro ⟨x, ⟨j, hj, rfl⟩, h⟩; exact absurd h (hbip.1 j i)
    · rintro ⟨o, _, h⟩; cases h
  · simp only [AKSSorting.Core.neighbours, Set.mem_setOf_eq, Finset.mem_map,
      Function.Embedding.inl_apply, Finset.coe_map, Set.mem_image, Finset.mem_coe,
      Function.Embedding.inr_apply, l31NI, Finset.mem_filter, Finset.mem_univ, true_and,
      Sum.inr.injEq]
    constructor
    · rintro ⟨x, ⟨j, hj, rfl⟩, h⟩; exact ⟨o, ⟨j, hj, h⟩, rfl⟩
    · rintro ⟨o', ⟨j, hj, h⟩, rfl⟩; exact ⟨_, ⟨j, hj, rfl⟩, h⟩

lemma l31_nbO (hbip : IsIOBipartite G) (B : Finset O) :
    AKSSorting.Core.neighbours G (B.map Function.Embedding.inr) =
      (((l31NO G B).map Function.Embedding.inl : Finset (I ⊕ O)) : Set (I ⊕ O)) := by
  ext v
  rcases v with i | o
  · simp only [AKSSorting.Core.neighbours, Set.mem_setOf_eq, Finset.mem_map,
      Function.Embedding.inl_apply, Finset.coe_map, Set.mem_image, Finset.mem_coe,
      Function.Embedding.inr_apply, l31NO, Finset.mem_filter, Finset.mem_univ, true_and,
      Sum.inl.injEq]
    constructor
    · rintro ⟨x, ⟨j, hj, rfl⟩, h⟩; exact ⟨i, ⟨j, hj, h⟩, rfl⟩
    · rintro ⟨o', ⟨j, hj, h⟩, rfl⟩; exact ⟨_, ⟨j, hj, rfl⟩, h⟩
  · simp only [AKSSorting.Core.neighbours, Set.mem_setOf_eq, Finset.mem_map,
      Function.Embedding.inl_apply, Finset.coe_map, Set.mem_image, Finset.mem_coe,
      Function.Embedding.inr_apply]
    constructor
    · rintro ⟨x, ⟨j, hj, rfl⟩, h⟩; exact absurd h (hbip.2 j o)
    · rintro ⟨o, _, h⟩; cases h

end comb

theorem l31_core {I O : Type} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (G : SimpleGraph (I ⊕ O)) [DecidableRel G.Adj] (n d : ℕ) (c : ℝ) (hn : 2 ≤ n)
    (hG : IsStrongExpander G n d c) :
    IsMagnifier G (2 * n) d (c / 16) := by
  obtain ⟨hI, hO, hbip, hdeg, hexp⟩ := hG
  have hexp' : ∀ A : Finset I, (1 + c * (1 - (A.card : ℝ) / n)) * (A.card : ℝ) ≤
      ((l31NI G A).card : ℝ) := by
    intro A
    have := hexp A
    rwa [l31_nbI G hbip, Set.ncard_coe_finset, Finset.card_map] at this
  refine ⟨by simp [Fintype.card_sum, hI, hO]; ring, hdeg, ?_⟩
  intro X hX
  rcases lt_or_ge c 0 with hc | hc0
  · have : c / 16 * (X.card : ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg _)
    exact this.trans (Nat.cast_nonneg _)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  -- c ≤ 3
  have hc3 : c ≤ 3 := by
    obtain ⟨S, -, hS⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset I))
      (n := n / 2) (by rw [Finset.card_univ, hI]; omega)
    have h := hexp' S
    have hle : (l31NI G S).card ≤ n := by
      rw [← hO]; exact Finset.card_le_univ _
    have hle' : ((l31NI G S).card : ℝ) ≤ n := by exact_mod_cast hle
    rw [hS] at h
    have hk1 : 1 ≤ n / 2 := by omega
    have hk2 : n ≤ 3 * (n / 2) := by omega
    have hk3 : n / 2 < n := by omega
    have hk1' : (1 : ℝ) ≤ ((n / 2 : ℕ) : ℝ) := by exact_mod_cast hk1
    have hk2' : (n : ℝ) ≤ 3 * ((n / 2 : ℕ) : ℝ) := by exact_mod_cast hk2
    have hk3' : ((n / 2 : ℕ) : ℝ) < n := by exact_mod_cast hk3
    set k : ℝ := ((n / 2 : ℕ) : ℝ)
    have e : (1 + c * (1 - k / n)) * k = k + c * k * (n - k) / n := by field_simp
    rw [e] at h
    have h' : c * k * (n - k) / n ≤ n - k := by linarith
    rw [div_le_iff₀ hnR] at h'
    have h'' : c * k * (n - k) ≤ n * (n - k) := by linarith
    have h3 : c * k ≤ n := le_of_mul_le_mul_right (by linarith) (by linarith : (0:ℝ) < n - k)
    nlinarith
  set A := X.toLeft
  set B := X.toRight
  have hcard : A.card + B.card = X.card := Finset.card_toLeft_add_card_toRight
  set A' : Finset I := Finset.univ \ l31NO G B
  have hA'card : A'.card = n - (l31NO G B).card := by
    rw [Finset.card_univ_diff, hI]
  have hNOle : (l31NO G B).card ≤ n := by rw [← hI]; exact Finset.card_le_univ _
  have hNA' : l31NI G A' ⊆ Finset.univ \ B := by
    intro o ho
    simp only [l31NI, Finset.mem_filter, Finset.mem_univ, true_and] at ho
    obtain ⟨i, hi, h⟩ := ho
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    intro hoB
    simp only [A', Finset.mem_sdiff, Finset.mem_univ, true_and, l31NO, Finset.mem_filter,
      not_exists, not_and] at hi
    exact hi o hoB h.symm
  have hNA'card : (l31NI G A').card ≤ n - B.card := by
    have := Finset.card_le_card hNA'
    rwa [Finset.card_univ_diff, hO] at this
  have hBn : B.card ≤ n := by rw [← hO]; exact Finset.card_le_univ _
  have h2 := hexp' A'
  rw [hA'card] at h2
  have h2r : (1 + c * (1 - ((n : ℝ) - (l31NO G B).card) / n)) * ((n : ℝ) - (l31NO G B).card)
      ≤ (n : ℝ) - B.card := by
    have := (Nat.cast_le (α := ℝ)).2 hNA'card
    push_cast [hNOle, hBn] at h2 this
    linarith
  have h1 := hexp' A
  -- lower bounds on the target
  have hsub1 : (((l31NI G A \ B).map Function.Embedding.inr : Finset (I ⊕ O)) : Set (I ⊕ O)) ⊆
      AKSSorting.Core.neighbours G X \ (X : Set (I ⊕ O)) := by
    intro v hv
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe, Finset.mem_sdiff,
      Function.Embedding.inr_apply] at hv
    obtain ⟨o, ⟨ho, hoB⟩, rfl⟩ := hv
    simp only [l31NI, Finset.mem_filter, Finset.mem_univ, true_and] at ho
    obtain ⟨i, hi, h⟩ := ho
    refine ⟨⟨Sum.inl i, by simpa [A] using hi, h⟩, ?_⟩
    simpa [B] using hoB
  have hsub2 : (((l31NO G B \ A).map Function.Embedding.inl : Finset (I ⊕ O)) : Set (I ⊕ O)) ⊆
      AKSSorting.Core.neighbours G X \ (X : Set (I ⊕ O)) := by
    intro v hv
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe, Finset.mem_sdiff,
      Function.Embedding.inl_apply] at hv
    obtain ⟨i, ⟨hi, hiA⟩, rfl⟩ := hv
    simp only [l31NO, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨o, ho, h⟩ := hi
    refine ⟨⟨Sum.inr o, by simpa [B] using ho, h⟩, ?_⟩
    simpa [A] using hiA
  have hfin : (AKSSorting.Core.neighbours G X \ (X : Set (I ⊕ O))).Finite := Set.toFinite _
  have hb1 := Set.ncard_le_ncard hsub1 hfin
  have hb2 := Set.ncard_le_ncard hsub2 hfin
  rw [Set.ncard_coe_finset, Finset.card_map] at hb1 hb2
  have hb1' : ((l31NI G A).card : ℝ) - B.card ≤
      ((AKSSorting.Core.neighbours G X \ (X : Set (I ⊕ O))).ncard : ℝ) := by
    have h' : (l31NI G A).card ≤ (l31NI G A \ B).card + B.card := by
      have := Finset.card_le_card_sdiff_add_card (s := l31NI G A) (t := B); omega
    have : ((l31NI G A).card : ℝ) ≤ (l31NI G A \ B).card + B.card := by exact_mod_cast h'
    have : ((l31NI G A \ B).card : ℝ) ≤ ((AKSSorting.Core.neighbours G X \ (X : Set (I ⊕ O))).ncard : ℝ) := by exact_mod_cast hb1
    linarith
  have hb2' : ((l31NO G B).card : ℝ) - A.card ≤
      ((AKSSorting.Core.neighbours G X \ (X : Set (I ⊕ O))).ncard : ℝ) := by
    have h' : (l31NO G B).card ≤ (l31NO G B \ A).card + A.card := by
      have := Finset.card_le_card_sdiff_add_card (s := l31NO G B) (t := A); omega
    have : ((l31NO G B).card : ℝ) ≤ (l31NO G B \ A).card + A.card := by exact_mod_cast h'
    have : ((l31NO G B \ A).card : ℝ) ≤ ((AKSSorting.Core.neighbours G X \ (X : Set (I ⊕ O))).ncard : ℝ) := by exact_mod_cast hb2
    linarith
  have hXc : ((X.card : ℕ) : ℝ) = (A.card : ℝ) + B.card := by rw [← hcard]; push_cast; ring
  have hab : (A.card : ℝ) + B.card ≤ n := by
    have : A.card + B.card ≤ n := by omega
    exact_mod_cast this
  have hNOle' : ((l31NO G B).card : ℝ) ≤ n := by exact_mod_cast hNOle
  rcases l31_arith n A.card B.card (l31NI G A).card (l31NO G B).card c hnR (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) hab hc0 hc3 (Nat.cast_nonneg _) hNOle' h1 h2r with h | h
  · rw [hXc]; linarith
  · rw [hXc]; linarith

end AlonExpanders.Core

open AlonExpanders.Core


theorem solution {I O : Type} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (G : SimpleGraph (I ⊕ O)) [DecidableRel G.Adj] (n d : ℕ) (c : ℝ) (hn : 2 ≤ n)
    (hG : IsStrongExpander G n d c) :
    IsMagnifier G (2 * n) d (c / 16) := by
  exact l31_core G n d c hn hG
