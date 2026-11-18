-- Prove2me | solution 1 for ArcKayles192.PSPACE.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T04:15:48.434585+00:00
-- url     : https://prove2.me/submissions/c9b31c1e-6d74-4aad-99d8-009df7c2d008

import Mathlib
import Definitions.Def_ArcKayles192_PSPACE_Game

open ArcKayles192.PSPACE

namespace AK6

variable {W : Type*} [DecidableEq W]

lemma sg_eq (G : SimpleGraph W) (S : Finset W) :
    sg G S = mex {x | ∃ u v, ∃ _ : u ∈ S ∧ v ∈ S ∧ G.Adj u v, sg G (S \ {u, v}) = x} := by
  rw [sg]

lemma opt_finite (G : SimpleGraph W) (S : Finset W) :
    {x | ∃ u v, ∃ _ : u ∈ S ∧ v ∈ S ∧ G.Adj u v, sg G (S \ {u, v}) = x}.Finite := by
  apply Set.Finite.subset ((S ×ˢ S).finite_toSet.image (fun p : W × W => sg G (S \ {p.1, p.2})))
  rintro x ⟨u, v, ⟨hu, hv, _⟩, rfl⟩
  exact ⟨(u, v), by simp [hu, hv], rfl⟩

lemma sg_char (G : SimpleGraph W) (S : Finset W) :
    (∀ i < sg G S, ∃ u v, u ∈ S ∧ v ∈ S ∧ G.Adj u v ∧ sg G (S \ {u, v}) = i) ∧
    (∀ u v, u ∈ S → v ∈ S → G.Adj u v → sg G (S \ {u, v}) ≠ sg G S) := by
  have hne : ({x | ∃ u v, ∃ _ : u ∈ S ∧ v ∈ S ∧ G.Adj u v, sg G (S \ {u, v}) = x}ᶜ).Nonempty :=
    (opt_finite G S).infinite_compl.nonempty
  have hmex : sg G S = sInf {x | ∃ u v, ∃ _ : u ∈ S ∧ v ∈ S ∧ G.Adj u v, sg G (S \ {u, v}) = x}ᶜ := by
    rw [sg_eq]; rfl
  constructor
  · intro i hi
    rw [hmex] at hi
    by_contra hcon
    have hmem : i ∈ {x | ∃ u v, ∃ _ : u ∈ S ∧ v ∈ S ∧ G.Adj u v, sg G (S \ {u, v}) = x}ᶜ := by
      intro ⟨u, v, ⟨hu, hv, ha⟩, h⟩
      exact hcon ⟨u, v, hu, hv, ha, h⟩
    exact absurd (Nat.sInf_le hmem) (by omega)
  · intro u v hu hv ha h
    have hmem : sg G S ∈ {x | ∃ u v, ∃ _ : u ∈ S ∧ v ∈ S ∧ G.Adj u v, sg G (S \ {u, v}) = x}ᶜ := by
      rw [hmex]; exact Nat.sInf_mem hne
    exact hmem ⟨u, v, ⟨hu, hv, ha⟩, h⟩

lemma sg_eq_of (G : SimpleGraph W) (S : Finset W) (x : ℕ)
    (h1 : ∀ i < x, ∃ u v, u ∈ S ∧ v ∈ S ∧ G.Adj u v ∧ sg G (S \ {u, v}) = i)
    (h2 : ∀ u v, u ∈ S → v ∈ S → G.Adj u v → sg G (S \ {u, v}) ≠ x) : sg G S = x := by
  obtain ⟨c1, c2⟩ := sg_char G S
  rcases lt_trichotomy (sg G S) x with h | h | h
  · obtain ⟨u, v, hu, hv, ha, he⟩ := h1 _ h
    exact absurd he (c2 u v hu hv ha)
  · exact h
  · obtain ⟨u, v, hu, hv, ha, he⟩ := c1 _ h
    exact absurd he (h2 u v hu hv ha)

structure Hyp (H : SimpleGraph W) (S B₁ B₂ I : Finset W) : Prop where
  cover : B₁ ∪ B₂ ∪ I = S
  disj : Disjoint (B₁ ∪ B₂) I
  bic : ∀ u ∈ B₁ ∪ B₂, ∀ w ∈ B₁ ∪ B₂, H.Adj u w ↔ (u ∈ B₁ ↔ w ∈ B₂)
  ind : ∀ u ∈ I, ∀ w ∈ I, ¬H.Adj u w
  pend : ∀ u ∈ B₁ ∪ B₂, ∃ w ∈ I, H.Adj u w ∧ ∀ x ∈ S, H.Adj w x → x = u

lemma Hyp.disjB {H : SimpleGraph W} {S B₁ B₂ I : Finset W} (h : Hyp H S B₁ B₂ I) :
    Disjoint B₁ B₂ := by
  rw [Finset.disjoint_left]
  intro u h1 h2
  have hadj : H.Adj u u :=
    (h.bic u (by simp [h1]) u (by simp [h1])).2 ⟨fun _ => h2, fun _ => h1⟩
  exact H.irrefl hadj

lemma Hyp.move {H : SimpleGraph W} {S B₁ B₂ I : Finset W} (h : Hyp H S B₁ B₂ I)
    {u v : W} (hu : u ∈ S) (hv : v ∈ S) (hadj : H.Adj u v) :
    Hyp H (S \ {u, v}) (B₁ \ {u, v}) (B₂ \ {u, v}) (I \ {u, v}) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← h.cover, ← Finset.union_sdiff_distrib, ← Finset.union_sdiff_distrib]
  · exact Finset.disjoint_of_subset_left (by
      rw [← Finset.union_sdiff_distrib]; exact Finset.sdiff_subset)
      (Finset.disjoint_of_subset_right Finset.sdiff_subset h.disj)
  · intro a ha b hb
    rw [← Finset.union_sdiff_distrib] at ha hb
    rw [Finset.mem_sdiff] at ha hb
    rw [h.bic a ha.1 b hb.1]
    simp only [Finset.mem_sdiff, ha.2, hb.2, not_false_eq_true, and_true]
  · intro a ha b hb
    exact h.ind a (Finset.mem_sdiff.1 ha).1 b (Finset.mem_sdiff.1 hb).1
  · intro x hx
    rw [← Finset.union_sdiff_distrib, Finset.mem_sdiff] at hx
    obtain ⟨w, hwI, hwa, hwo⟩ := h.pend x hx.1
    have hwP : w ∉ ({u, v} : Finset W) := by
      intro hw
      rw [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with hw | hw
      · have hvx : v = x := hwo v hv (by rw [hw]; exact hadj)
        exact hx.2 (Finset.mem_insert_of_mem (Finset.mem_singleton.2 hvx.symm))
      · have hux : u = x := hwo u hu (by rw [hw]; exact hadj.symm)
        exact hx.2 (Finset.mem_insert.2 (Or.inl hux.symm))
    refine ⟨w, Finset.mem_sdiff.2 ⟨hwI, hwP⟩, hwa, ?_⟩
    intro y hy hy'
    exact hwo y (Finset.mem_sdiff.1 hy).1 hy'

lemma card_sd (B : Finset W) (u v : W) (huv : u ≠ v) :
    (B \ {u, v}).card = B.card - (if u ∈ B then 1 else 0) - (if v ∈ B then 1 else 0) := by
  have : B \ {u, v} = (B.erase u).erase v := by
    ext x; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase]; tauto
  rw [this, Finset.card_erase_eq_ite, Finset.card_erase_eq_ite]
  have hv : v ∈ B.erase u ↔ v ∈ B := by simp [Finset.mem_erase, huv.symm]
  by_cases h1 : u ∈ B <;> by_cases h2 : v ∈ B <;> simp [h1, h2, hv] <;> omega


theorem main (H : SimpleGraph W) : ∀ (n : ℕ) (S B₁ B₂ I : Finset W), S.card = n →
    Hyp H S B₁ B₂ I → sg H S = g B₁.card B₂.card := by
  intro n
  induction' n using Nat.strong_induction_on with n ih
  intro S B₁ B₂ I hn hyp
  have IH : ∀ u v, u ∈ S → v ∈ S → H.Adj u v →
      sg H (S \ {u, v}) = g (B₁ \ {u, v}).card (B₂ \ {u, v}).card := by
    intro u v hu hv ha
    exact ih _ (hn ▸ card_sdiff_pair_lt _ hu) _ _ _ _ rfl (hyp.move hu hv ha)
  have hmem : ∀ x ∈ S, x ∈ B₁ ∨ x ∈ B₂ ∨ x ∈ I := by
    intro x hx
    rw [← hyp.cover] at hx
    simp only [Finset.mem_union] at hx
    tauto
  have inS : ∀ x, x ∈ B₁ ∨ x ∈ B₂ ∨ x ∈ I → x ∈ S := by
    intro x hx
    rw [← hyp.cover]
    simp only [Finset.mem_union]
    tauto
  have disj12 := hyp.disjB
  have n12 : ∀ x ∈ B₁, x ∉ B₂ := fun x h1 h2 => Finset.disjoint_left.1 disj12 h1 h2
  have n21 : ∀ x ∈ B₂, x ∉ B₁ := fun x h2 h1 => Finset.disjoint_left.1 disj12 h1 h2
  have n1I : ∀ x ∈ B₁, x ∉ I := fun x h1 hI =>
    Finset.disjoint_left.1 hyp.disj (Finset.mem_union_left _ h1) hI
  have n2I : ∀ x ∈ B₂, x ∉ I := fun x h2 hI =>
    Finset.disjoint_left.1 hyp.disj (Finset.mem_union_right _ h2) hI
  have nI1 : ∀ x ∈ I, x ∉ B₁ := fun x hI h1 => n1I x h1 hI
  have nI2 : ∀ x ∈ I, x ∉ B₂ := fun x hI h2 => n2I x h2 hI
  have pos1 : ∀ x ∈ B₁, 1 ≤ B₁.card := fun x hx => Finset.card_pos.2 ⟨x, hx⟩
  have pos2 : ∀ x ∈ B₂, 1 ≤ B₂.card := fun x hx => Finset.card_pos.2 ⟨x, hx⟩
  have cls : ∀ u v, u ∈ S → v ∈ S → H.Adj u v →
      (1 ≤ B₁.card ∧ 1 ≤ B₂.card ∧ (B₁ \ {u, v}).card = B₁.card - 1 ∧
        (B₂ \ {u, v}).card = B₂.card - 1) ∨
      (1 ≤ B₁.card ∧ (B₁ \ {u, v}).card = B₁.card - 1 ∧ (B₂ \ {u, v}).card = B₂.card) ∨
      (1 ≤ B₂.card ∧ (B₁ \ {u, v}).card = B₁.card ∧ (B₂ \ {u, v}).card = B₂.card - 1) := by
    intro u v hu hv ha
    have hne : u ≠ v := H.ne_of_adj ha
    rw [card_sd B₁ u v hne, card_sd B₂ u v hne]
    rcases hmem u hu with h1 | h2 | h3 <;> rcases hmem v hv with g1 | g2 | g3
    · exfalso
      have := (hyp.bic u (by simp [h1]) v (by simp [g1])).1 ha
      exact n12 v g1 (this.1 h1)
    · have p1 := pos1 u h1
      have p2 := pos2 v g2
      simp only [h1, g2, n12 u h1, n21 v g2, ↓reduceIte, Nat.sub_zero]
      first | omega | tauto
    · have p1 := pos1 u h1
      simp only [h1, n12 u h1, nI1 v g3, nI2 v g3, ↓reduceIte, Nat.sub_zero]
      first | omega | tauto
    · have p1 := pos1 v g1
      have p2 := pos2 u h2
      simp only [h2, g1, n21 u h2, n12 v g1, ↓reduceIte, Nat.sub_zero]
      first | omega | tauto
    · exfalso
      have := (hyp.bic u (by simp [h2]) v (by simp [g2])).1 ha
      exact n21 u h2 (this.2 g2)
    · have p2 := pos2 u h2
      simp only [h2, n21 u h2, nI1 v g3, nI2 v g3, ↓reduceIte, Nat.sub_zero]
      first | omega | tauto
    · have p1 := pos1 v g1
      simp only [g1, nI1 u h3, nI2 u h3, n12 v g1, ↓reduceIte, Nat.sub_zero]
      first | omega | tauto
    · have p2 := pos2 v g2
      simp only [g2, nI1 u h3, nI2 u h3, n21 v g2, ↓reduceIte, Nat.sub_zero]
      first | omega | tauto
    · exact absurd ha (hyp.ind u h3 v g3)
  apply sg_eq_of
  · intro i hi
    have key : (1 ≤ B₁.card ∧ 1 ≤ B₂.card ∧ g (B₁.card - 1) (B₂.card - 1) = i) ∨
        (1 ≤ B₁.card ∧ g (B₁.card - 1) B₂.card = i) ∨
        (1 ≤ B₂.card ∧ g B₁.card (B₂.card - 1) = i) := by
      simp only [g] at hi ⊢
      omega
    rcases key with ⟨p1, p2, hg⟩ | ⟨p1, hg⟩ | ⟨p2, hg⟩
    · obtain ⟨u, hu⟩ := Finset.card_pos.1 (by omega : 0 < B₁.card)
      obtain ⟨v, hv⟩ := Finset.card_pos.1 (by omega : 0 < B₂.card)
      have ha : H.Adj u v :=
        (hyp.bic u (by simp [hu]) v (by simp [hv])).2 ⟨fun _ => hv, fun _ => hu⟩
      refine ⟨u, v, inS u (Or.inl hu), inS v (Or.inr (Or.inl hv)), ha, ?_⟩
      rw [IH u v (inS u (Or.inl hu)) (inS v (Or.inr (Or.inl hv))) ha,
        card_sd B₁ u v (H.ne_of_adj ha), card_sd B₂ u v (H.ne_of_adj ha)]
      simp only [hu, hv, n12 u hu, n21 v hv, ↓reduceIte, Nat.sub_zero]
      exact hg
    · obtain ⟨u, hu⟩ := Finset.card_pos.1 (by omega : 0 < B₁.card)
      obtain ⟨w, hwI, hwa, hwo⟩ := hyp.pend u (by simp [hu])
      refine ⟨u, w, inS u (Or.inl hu), inS w (Or.inr (Or.inr hwI)), hwa, ?_⟩
      rw [IH u w (inS u (Or.inl hu)) (inS w (Or.inr (Or.inr hwI))) hwa,
        card_sd B₁ u w (H.ne_of_adj hwa), card_sd B₂ u w (H.ne_of_adj hwa)]
      simp only [hu, n12 u hu, nI1 w hwI, nI2 w hwI, ↓reduceIte, Nat.sub_zero]
      exact hg
    · obtain ⟨u, hu⟩ := Finset.card_pos.1 (by omega : 0 < B₂.card)
      obtain ⟨w, hwI, hwa, hwo⟩ := hyp.pend u (by simp [hu])
      refine ⟨u, w, inS u (Or.inr (Or.inl hu)), inS w (Or.inr (Or.inr hwI)), hwa, ?_⟩
      rw [IH u w (inS u (Or.inr (Or.inl hu))) (inS w (Or.inr (Or.inr hwI))) hwa,
        card_sd B₁ u w (H.ne_of_adj hwa), card_sd B₂ u w (H.ne_of_adj hwa)]
      simp only [hu, n21 u hu, nI1 w hwI, nI2 w hwI, ↓reduceIte, Nat.sub_zero]
      exact hg
  · intro u v hu hv ha
    rw [IH u v hu hv ha]
    rcases cls u v hu hv ha with ⟨p, q, e1, e2⟩ | ⟨p, e1, e2⟩ | ⟨p, e1, e2⟩ <;>
      (rw [e1, e2]; simp only [g]; omega)

end AK6

theorem solution {W : Type*} [DecidableEq W] (H : SimpleGraph W) (S B₁ B₂ I : Finset W)
    (hcover : B₁ ∪ B₂ ∪ I = S) (hdisj : Disjoint (B₁ ∪ B₂) I)
    (hbic : ∀ u ∈ B₁ ∪ B₂, ∀ w ∈ B₁ ∪ B₂, H.Adj u w ↔ (u ∈ B₁ ↔ w ∈ B₂))
    (hind : ∀ u ∈ I, ∀ w ∈ I, ¬ H.Adj u w)
    (hpend : ∀ u ∈ B₁ ∪ B₂, ∃ w ∈ I, H.Adj u w ∧ ∀ x ∈ S, H.Adj w x → x = u) :
    sg H S = g B₁.card B₂.card :=
  AK6.main H S.card S B₁ B₂ I rfl ⟨hcover, hdisj, hbic, hind, hpend⟩
