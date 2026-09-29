-- Prove2me | solution 1 for AssignmentGame.CoreCorners.core_corners
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-28T19:27:44.491829+00:00
-- url     : https://prove2.me/submissions/3b36c0b9-6c91-4cb4-bebc-e0c894c46bd7

import Mathlib
import Definitions.Def_AssignmentGame_CoreCorners_Game

set_option autoImplicit false

/-! ## Basic facts about `worth` and matchings -/

open AssignmentGame.CoreCorners in
theorem ag1171_mem_matchings {M N : Type*} {A : Finset M} {B : Finset N} {P : Finset (M × N)}
    (h : IsMatching A B P) : P ∈ matchings A B := by
  classical
  unfold matchings
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨h.1, h⟩

open AssignmentGame.CoreCorners in
theorem ag1171_isMatching_of_mem {M N : Type*} {A : Finset M} {B : Finset N} {P : Finset (M × N)}
    (h : P ∈ matchings A B) : IsMatching A B P := by
  classical
  unfold matchings at h
  rw [Finset.mem_filter] at h
  exact h.2

open AssignmentGame.CoreCorners in
theorem ag1171_le_worth {M N : Type*} (a : M → N → ℝ) {A : Finset M} {B : Finset N}
    {P : Finset (M × N)} (h : IsMatching A B P) :
    ∑ p ∈ P, a p.1 p.2 ≤ worth a A B := by
  unfold worth
  exact Finset.le_sup' (fun P => ∑ p ∈ P, a p.1 p.2) (ag1171_mem_matchings h)

open AssignmentGame.CoreCorners in
theorem ag1171_exists_opt {M N : Type*} (a : M → N → ℝ) (A : Finset M) (B : Finset N) :
    ∃ P : Finset (M × N), IsMatching A B P ∧ worth a A B = ∑ p ∈ P, a p.1 p.2 := by
  unfold worth
  obtain ⟨P, hP, heq⟩ := Finset.exists_mem_eq_sup' (⟨∅, empty_mem_matchings A B⟩ :
    (matchings A B).Nonempty) (fun P => ∑ p ∈ P, a p.1 p.2)
  exact ⟨P, ag1171_isMatching_of_mem hP, heq⟩

open AssignmentGame.CoreCorners in
theorem ag1171_worth_nonneg {M N : Type*} (a : M → N → ℝ) (A : Finset M) (B : Finset N) :
    0 ≤ worth a A B := by
  have h : IsMatching A B (∅ : Finset (M × N)) := by
    refine ⟨by simp, ?_, ?_⟩ <;> simp
  simpa using ag1171_le_worth a h

open AssignmentGame.CoreCorners in
theorem ag1171_worth_le {M N : Type*} (a : M → N → ℝ) (A : Finset M) (B : Finset N) (c : ℝ)
    (h : ∀ P : Finset (M × N), IsMatching A B P → ∑ p ∈ P, a p.1 p.2 ≤ c) :
    worth a A B ≤ c := by
  obtain ⟨P, hP, hw⟩ := ag1171_exists_opt a A B
  rw [hw]
  exact h P hP

/-- dual feasibility -/
def ag1171_DF {M N : Type*} (a : M → N → ℝ) (u : M → ℝ) (v : N → ℝ) : Prop :=
  (∀ i, 0 ≤ u i) ∧ (∀ j, 0 ≤ v j) ∧ ∀ i j, a i j ≤ u i + v j

open AssignmentGame.CoreCorners in
theorem ag1171_matching_sum_le {M N : Type*} (a : M → N → ℝ) (u : M → ℝ) (v : N → ℝ)
    (h : ag1171_DF a u v) {A : Finset M} {B : Finset N} {P : Finset (M × N)}
    (hP : IsMatching A B P) :
    ∑ p ∈ P, a p.1 p.2 ≤ ∑ i ∈ A, u i + ∑ j ∈ B, v j := by
  classical
  obtain ⟨hsub, h1, h2⟩ := hP
  obtain ⟨hu, hv, hab⟩ := h
  have e1 : ∑ p ∈ P, u p.1 = ∑ i ∈ P.image Prod.fst, u i := by
    rw [Finset.sum_image]
    intro p hp q hq hpq
    exact h1 p hp q hq hpq
  have e2 : ∑ p ∈ P, v p.2 = ∑ j ∈ P.image Prod.snd, v j := by
    rw [Finset.sum_image]
    intro p hp q hq hpq
    exact h2 p hp q hq hpq
  have s1 : ∑ i ∈ P.image Prod.fst, u i ≤ ∑ i ∈ A, u i := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hi
      exact (Finset.mem_product.1 (hsub hp)).1
    · intro i _ _; exact hu i
  have s2 : ∑ j ∈ P.image Prod.snd, v j ≤ ∑ j ∈ B, v j := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro j hj
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hj
      exact (Finset.mem_product.1 (hsub hp)).2
    · intro j _ _; exact hv j
  calc ∑ p ∈ P, a p.1 p.2 ≤ ∑ p ∈ P, (u p.1 + v p.2) :=
        Finset.sum_le_sum fun p _ => hab p.1 p.2
    _ = ∑ p ∈ P, u p.1 + ∑ p ∈ P, v p.2 := Finset.sum_add_distrib
    _ ≤ ∑ i ∈ A, u i + ∑ j ∈ B, v j := by rw [e1, e2]; exact add_le_add s1 s2

open AssignmentGame.CoreCorners in
theorem ag1171_core_iff {M N : Type*} [Fintype M] [Fintype N] (a : M → N → ℝ)
    (u : M → ℝ) (v : N → ℝ) :
    (u, v) ∈ core a ↔ ag1171_DF a u v ∧ ∑ i, u i + ∑ j, v j = worth a Finset.univ Finset.univ := by
  classical
  constructor
  · rintro ⟨hsum, hcore⟩
    refine ⟨⟨?_, ?_, ?_⟩, hsum⟩
    · intro i
      have := hcore {i} ∅
      have h0 := ag1171_worth_nonneg a {i} (∅ : Finset N)
      simp only [Finset.sum_singleton, Finset.sum_empty, add_zero] at this
      linarith
    · intro j
      have := hcore ∅ {j}
      have h0 := ag1171_worth_nonneg a (∅ : Finset M) {j}
      simp only [Finset.sum_singleton, Finset.sum_empty, zero_add] at this
      linarith
    · intro i j
      have := hcore {i} {j}
      have h1 : IsMatching ({i} : Finset M) ({j} : Finset N) {(i, j)} := by
        refine ⟨by simp, ?_, ?_⟩ <;> simp
      have h2 := ag1171_le_worth a h1
      simp only [Finset.sum_singleton] at this h2
      linarith
  · rintro ⟨hdf, hsum⟩
    refine ⟨hsum, fun A B => ?_⟩
    apply ag1171_worth_le
    intro P hP
    exact ag1171_matching_sum_le a u v hdf hP

/-! ## Hall / Mendelsohn-Dulmage -/


open Classical in
/-- Mendelsohn–Dulmage type lemma from Hall. -/
theorem ag1171_md {M N : Type*} [Fintype M] [Fintype N] (E : M → N → Prop) (X : Finset M)
    (Y : Finset N)
    (hX : ∀ S ⊆ X, S.card ≤ (Finset.univ.filter (fun j => ∃ i ∈ S, E i j)).card)
    (hY : ∀ Q ⊆ Y, Q.card ≤ (Finset.univ.filter (fun i => ∃ j ∈ Q, E i j)).card) :
    ∃ P : Finset (M × N), (∀ p ∈ P, E p.1 p.2) ∧ (∀ p ∈ P, ∀ q ∈ P, p.1 = q.1 → p = q) ∧
      (∀ p ∈ P, ∀ q ∈ P, p.2 = q.2 → p = q) ∧ (∀ i ∈ X, ∃ p ∈ P, p.1 = i) ∧
      (∀ j ∈ Y, ∃ p ∈ P, p.2 = j) := by
  classical
  let Adj : M ⊕ N → N ⊕ M → Prop := fun x y =>
    match x, y with
    | Sum.inl i, Sum.inl j => E i j
    | Sum.inl i, Sum.inr i' => i' = i ∧ i ∉ X
    | Sum.inr j, Sum.inl j' => j' = j ∧ j ∉ Y
    | Sum.inr _, Sum.inr _ => True
  let t : M ⊕ N → Finset (N ⊕ M) := fun x => Finset.univ.filter (Adj x)
  have hmem : ∀ x y, y ∈ t x ↔ Adj x y := fun x y => by simp [t]
  have hall : ∀ s : Finset (M ⊕ N), s.card ≤ (s.biUnion t).card := by
    intro s
    have hcard := Finset.card_toLeft_add_card_toRight (u := s)
    have hS : ∀ i, i ∈ s.toLeft ↔ Sum.inl i ∈ s := fun i => Finset.mem_toLeft
    have hQ : ∀ j, j ∈ s.toRight ↔ Sum.inr j ∈ s := fun j => Finset.mem_toRight
    generalize s.toLeft = S at hcard hS
    generalize s.toRight = Q at hcard hQ
    by_cases hQe : Q = ∅
    · -- only sellers
      have hQc : Q.card = 0 := by rw [hQe]; rfl
      let S1 := S.filter (fun i => i ∈ X)
      let S2 := S.filter (fun i => i ∉ X)
      let Nb := Finset.univ.filter (fun j => ∃ i ∈ S1, E i j)
      have h1 : S1.card ≤ Nb.card := hX S1 (fun i hi => (Finset.mem_filter.1 hi).2)
      have hsplit : S1.card + S2.card = S.card := Finset.card_filter_add_card_filter_not _
      have hsub : Nb.map Function.Embedding.inl ∪ S2.map Function.Embedding.inr ⊆ s.biUnion t := by
        intro y hy
        rcases Finset.mem_union.1 hy with hy | hy
        · obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hy
          obtain ⟨i, hi, hij⟩ := (Finset.mem_filter.1 hj).2
          have hi' := (Finset.mem_filter.1 hi)
          refine Finset.mem_biUnion.2 ⟨Sum.inl i, ?_, ?_⟩
          · exact (hS i).1 hi'.1
          · rw [hmem]; exact hij
        · obtain ⟨i, hi, rfl⟩ := Finset.mem_map.1 hy
          have hi' := (Finset.mem_filter.1 hi)
          refine Finset.mem_biUnion.2 ⟨Sum.inl i, ?_, ?_⟩
          · exact (hS i).1 hi'.1
          · rw [hmem]; exact ⟨rfl, hi'.2⟩
      have hdisj : Disjoint (Nb.map Function.Embedding.inl) (S2.map Function.Embedding.inr) := by
        rw [Finset.disjoint_left]
        intro y hy hy'
        obtain ⟨j, _, rfl⟩ := Finset.mem_map.1 hy
        obtain ⟨i, _, hh⟩ := Finset.mem_map.1 hy'
        exact Sum.inr_ne_inl hh
      have hc := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint hdisj, Finset.card_map, Finset.card_map] at hc
      omega
    · -- some dummy seller present
      obtain ⟨j0, hj0⟩ := Finset.nonempty_iff_ne_empty.2 hQe
      let NS := Finset.univ.filter (fun j => ∃ i ∈ S, E i j)
      let U := NS ∪ Q.filter (fun j => j ∉ Y)
      let Q1 := Q.filter (fun j => j ∈ Y ∧ j ∉ NS)
      let NQ := Finset.univ.filter (fun i => ∃ j ∈ Q1, E i j)
      have h1 : Q1.card ≤ NQ.card := hY Q1 (fun j hj => (Finset.mem_filter.1 hj).2.1)
      have hdisj0 : Disjoint S NQ := by
        rw [Finset.disjoint_left]
        intro i hi hi'
        obtain ⟨j, hj, hij⟩ := (Finset.mem_filter.1 hi').2
        have hj' := (Finset.mem_filter.1 hj).2
        apply hj'.2
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, i, hi, hij⟩
      have h2 : S.card + NQ.card ≤ Fintype.card M := by
        rw [← Finset.card_union_of_disjoint hdisj0]
        exact Finset.card_le_univ _
      have hQsub : Q ⊆ Q1 ∪ U := by
        intro j hj
        by_cases hY' : j ∈ Y
        · by_cases hNS : j ∈ NS
          · exact Finset.mem_union.2 (Or.inr (Finset.mem_union.2 (Or.inl hNS)))
          · exact Finset.mem_union.2 (Or.inl (Finset.mem_filter.2 ⟨hj, hY', hNS⟩))
        · exact Finset.mem_union.2 (Or.inr (Finset.mem_union.2 (Or.inr (Finset.mem_filter.2 ⟨hj, hY'⟩))))
      have h3 : Q.card ≤ Q1.card + U.card :=
        (Finset.card_le_card hQsub).trans (Finset.card_union_le _ _)
      have hsub : (Finset.univ : Finset M).map Function.Embedding.inr ∪ U.map Function.Embedding.inl ⊆
          s.biUnion t := by
        intro y hy
        rcases Finset.mem_union.1 hy with hy | hy
        · obtain ⟨i, _, rfl⟩ := Finset.mem_map.1 hy
          refine Finset.mem_biUnion.2 ⟨Sum.inr j0, ?_, ?_⟩
          · exact (hQ j0).1 hj0
          · rw [hmem]; trivial
        · obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hy
          rcases Finset.mem_union.1 hj with hj | hj
          · obtain ⟨i, hi, hij⟩ := (Finset.mem_filter.1 hj).2
            refine Finset.mem_biUnion.2 ⟨Sum.inl i, ?_, ?_⟩
            · exact (hS i).1 hi
            · rw [hmem]; exact hij
          · have hj' := Finset.mem_filter.1 hj
            refine Finset.mem_biUnion.2 ⟨Sum.inr j, ?_, ?_⟩
            · exact (hQ j).1 hj'.1
            · rw [hmem]; exact ⟨rfl, hj'.2⟩
      have hdisj : Disjoint ((Finset.univ : Finset M).map Function.Embedding.inr)
          (U.map Function.Embedding.inl) := by
        rw [Finset.disjoint_left]
        intro y hy hy'
        obtain ⟨j, _, rfl⟩ := Finset.mem_map.1 hy'
        obtain ⟨i, _, hh⟩ := Finset.mem_map.1 hy
        exact Sum.inr_ne_inl hh
      have hc := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint hdisj, Finset.card_map, Finset.card_map,
        Finset.card_univ] at hc
      omega
  obtain ⟨f, hfinj, hf⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).1 hall
  have hfbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hfinj, ?_⟩
    simp [Fintype.card_sum, add_comm]
  refine ⟨Finset.univ.filter (fun p : M × N => f (Sum.inl p.1) = Sum.inl p.2), ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    have h1 := (Finset.mem_filter.1 hp).2
    have h2 := (hmem _ _).1 (hf (Sum.inl p.1))
    rw [h1] at h2
    exact h2
  · intro p hp q hq hpq
    have h1 := (Finset.mem_filter.1 hp).2
    have h2 := (Finset.mem_filter.1 hq).2
    rw [hpq] at h1
    rw [h1] at h2
    exact Prod.ext hpq (Sum.inl_injective h2)
  · intro p hp q hq hpq
    have h1 := (Finset.mem_filter.1 hp).2
    have h2 := (Finset.mem_filter.1 hq).2
    have := hfinj (h1.trans ((congrArg Sum.inl hpq).trans h2.symm))
    exact Prod.ext (Sum.inl_injective this) hpq
  · intro i hi
    have h2 := (hmem _ _).1 (hf (Sum.inl i))
    rcases hfi : f (Sum.inl i) with j | i'
    · exact ⟨(i, j), Finset.mem_filter.2 ⟨Finset.mem_univ _, hfi⟩, rfl⟩
    · rw [hfi] at h2
      exact absurd hi h2.2
  · intro j hj
    obtain ⟨x, hx⟩ := hfbij.2 (Sum.inl j)
    rcases x with i | j'
    · exact ⟨(i, j), Finset.mem_filter.2 ⟨Finset.mem_univ _, hx⟩, rfl⟩
    · have h2 := (hmem _ _).1 (hf (Sum.inr j'))
      rw [hx] at h2
      have : j = j' := h2.1
      subst this
      exact absurd hj h2.2

/-! ## Perturbation -/

open Classical in
/-- Perturbation: a dual-optimal vector has the Hall property on the positive sellers. -/
theorem ag1171_hall_side {M N : Type*} [Fintype M] [Fintype N] (a : M → N → ℝ) (u : M → ℝ)
    (v : N → ℝ) (hdf : ag1171_DF a u v)
    (hmin : ∀ (u' : M → ℝ) (v' : N → ℝ), ag1171_DF a u' v' →
      ∑ i, u i + ∑ j, v j ≤ ∑ i, u' i + ∑ j, v' j)
    (S : Finset M) (hS : ∀ i ∈ S, 0 < u i) :
    S.card ≤ (Finset.univ.filter (fun j => ∃ i ∈ S, u i + v j = a i j)).card := by
  by_contra hlt
  rw [not_le] at hlt
  set Nb := Finset.univ.filter (fun j => ∃ i ∈ S, u i + v j = a i j) with hNb
  have hne : (S ×ˢ (Finset.univ : Finset (Option N))).Nonempty := by
    have : 0 < S.card := lt_of_le_of_lt (Nat.zero_le _) hlt
    obtain ⟨i, hi⟩ := Finset.card_pos.1 this
    exact ⟨(i, none), Finset.mem_product.2 ⟨hi, Finset.mem_univ _⟩⟩
  let g : M × Option N → ℝ := fun x =>
    match x.2 with
    | none => u x.1
    | some j => if j ∈ Nb then u x.1 else u x.1 + v j - a x.1 j
  obtain ⟨x0, hx0, hmin0⟩ := Finset.exists_min_image (S ×ˢ (Finset.univ : Finset (Option N))) g hne
  set ε := g x0 with hε
  have hslack : ∀ i ∈ S, ∀ j, j ∉ Nb → 0 < u i + v j - a i j := by
    intro i hi j hj
    have h1 := hdf.2.2 i j
    have h2 : u i + v j ≠ a i j := fun h => hj (Finset.mem_filter.2 ⟨Finset.mem_univ _, i, hi, h⟩)
    have := lt_of_le_of_ne h1 (Ne.symm h2)
    linarith
  have hεpos : 0 < ε := by
    obtain ⟨i0, j0⟩ := x0
    have hi0 : i0 ∈ S := (Finset.mem_product.1 hx0).1
    rw [hε]
    rcases j0 with _ | j0
    · exact hS i0 hi0
    · simp only [g]
      split_ifs with h
      · exact hS i0 hi0
      · exact hslack i0 hi0 j0 h
  have hε1 : ∀ i ∈ S, ε ≤ u i := by
    intro i hi
    exact hmin0 (i, none) (Finset.mem_product.2 ⟨hi, Finset.mem_univ _⟩)
  have hε2 : ∀ i ∈ S, ∀ j, j ∉ Nb → ε ≤ u i + v j - a i j := by
    intro i hi j hj
    have := hmin0 (i, some j) (Finset.mem_product.2 ⟨hi, Finset.mem_univ _⟩)
    simpa [g, hj] using this
  let u' : M → ℝ := fun i => u i - if i ∈ S then ε else 0
  let v' : N → ℝ := fun j => v j + if j ∈ Nb then ε else 0
  have hdf' : ag1171_DF a u' v' := by
    refine ⟨?_, ?_, ?_⟩
    · intro i
      simp only [u']
      split_ifs with h
      · linarith [hε1 i h]
      · linarith [hdf.1 i]
    · intro j
      simp only [v']
      split_ifs
      · linarith [hdf.2.1 j]
      · linarith [hdf.2.1 j]
    · intro i j
      simp only [u', v']
      have hab := hdf.2.2 i j
      by_cases hi : i ∈ S
      · by_cases hj : j ∈ Nb
        · simp only [hi, hj, if_true]; linarith
        · have := hε2 i hi j hj
          simp only [hi, hj, if_true, if_false]; linarith
      · by_cases hj : j ∈ Nb
        · simp only [hi, hj, if_true, if_false]; linarith
        · simp only [hi, hj, if_false]; linarith
  have hobj := hmin u' v' hdf'
  have e1 : ∑ i, u' i = ∑ i, u i - ε * S.card := by
    simp only [u']
    rw [Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
      nsmul_eq_mul]
    ring
  have e2 : ∑ j, v' j = ∑ j, v j + ε * Nb.card := by
    simp only [v']
    rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
      nsmul_eq_mul]
    ring
  rw [e1, e2] at hobj
  have hlt' : (Nb.card : ℝ) < S.card := by exact_mod_cast hlt
  nlinarith

/-! ## Existence of a dual optimum -/

theorem ag1171_exists_min {M N : Type*} [Fintype M] [Fintype N] (a : M → N → ℝ)
    (ha : ∀ i j, 0 ≤ a i j) :
    ∃ (u : M → ℝ) (v : N → ℝ), ag1171_DF a u v ∧
      ∀ (u' : M → ℝ) (v' : N → ℝ), ag1171_DF a u' v' →
        ∑ i, u i + ∑ j, v j ≤ ∑ i, u' i + ∑ j, v' j := by
  classical
  let obj : (M → ℝ) × (N → ℝ) → ℝ := fun p => ∑ i, p.1 i + ∑ j, p.2 j
  have hobj : Continuous obj := by
    simp only [obj]; fun_prop
  let p0 : (M → ℝ) × (N → ℝ) := (fun i => ∑ j, a i j, fun _ => 0)
  have hp0 : ag1171_DF a p0.1 p0.2 := by
    refine ⟨fun i => Finset.sum_nonneg (fun j _ => ha i j), fun _ => le_rfl, fun i j => ?_⟩
    simp only [p0, add_zero]
    exact Finset.single_le_sum (f := fun j => a i j) (fun j _ => ha i j) (Finset.mem_univ j)
  set C := obj p0 with hC
  let K : Set ((M → ℝ) × (N → ℝ)) := {p | ag1171_DF a p.1 p.2 ∧ obj p ≤ C}
  have hKc : IsCompact K := by
    have hbox : IsCompact ((Set.univ.pi fun _ : M => Set.Icc (0:ℝ) C) ×ˢ
        (Set.univ.pi fun _ : N => Set.Icc (0:ℝ) C)) :=
      (isCompact_univ_pi fun _ => isCompact_Icc).prod (isCompact_univ_pi fun _ => isCompact_Icc)
    refine hbox.of_isClosed_subset ?_ ?_
    · have c1 : IsClosed {p : (M → ℝ) × (N → ℝ) | ∀ i, 0 ≤ p.1 i} := by
        simp only [Set.ofPred_forall]
        exact isClosed_iInter fun i => isClosed_le continuous_const (by fun_prop)
      have c2 : IsClosed {p : (M → ℝ) × (N → ℝ) | ∀ j, 0 ≤ p.2 j} := by
        simp only [Set.ofPred_forall]
        exact isClosed_iInter fun j => isClosed_le continuous_const (by fun_prop)
      have c3 : IsClosed {p : (M → ℝ) × (N → ℝ) | ∀ i j, a i j ≤ p.1 i + p.2 j} := by
        simp only [Set.ofPred_forall]
        exact isClosed_iInter fun i => isClosed_iInter fun j =>
          isClosed_le continuous_const (by fun_prop)
      have c4 : IsClosed {p : (M → ℝ) × (N → ℝ) | obj p ≤ C} :=
        isClosed_le hobj continuous_const
      have e : K = (({p : (M → ℝ) × (N → ℝ) | ∀ i, 0 ≤ p.1 i} ∩ {p | ∀ j, 0 ≤ p.2 j}) ∩
          {p | ∀ i j, a i j ≤ p.1 i + p.2 j}) ∩ {p | obj p ≤ C} := by
        ext p
        simp only [K, ag1171_DF, Set.mem_ofPred_eq, Set.mem_inter_iff, and_assoc]
      rw [e]
      exact ((c1.inter c2).inter c3).inter c4
    · intro p hp
      obtain ⟨⟨hu, hv, -⟩, hle⟩ := hp
      have h2 : 0 ≤ ∑ k, p.2 k := Finset.sum_nonneg (fun k _ => hv k)
      have h2' : 0 ≤ ∑ k, p.1 k := Finset.sum_nonneg (fun k _ => hu k)
      have hop : obj p = ∑ i, p.1 i + ∑ j, p.2 j := rfl
      refine ⟨fun i _ => ⟨hu i, ?_⟩, fun j _ => ⟨hv j, ?_⟩⟩
      · have h1 : p.1 i ≤ ∑ k, p.1 k :=
          Finset.single_le_sum (f := fun k => p.1 k) (fun k _ => hu k) (Finset.mem_univ i)
        linarith
      · have h1 : p.2 j ≤ ∑ k, p.2 k :=
          Finset.single_le_sum (f := fun k => p.2 k) (fun k _ => hv k) (Finset.mem_univ j)
        linarith
  obtain ⟨p, hpK, hpmin⟩ := hKc.exists_isMinOn ⟨p0, hp0, le_rfl⟩ hobj.continuousOn
  refine ⟨p.1, p.2, hpK.1, fun u' v' hq => ?_⟩
  by_cases hqC : obj (u', v') ≤ C
  · exact isMinOn_iff.1 hpmin (u', v') (show (u', v') ∈ K from ⟨hq, hqC⟩)
  · have h1 := hpK.2
    have h2 := not_le.1 hqC
    show obj p ≤ obj (u', v')
    linarith

/-! ## Nonemptiness of the core (Egerváry) -/

open AssignmentGame.CoreCorners in
theorem ag1171_core_nonempty {M N : Type*} [Fintype M] [Fintype N] (a : M → N → ℝ)
    (ha : ∀ i j, 0 ≤ a i j) : ∃ (u : M → ℝ) (v : N → ℝ), (u, v) ∈ core a := by
  classical
  obtain ⟨u, v, hdf, hmin⟩ := ag1171_exists_min a ha
  have hX : ∀ S ⊆ (Finset.univ.filter (fun i => 0 < u i)), S.card ≤
      (Finset.univ.filter (fun j => ∃ i ∈ S, (fun i j => u i + v j = a i j) i j)).card := by
    intro S hS
    convert ag1171_hall_side a u v hdf hmin S (fun i hi => (Finset.mem_filter.1 (hS hi)).2)
      using 3
  have hY : ∀ Q ⊆ (Finset.univ.filter (fun j => 0 < v j)), Q.card ≤
      (Finset.univ.filter (fun i => ∃ j ∈ Q, (fun i j => u i + v j = a i j) i j)).card := by
    intro Q hQ
    have hdf' : ag1171_DF (fun j i => a i j) v u :=
      ⟨hdf.2.1, hdf.1, fun j i => by have := hdf.2.2 i j; linarith⟩
    have hmin' : ∀ (v' : N → ℝ) (u' : M → ℝ), ag1171_DF (fun j i => a i j) v' u' →
        ∑ j, v j + ∑ i, u i ≤ ∑ j, v' j + ∑ i, u' i := by
      intro v' u' h
      have := hmin u' v' ⟨h.2.1, h.1, fun i j => by have := h.2.2 j i; linarith⟩
      linarith
    convert ag1171_hall_side (fun j i => a i j) v u hdf' hmin' Q
      (fun j hj => (Finset.mem_filter.1 (hQ hj)).2) using 3
    simp only [add_comm]
  obtain ⟨P, hE, h1, h2, hcx, hcy⟩ := ag1171_md (fun i j => u i + v j = a i j) _ _ hX hY
  have hP : IsMatching (Finset.univ : Finset M) (Finset.univ : Finset N) P :=
    ⟨fun p _ => Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_univ _⟩, h1, h2⟩
  have hsumu : ∑ i, u i = ∑ i ∈ P.image Prod.fst, u i := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    by_contra hne
    have : 0 < u i := lt_of_le_of_ne (hdf.1 i) (Ne.symm hne)
    obtain ⟨p, hp, hp1⟩ := hcx i (Finset.mem_filter.2 ⟨Finset.mem_univ _, this⟩)
    exact hi (Finset.mem_image.2 ⟨p, hp, hp1⟩)
  have hsumv : ∑ j, v j = ∑ j ∈ P.image Prod.snd, v j := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    by_contra hne
    have : 0 < v j := lt_of_le_of_ne (hdf.2.1 j) (Ne.symm hne)
    obtain ⟨p, hp, hp1⟩ := hcy j (Finset.mem_filter.2 ⟨Finset.mem_univ _, this⟩)
    exact hj (Finset.mem_image.2 ⟨p, hp, hp1⟩)
  have e1 : ∑ p ∈ P, u p.1 = ∑ i ∈ P.image Prod.fst, u i := by
    rw [Finset.sum_image]
    intro p hp q hq hpq
    exact h1 p hp q hq hpq
  have e2 : ∑ p ∈ P, v p.2 = ∑ j ∈ P.image Prod.snd, v j := by
    rw [Finset.sum_image]
    intro p hp q hq hpq
    exact h2 p hp q hq hpq
  have hPsum : ∑ p ∈ P, a p.1 p.2 = ∑ i, u i + ∑ j, v j := by
    calc ∑ p ∈ P, a p.1 p.2 = ∑ p ∈ P, (u p.1 + v p.2) :=
          Finset.sum_congr rfl fun p hp => (hE p hp).symm
      _ = ∑ p ∈ P, u p.1 + ∑ p ∈ P, v p.2 := Finset.sum_add_distrib
      _ = ∑ i, u i + ∑ j, v j := by rw [e1, e2, hsumu, hsumv]
  have hge : ∑ i, u i + ∑ j, v j ≤ worth a Finset.univ Finset.univ := by
    rw [← hPsum]; exact ag1171_le_worth a hP
  have hle : worth a Finset.univ Finset.univ ≤ ∑ i, u i + ∑ j, v j := by
    apply ag1171_worth_le
    intro P' hP'
    exact ag1171_matching_sum_le a u v hdf hP'
  exact ⟨u, v, (ag1171_core_iff a u v).2 ⟨hdf, le_antisymm hge hle⟩⟩

/-! ## Lattice structure of the core -/

open AssignmentGame.CoreCorners in
theorem ag1171_cs {M N : Type*} [Fintype M] [Fintype N] (a : M → N → ℝ) {u : M → ℝ} {v : N → ℝ}
    (h : (u, v) ∈ core a) {P : Finset (M × N)}
    (hP : IsMatching (Finset.univ : Finset M) (Finset.univ : Finset N) P)
    (hw : worth a Finset.univ Finset.univ = ∑ p ∈ P, a p.1 p.2) :
    (∀ p ∈ P, u p.1 + v p.2 = a p.1 p.2) ∧ (∀ i, (∀ p ∈ P, p.1 ≠ i) → u i = 0) ∧
      (∀ j, (∀ p ∈ P, p.2 ≠ j) → v j = 0) := by
  classical
  obtain ⟨⟨hu, hv, hab⟩, hsum⟩ := (ag1171_core_iff a u v).1 h
  obtain ⟨-, h1, h2⟩ := hP
  have e1 : ∑ p ∈ P, u p.1 = ∑ i ∈ P.image Prod.fst, u i := by
    rw [Finset.sum_image]
    intro p hp q hq hpq
    exact h1 p hp q hq hpq
  have e2 : ∑ p ∈ P, v p.2 = ∑ j ∈ P.image Prod.snd, v j := by
    rw [Finset.sum_image]
    intro p hp q hq hpq
    exact h2 p hp q hq hpq
  have hF' : ∑ i ∈ P.image Prod.fst, u i + ∑ i ∈ (P.image Prod.fst)ᶜ, u i = ∑ i, u i :=
    Finset.sum_add_sum_compl _ u
  have hG' : ∑ j ∈ P.image Prod.snd, v j + ∑ j ∈ (P.image Prod.snd)ᶜ, v j = ∑ j, v j :=
    Finset.sum_add_sum_compl _ v
  have hT2 : 0 ≤ ∑ i ∈ (P.image Prod.fst)ᶜ, u i := Finset.sum_nonneg fun i _ => hu i
  have hT3 : 0 ≤ ∑ j ∈ (P.image Prod.snd)ᶜ, v j := Finset.sum_nonneg fun j _ => hv j
  have hT1 : 0 ≤ ∑ p ∈ P, (u p.1 + v p.2 - a p.1 p.2) :=
    Finset.sum_nonneg fun p _ => by linarith [hab p.1 p.2]
  have hexp : ∑ p ∈ P, (u p.1 + v p.2 - a p.1 p.2) =
      ∑ p ∈ P, u p.1 + ∑ p ∈ P, v p.2 - ∑ p ∈ P, a p.1 p.2 := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hz1 : ∑ p ∈ P, (u p.1 + v p.2 - a p.1 p.2) = 0 := by linarith
  have hz2 : ∑ i ∈ (P.image Prod.fst)ᶜ, u i = 0 := by linarith
  have hz3 : ∑ j ∈ (P.image Prod.snd)ᶜ, v j = 0 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun p _ => by linarith [hab p.1 p.2])).1 hz1 p hp
    linarith
  · intro i hi
    have hiF : i ∈ (P.image Prod.fst)ᶜ := by
      rw [Finset.mem_compl, Finset.mem_image]
      rintro ⟨p, hp, hp1⟩
      exact hi p hp hp1
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hu i)).1 hz2 i hiF
  · intro j hj
    have hjG : j ∈ (P.image Prod.snd)ᶜ := by
      rw [Finset.mem_compl, Finset.mem_image]
      rintro ⟨p, hp, hp1⟩
      exact hj p hp hp1
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hv j)).1 hz3 j hjG

open AssignmentGame.CoreCorners in
theorem ag1171_sum_of_cs {M N : Type*} [Fintype M] [Fintype N] (a : M → N → ℝ) (u : M → ℝ)
    (v : N → ℝ) {P : Finset (M × N)}
    (hP : IsMatching (Finset.univ : Finset M) (Finset.univ : Finset N) P)
    (h1 : ∀ p ∈ P, u p.1 + v p.2 = a p.1 p.2) (h2 : ∀ i, (∀ p ∈ P, p.1 ≠ i) → u i = 0)
    (h3 : ∀ j, (∀ p ∈ P, p.2 ≠ j) → v j = 0) :
    ∑ i, u i + ∑ j, v j = ∑ p ∈ P, a p.1 p.2 := by
  classical
  obtain ⟨-, hi1, hi2⟩ := hP
  have hsumu : ∑ i, u i = ∑ i ∈ P.image Prod.fst, u i := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    exact h2 i (fun p hp hp1 => hi (Finset.mem_image.2 ⟨p, hp, hp1⟩))
  have hsumv : ∑ j, v j = ∑ j ∈ P.image Prod.snd, v j := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    exact h3 j (fun p hp hp1 => hj (Finset.mem_image.2 ⟨p, hp, hp1⟩))
  have e1 : ∑ p ∈ P, u p.1 = ∑ i ∈ P.image Prod.fst, u i := by
    rw [Finset.sum_image]
    intro p hp q hq hpq
    exact hi1 p hp q hq hpq
  have e2 : ∑ p ∈ P, v p.2 = ∑ j ∈ P.image Prod.snd, v j := by
    rw [Finset.sum_image]
    intro p hp q hq hpq
    exact hi2 p hp q hq hpq
  calc ∑ i, u i + ∑ j, v j = ∑ p ∈ P, u p.1 + ∑ p ∈ P, v p.2 := by
        rw [e1, e2, hsumu, hsumv]
    _ = ∑ p ∈ P, (u p.1 + v p.2) := Finset.sum_add_distrib.symm
    _ = ∑ p ∈ P, a p.1 p.2 := Finset.sum_congr rfl h1

open AssignmentGame.CoreCorners in
theorem ag1171_core_lattice {M N : Type*} [Fintype M] [Fintype N] (a : M → N → ℝ)
    {u u' : M → ℝ} {v v' : N → ℝ} (h : (u, v) ∈ core a) (h' : (u', v') ∈ core a) :
    ((fun i => max (u i) (u' i), fun j => min (v j) (v' j)) ∈ core a) ∧
    ((fun i => min (u i) (u' i), fun j => max (v j) (v' j)) ∈ core a) := by
  classical
  obtain ⟨P, hP, hw⟩ := ag1171_exists_opt a Finset.univ Finset.univ
  obtain ⟨c1, c2, c3⟩ := ag1171_cs a h hP hw
  obtain ⟨c1', c2', c3'⟩ := ag1171_cs a h' hP hw
  obtain ⟨⟨hu, hv, hab⟩, -⟩ := (ag1171_core_iff a u v).1 h
  obtain ⟨⟨hu', hv', hab'⟩, -⟩ := (ag1171_core_iff a u' v').1 h'
  constructor
  · rw [ag1171_core_iff]
    have hdf : ag1171_DF a (fun i => max (u i) (u' i)) (fun j => min (v j) (v' j)) := by
      refine ⟨fun i => le_max_of_le_left (hu i), fun j => le_min (hv j) (hv' j), fun i j => ?_⟩
      rcases le_total (v j) (v' j) with hj | hj
      · show a i j ≤ max (u i) (u' i) + min (v j) (v' j)
        rw [min_eq_left hj]; linarith [le_max_left (u i) (u' i), hab i j]
      · show a i j ≤ max (u i) (u' i) + min (v j) (v' j)
        rw [min_eq_right hj]; linarith [le_max_right (u i) (u' i), hab' i j]
    refine ⟨hdf, ?_⟩
    rw [hw]
    refine ag1171_sum_of_cs a _ _ hP ?_ ?_ ?_
    · intro p hp
      have e1 := c1 p hp
      have e2 := c1' p hp
      show max (u p.1) (u' p.1) + min (v p.2) (v' p.2) = a p.1 p.2
      rcases le_total (u p.1) (u' p.1) with hh | hh
      · rw [max_eq_right hh, min_eq_right (by linarith)]; linarith
      · rw [max_eq_left hh, min_eq_left (by linarith)]; linarith
    · intro i hi
      show max (u i) (u' i) = 0
      rw [c2 i hi, c2' i hi]; simp
    · intro j hj
      show min (v j) (v' j) = 0
      rw [c3 j hj, c3' j hj]; simp
  · rw [ag1171_core_iff]
    have hdf : ag1171_DF a (fun i => min (u i) (u' i)) (fun j => max (v j) (v' j)) := by
      refine ⟨fun i => le_min (hu i) (hu' i), fun j => le_max_of_le_left (hv j), fun i j => ?_⟩
      rcases le_total (u i) (u' i) with hj | hj
      · show a i j ≤ min (u i) (u' i) + max (v j) (v' j)
        rw [min_eq_left hj]; linarith [le_max_left (v j) (v' j), hab i j]
      · show a i j ≤ min (u i) (u' i) + max (v j) (v' j)
        rw [min_eq_right hj]; linarith [le_max_right (v j) (v' j), hab' i j]
    refine ⟨hdf, ?_⟩
    rw [hw]
    refine ag1171_sum_of_cs a _ _ hP ?_ ?_ ?_
    · intro p hp
      have e1 := c1 p hp
      have e2 := c1' p hp
      show min (u p.1) (u' p.1) + max (v p.2) (v' p.2) = a p.1 p.2
      rcases le_total (u p.1) (u' p.1) with hh | hh
      · rw [min_eq_left hh, max_eq_left (by linarith)]; linarith
      · rw [min_eq_right hh, max_eq_right (by linarith)]; linarith
    · intro i hi
      show min (u i) (u' i) = 0
      rw [c2 i hi, c2' i hi]; simp
    · intro j hj
      show max (v j) (v' j) = 0
      rw [c3 j hj, c3' j hj]; simp

/-! ## Compactness and attainment of the extrema -/

open AssignmentGame.CoreCorners in
theorem ag1171_core_compact {M N : Type*} [Fintype M] [Fintype N] (a : M → N → ℝ) :
    IsCompact (core a) := by
  classical
  set W := worth a Finset.univ Finset.univ with hW
  have hbox : IsCompact ((Set.univ.pi fun _ : M => Set.Icc (0:ℝ) W) ×ˢ
      (Set.univ.pi fun _ : N => Set.Icc (0:ℝ) W)) :=
    (isCompact_univ_pi fun _ => isCompact_Icc).prod (isCompact_univ_pi fun _ => isCompact_Icc)
  refine hbox.of_isClosed_subset ?_ ?_
  · have c1 : IsClosed {p : (M → ℝ) × (N → ℝ) | ∑ i, p.1 i + ∑ j, p.2 j = W} :=
      isClosed_eq (by fun_prop) continuous_const
    have c2 : IsClosed {p : (M → ℝ) × (N → ℝ) | ∀ (A : Finset M) (B : Finset N),
        worth a A B ≤ ∑ i ∈ A, p.1 i + ∑ j ∈ B, p.2 j} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun A => isClosed_iInter fun B =>
        isClosed_le continuous_const (by fun_prop)
    exact c1.inter c2
  · intro p hp
    have hp' : (p.1, p.2) ∈ core a := by rwa [Prod.mk.eta]
    obtain ⟨⟨hu, hv, -⟩, hsum⟩ := (ag1171_core_iff a p.1 p.2).1 hp'
    have h2 : 0 ≤ ∑ k, p.2 k := Finset.sum_nonneg (fun k _ => hv k)
    have h2' : 0 ≤ ∑ k, p.1 k := Finset.sum_nonneg (fun k _ => hu k)
    refine ⟨fun i _ => ⟨hu i, ?_⟩, fun j _ => ⟨hv j, ?_⟩⟩
    · have h1 : p.1 i ≤ ∑ k, p.1 k :=
        Finset.single_le_sum (f := fun k => p.1 k) (fun k _ => hu k) (Finset.mem_univ i)
      linarith
    · have h1 : p.2 j ≤ ∑ k, p.2 k :=
        Finset.single_le_sum (f := fun k => p.2 k) (fun k _ => hv k) (Finset.mem_univ j)
      linarith

open AssignmentGame.CoreCorners in
theorem ag1171_ext {M N : Type*} [Fintype M] [Fintype N] (a : M → N → ℝ)
    (h0 : (core a).Nonempty) (f : (M → ℝ) × (N → ℝ) → ℝ) (hf : Continuous f) :
    (∃ p ∈ core a, ∀ q ∈ core a, f p ≤ f q) ∧ (∃ p ∈ core a, ∀ q ∈ core a, f q ≤ f p) := by
  obtain ⟨p, hp, hpm⟩ := (ag1171_core_compact a).exists_isMinOn h0 hf.continuousOn
  obtain ⟨p', hp', hpM⟩ := (ag1171_core_compact a).exists_isMaxOn h0 hf.continuousOn
  exact ⟨⟨p, hp, fun q hq => isMinOn_iff.1 hpm q hq⟩, ⟨p', hp', fun q hq => isMaxOn_iff.1 hpM q hq⟩⟩

open AssignmentGame.CoreCorners in
theorem ag1171_uLo {M N : Type*} [Fintype M] [Fintype N] (a : M → N → ℝ)
    (h0 : (core a).Nonempty) (i : M) :
    ∃ p ∈ core a, p.1 i = uLo a i ∧ ∀ q ∈ core a, uLo a i ≤ q.1 i := by
  obtain ⟨⟨p, hp, hpm⟩, -⟩ := ag1171_ext a h0 (fun p => p.1 i) (by fun_prop)
  have : uLo a i = p.1 i := by
    unfold uLo
    exact IsLeast.csInf_eq ⟨⟨p, hp, rfl⟩, by rintro _ ⟨q, hq, rfl⟩; exact hpm q hq⟩
  exact ⟨p, hp, this.symm, fun q hq => this ▸ hpm q hq⟩

open AssignmentGame.CoreCorners in
theorem ag1171_uHi {M N : Type*} [Fintype M] [Fintype N] (a : M → N → ℝ)
    (h0 : (core a).Nonempty) (i : M) :
    ∃ p ∈ core a, p.1 i = uHi a i ∧ ∀ q ∈ core a, q.1 i ≤ uHi a i := by
  obtain ⟨-, ⟨p, hp, hpm⟩⟩ := ag1171_ext a h0 (fun p => p.1 i) (by fun_prop)
  have : uHi a i = p.1 i := by
    unfold uHi
    exact IsGreatest.csSup_eq ⟨⟨p, hp, rfl⟩, by rintro _ ⟨q, hq, rfl⟩; exact hpm q hq⟩
  exact ⟨p, hp, this.symm, fun q hq => this ▸ hpm q hq⟩

open AssignmentGame.CoreCorners in
theorem ag1171_vLo {M N : Type*} [Fintype M] [Fintype N] (a : M → N → ℝ)
    (h0 : (core a).Nonempty) (j : N) :
    ∃ p ∈ core a, p.2 j = vLo a j ∧ ∀ q ∈ core a, vLo a j ≤ q.2 j := by
  obtain ⟨⟨p, hp, hpm⟩, -⟩ := ag1171_ext a h0 (fun p => p.2 j) (by fun_prop)
  have : vLo a j = p.2 j := by
    unfold vLo
    exact IsLeast.csInf_eq ⟨⟨p, hp, rfl⟩, by rintro _ ⟨q, hq, rfl⟩; exact hpm q hq⟩
  exact ⟨p, hp, this.symm, fun q hq => this ▸ hpm q hq⟩

open AssignmentGame.CoreCorners in
theorem ag1171_vHi {M N : Type*} [Fintype M] [Fintype N] (a : M → N → ℝ)
    (h0 : (core a).Nonempty) (j : N) :
    ∃ p ∈ core a, p.2 j = vHi a j ∧ ∀ q ∈ core a, q.2 j ≤ vHi a j := by
  obtain ⟨-, ⟨p, hp, hpm⟩⟩ := ag1171_ext a h0 (fun p => p.2 j) (by fun_prop)
  have : vHi a j = p.2 j := by
    unfold vHi
    exact IsGreatest.csSup_eq ⟨⟨p, hp, rfl⟩, by rintro _ ⟨q, hq, rfl⟩; exact hpm q hq⟩
  exact ⟨p, hp, this.symm, fun q hq => this ▸ hpm q hq⟩

/-! ## Finite meets and joins -/

open AssignmentGame.CoreCorners in
theorem ag1171_meet {M N : Type*} [Fintype M] [Fintype N] (a : M → N → ℝ)
    (h0 : (core a).Nonempty) {ι : Type*} [Fintype ι] (p : ι → (M → ℝ) × (N → ℝ))
    (hp : ∀ k, p k ∈ core a) :
    ∃ r ∈ core a, ∀ k, (∀ i, r.1 i ≤ (p k).1 i) ∧ (∀ j, (p k).2 j ≤ r.2 j) := by
  classical
  have key : ∀ s : Finset ι, ∃ r ∈ core a, ∀ k ∈ s,
      (∀ i, r.1 i ≤ (p k).1 i) ∧ (∀ j, (p k).2 j ≤ r.2 j) := by
    intro s
    induction s using Finset.induction_on with
    | empty => obtain ⟨r, hr⟩ := h0; exact ⟨r, hr, by simp⟩
    | insert k s hk ih =>
      obtain ⟨r, hr, hrs⟩ := ih
      have hr' : (r.1, r.2) ∈ core a := by rwa [Prod.mk.eta]
      have hk' : ((p k).1, (p k).2) ∈ core a := by rw [Prod.mk.eta]; exact hp k
      have := (ag1171_core_lattice a hr' hk').2
      refine ⟨(fun i => min (r.1 i) ((p k).1 i), fun j => max (r.2 j) ((p k).2 j)), this, ?_⟩
      intro k' hk''
      rcases Finset.mem_insert.1 hk'' with rfl | hk''
      · exact ⟨fun i => min_le_right _ _, fun j => le_max_right _ _⟩
      · obtain ⟨h1, h2⟩ := hrs k' hk''
        exact ⟨fun i => (min_le_left _ _).trans (h1 i), fun j => (h2 j).trans (le_max_left _ _)⟩
  obtain ⟨r, hr, h⟩ := key Finset.univ
  exact ⟨r, hr, fun k => h k (Finset.mem_univ k)⟩

open AssignmentGame.CoreCorners in
theorem ag1171_join {M N : Type*} [Fintype M] [Fintype N] (a : M → N → ℝ)
    (h0 : (core a).Nonempty) {ι : Type*} [Fintype ι] (p : ι → (M → ℝ) × (N → ℝ))
    (hp : ∀ k, p k ∈ core a) :
    ∃ r ∈ core a, ∀ k, (∀ i, (p k).1 i ≤ r.1 i) ∧ (∀ j, r.2 j ≤ (p k).2 j) := by
  classical
  have key : ∀ s : Finset ι, ∃ r ∈ core a, ∀ k ∈ s,
      (∀ i, (p k).1 i ≤ r.1 i) ∧ (∀ j, r.2 j ≤ (p k).2 j) := by
    intro s
    induction s using Finset.induction_on with
    | empty => obtain ⟨r, hr⟩ := h0; exact ⟨r, hr, by simp⟩
    | insert k s hk ih =>
      obtain ⟨r, hr, hrs⟩ := ih
      have hr' : (r.1, r.2) ∈ core a := by rwa [Prod.mk.eta]
      have hk' : ((p k).1, (p k).2) ∈ core a := by rw [Prod.mk.eta]; exact hp k
      have := (ag1171_core_lattice a hr' hk').1
      refine ⟨(fun i => max (r.1 i) ((p k).1 i), fun j => min (r.2 j) ((p k).2 j)), this, ?_⟩
      intro k' hk''
      rcases Finset.mem_insert.1 hk'' with rfl | hk''
      · exact ⟨fun i => le_max_right _ _, fun j => min_le_right _ _⟩
      · obtain ⟨h1, h2⟩ := hrs k' hk''
        exact ⟨fun i => (h1 i).trans (le_max_left _ _), fun j => (min_le_left _ _).trans (h2 j)⟩
  obtain ⟨r, hr, h⟩ := key Finset.univ
  exact ⟨r, hr, fun k => h k (Finset.mem_univ k)⟩

/-! ## The theorem -/

open Finset AssignmentGame.CoreCorners in
theorem solution {M N : Type*} [Fintype M] [Fintype N]
    (a : M → N → ℝ) (ha : ∀ i j, 0 ≤ a i j) :
    (uLo a, vHi a) ∈ core a ∧ (uHi a, vLo a) ∈ core a ∧
    ∀ (u' u'' : M → ℝ) (v' v'' : N → ℝ), (u', v') ∈ core a → (u'', v'') ∈ core a →
      ∑ i, (u' i - u'' i) ^ 2 + ∑ j, (v' j - v'' j) ^ 2 ≤
        ∑ i, (uLo a i - uHi a i) ^ 2 + ∑ j, (vHi a j - vLo a j) ^ 2 := by
  classical
  obtain ⟨u0, v0, h0⟩ := ag1171_core_nonempty a ha
  have hne : (core a).Nonempty := ⟨(u0, v0), h0⟩
  choose pl hpl using fun i => ag1171_uLo a hne i
  choose ph hph using fun i => ag1171_uHi a hne i
  choose ql hql using fun j => ag1171_vLo a hne j
  choose qh hqh using fun j => ag1171_vHi a hne j
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨r, hr, hrk⟩ := ag1171_meet a hne (ι := M ⊕ N) (Sum.elim pl qh) (by
      intro k
      rcases k with i | j
      · exact (hpl i).1
      · exact (hqh j).1)
    have hru : ∀ i, r.1 i = uLo a i := by
      intro i
      apply le_antisymm
      · have := (hrk (Sum.inl i)).1 i
        simpa [(hpl i).2.1] using this
      · exact (hpl i).2.2 r hr
    have hrv : ∀ j, r.2 j = vHi a j := by
      intro j
      apply le_antisymm
      · exact (hqh j).2.2 r hr
      · have := (hrk (Sum.inr j)).2 j
        simpa [(hqh j).2.1] using this
    have : r = (uLo a, vHi a) := Prod.ext (funext hru) (funext hrv)
    rw [← this]; exact hr
  · obtain ⟨r, hr, hrk⟩ := ag1171_join a hne (ι := M ⊕ N) (Sum.elim ph ql) (by
      intro k
      rcases k with i | j
      · exact (hph i).1
      · exact (hql j).1)
    have hru : ∀ i, r.1 i = uHi a i := by
      intro i
      apply le_antisymm
      · exact (hph i).2.2 r hr
      · have := (hrk (Sum.inl i)).1 i
        simpa [(hph i).2.1] using this
    have hrv : ∀ j, r.2 j = vLo a j := by
      intro j
      apply le_antisymm
      · have := (hrk (Sum.inr j)).2 j
        simpa [(hql j).2.1] using this
      · exact (hql j).2.2 r hr
    have : r = (uHi a, vLo a) := Prod.ext (funext hru) (funext hrv)
    rw [← this]; exact hr
  · intro u' u'' v' v'' h' h''
    have h1 : ∀ i, (u' i - u'' i) ^ 2 ≤ (uLo a i - uHi a i) ^ 2 := by
      intro i
      have a1 := (ag1171_uLo a hne i).choose_spec.2.2 _ h'
      have a2 := (ag1171_uLo a hne i).choose_spec.2.2 _ h''
      have b1 := (ag1171_uHi a hne i).choose_spec.2.2 _ h'
      have b2 := (ag1171_uHi a hne i).choose_spec.2.2 _ h''
      have hh : (u' i - u'' i) ^ 2 ≤ (uHi a i - uLo a i) ^ 2 := by
        apply sq_le_sq'
        · simp only at a1 a2 b1 b2; linarith
        · simp only at a1 a2 b1 b2; linarith
      calc (u' i - u'' i) ^ 2 ≤ (uHi a i - uLo a i) ^ 2 := hh
        _ = (uLo a i - uHi a i) ^ 2 := by ring
    have h2 : ∀ j, (v' j - v'' j) ^ 2 ≤ (vHi a j - vLo a j) ^ 2 := by
      intro j
      have a1 := (ag1171_vLo a hne j).choose_spec.2.2 _ h'
      have a2 := (ag1171_vLo a hne j).choose_spec.2.2 _ h''
      have b1 := (ag1171_vHi a hne j).choose_spec.2.2 _ h'
      have b2 := (ag1171_vHi a hne j).choose_spec.2.2 _ h''
      apply sq_le_sq'
      · simp only at a1 a2 b1 b2; linarith
      · simp only at a1 a2 b1 b2; linarith
    exact add_le_add (Finset.sum_le_sum fun i _ => h1 i) (Finset.sum_le_sum fun j _ => h2 j)
