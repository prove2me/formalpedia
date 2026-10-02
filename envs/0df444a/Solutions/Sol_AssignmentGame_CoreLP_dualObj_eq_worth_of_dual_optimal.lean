-- Prove2me | solution 1 for AssignmentGame.CoreLP.dualObj_eq_worth_of_dual_optimal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T22:05:48.015539+00:00
-- url     : https://prove2.me/submissions/3cb5503e-3410-442f-ba64-6d872384b1d3

import Mathlib
import Definitions.Def_AssignmentGame_CoreLP_Game

set_option autoImplicit false

/-! Assignment game: the core is the set of optimal dual solutions.  The hard direction
(strong duality `dualObj p ≤ worth`) goes through Hall's theorem on the tight graph of an optimal
dual, after padding the matrix to a square one. -/

theorem ag_exists_eps {ι : Type*} (S : Finset ι) (g : ι → ℝ) (hg : ∀ x ∈ S, 0 < g x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ S, ε ≤ g x := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a S ha ih =>
    obtain ⟨ε, hε, h⟩ := ih (fun x hx => hg x (Finset.mem_insert_of_mem hx))
    refine ⟨min ε (g a), lt_min hε (hg a (Finset.mem_insert_self a S)), ?_⟩
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (h x hx)

theorem ag_sum_ite {ι : Type*} [Fintype ι] [DecidableEq ι] (s : Finset ι) (ε : ℝ) :
    ∑ l, (if l ∈ s then ε else 0) = (s.card : ℝ) * ε := by
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]

/-- Hall + perturbation: a globally optimal free dual has a perfect-type tight system. -/
theorem ag_hall_dual {L R : Type*} [Fintype L] [Fintype R] (b : L → R → ℝ) (u : L → ℝ)
    (v : R → ℝ) (hf : ∀ l r, b l r ≤ u l + v r)
    (hmin : ∀ (u' : L → ℝ) (v' : R → ℝ), (∀ l r, b l r ≤ u' l + v' r) →
      ∑ l, u l + ∑ r, v r ≤ ∑ l, u' l + ∑ r, v' r) :
    ∃ f : L → R, Function.Injective f ∧ ∀ l, u l + v (f l) = b l (f l) := by
  classical
  have key := (Finset.all_card_le_biUnion_card_iff_exists_injective
    (fun l : L => (Finset.univ.filter (fun r : R => u l + v r = b l r)))).1 ?_
  · obtain ⟨f, hinj, hfl⟩ := key
    exact ⟨f, hinj, fun l => by simpa using hfl l⟩
  · intro s
    rcases le_or_gt s.card
      (s.biUnion (fun l : L => (Finset.univ.filter (fun r : R => u l + v r = b l r)))).card with
      h | h
    · exact h
    · exfalso
      set Γ := s.biUnion (fun l : L => (Finset.univ.filter (fun r : R => u l + v r = b l r)))
        with hΓ
      obtain ⟨ε, hε, hεle⟩ := ag_exists_eps (s ×ˢ Γᶜ)
        (fun p : L × R => u p.1 + v p.2 - b p.1 p.2) (by
          intro p hp
          rw [Finset.mem_product] at hp
          obtain ⟨hp1, hp2⟩ := hp
          have h1 := hf p.1 p.2
          have h2 : u p.1 + v p.2 ≠ b p.1 p.2 := by
            intro heq
            apply Finset.mem_compl.1 hp2
            rw [hΓ, Finset.mem_biUnion]
            exact ⟨p.1, hp1, by simpa using heq⟩
          have h3 := lt_of_le_of_ne h1 (Ne.symm h2)
          linarith)
      have hfeas : ∀ l r, b l r ≤
          (u l - if l ∈ s then ε else 0) + (v r + if r ∈ Γ then ε else 0) := by
        intro l r
        have h0 := hf l r
        by_cases hl : l ∈ s
        · by_cases hr : r ∈ Γ
          · simp only [hl, hr, if_true]; linarith
          · have h4 := hεle (l, r) (Finset.mem_product.2 ⟨hl, Finset.mem_compl.2 hr⟩)
            simp only [hl, hr, if_true, if_false]
            simp only at h4
            linarith
        · by_cases hr : r ∈ Γ
          · simp only [hl, hr, if_true, if_false]; linarith
          · simp only [hl, hr, if_false]; linarith
      have hm := hmin _ _ hfeas
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ag_sum_ite, ag_sum_ite] at hm
      have hc : (Γ.card : ℝ) < s.card := by exact_mod_cast h
      nlinarith

open AssignmentGame.CoreLP Finset in
theorem ag_weak {M N : Type*} [Fintype M] [Fintype N] (a : M → N → ℝ)
    (q : (M → ℝ) × (N → ℝ)) (hq : DualFeasible a q) (A : Finset M) (B : Finset N) :
    worth a A B ≤ ∑ i ∈ A, q.1 i + ∑ j ∈ B, q.2 j := by
  classical
  unfold worth
  apply Finset.sup'_le
  intro P hP
  have hP' : IsMatching A B P := by
    unfold matchings at hP
    exact (Finset.mem_filter.1 hP).2
  obtain ⟨hsub, h1, h2⟩ := hP'
  obtain ⟨hu, hv, hab⟩ := hq
  have e1 : ∑ p ∈ P, q.1 p.1 = ∑ i ∈ P.image Prod.fst, q.1 i := by
    rw [Finset.sum_image]
    intro x hx y hy hxy
    exact h1 x hx y hy hxy
  have e2 : ∑ p ∈ P, q.2 p.2 = ∑ j ∈ P.image Prod.snd, q.2 j := by
    rw [Finset.sum_image]
    intro x hx y hy hxy
    exact h2 x hx y hy hxy
  have hle1 : ∑ i ∈ P.image Prod.fst, q.1 i ≤ ∑ i ∈ A, q.1 i := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hi
      exact (Finset.mem_product.1 (hsub hp)).1
    · intro i _ _
      exact hu i
  have hle2 : ∑ j ∈ P.image Prod.snd, q.2 j ≤ ∑ j ∈ B, q.2 j := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro j hj
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hj
      exact (Finset.mem_product.1 (hsub hp)).2
    · intro j _ _
      exact hv j
  calc ∑ p ∈ P, a p.1 p.2 ≤ ∑ p ∈ P, (q.1 p.1 + q.2 p.2) :=
        Finset.sum_le_sum (fun p _ => hab p.1 p.2)
    _ = ∑ p ∈ P, q.1 p.1 + ∑ p ∈ P, q.2 p.2 := Finset.sum_add_distrib
    _ ≤ _ := by rw [e1, e2]; linarith

open AssignmentGame.CoreLP Finset in
theorem ag_worth_nonneg {M N : Type*} [Fintype M] [Fintype N] (a : M → N → ℝ)
    (A : Finset M) (B : Finset N) : 0 ≤ worth a A B := by
  classical
  unfold worth
  refine le_trans ?_ (Finset.le_sup' (fun P => ∑ p ∈ P, a p.1 p.2) (empty_mem_matchings A B))
  simp

open AssignmentGame.CoreLP Finset in
theorem ag_worth_single {M N : Type*} [Fintype M] [Fintype N] (a : M → N → ℝ) (i : M) (j : N) :
    a i j ≤ worth a {i} {j} := by
  classical
  unfold worth
  have hm : ({(i, j)} : Finset (M × N)) ∈ matchings ({i} : Finset M) ({j} : Finset N) := by
    unfold matchings
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨by simp, by simp, by simp, by simp⟩
  have h := Finset.le_sup' (fun P => ∑ p ∈ P, a p.1 p.2) hm
  simpa using h

open AssignmentGame.CoreLP Finset in
theorem ag_strong {M N : Type*} [Fintype M] [Fintype N] (a : M → N → ℝ)
    (ha : ∀ i j, 0 ≤ a i j) (p : (M → ℝ) × (N → ℝ)) (hp : DualFeasible a p)
    (hopt : ∀ q, DualFeasible a q → dualObj p ≤ dualObj q) :
    dualObj p ≤ worth a univ univ := by
  classical
  obtain ⟨hpu, hpv, hpab⟩ := hp
  let b : M ⊕ N → N ⊕ M → ℝ := fun l =>
    Sum.elim (fun i r => Sum.elim (fun j => a i j) (fun _ => 0) r) (fun _ _ => 0) l
  have hb : ∀ l r, 0 ≤ b l r := by
    intro l r
    rcases l with i | j <;> rcases r with j | i <;> simp [b, ha]
  let u0 : M ⊕ N → ℝ := Sum.elim p.1 (fun _ => 0)
  let v0 : N ⊕ M → ℝ := Sum.elim p.2 (fun _ => 0)
  have hfeas0 : ∀ l r, b l r ≤ u0 l + v0 r := by
    intro l r
    rcases l with i | j <;> rcases r with j | i <;> simp [b, u0, v0, hpab, hpu, hpv]
  have hsum0 : ∑ l, u0 l + ∑ r, v0 r = dualObj p := by
    simp only [u0, v0, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.sum_const_zero,
      dualObj]
    ring
  have hcard : Fintype.card (M ⊕ N) = Fintype.card (N ⊕ M) := by
    simp [add_comm]
  have hmin : ∀ (u' : M ⊕ N → ℝ) (v' : N ⊕ M → ℝ), (∀ l r, b l r ≤ u' l + v' r) →
      ∑ l, u0 l + ∑ r, v0 r ≤ ∑ l, u' l + ∑ r, v' r := by
    intro u' v' hf'
    rw [hsum0]
    rcases isEmpty_or_nonempty (M ⊕ N) with hE | hNE
    · have hE2 : IsEmpty (N ⊕ M) := by
        rw [← Fintype.card_eq_zero_iff] at hE ⊢
        omega
      have hd : dualObj p = 0 := by
        rw [← hsum0]
        simp
      simp [hd]
    · have hNE2 : Nonempty (N ⊕ M) := by
        rw [← Fintype.card_pos_iff] at hNE ⊢
        omega
      obtain ⟨l0, hl0⟩ := Finite.exists_min u'
      obtain ⟨r0, hr0⟩ := Finite.exists_min v'
      have hv'' : ∀ r, 0 ≤ v' r + u' l0 := by
        intro r
        have h1 := hf' l0 r0
        have h2 := hb l0 r0
        have h3 := hr0 r
        linarith
      have hu_nn : ∀ l, 0 ≤ u' l - u' l0 := by
        intro l
        have h1 := hl0 l
        linarith
      let q : (M → ℝ) × (N → ℝ) :=
        (fun i => u' (Sum.inl i) - u' l0, fun j => v' (Sum.inl j) + u' l0)
      have hq : DualFeasible a q := by
        refine ⟨fun i => hu_nn _, fun j => hv'' _, fun i j => ?_⟩
        have h1 := hf' (Sum.inl i) (Sum.inl j)
        simp only [b, Sum.elim_inl] at h1
        show a i j ≤ (u' (Sum.inl i) - u' l0) + (v' (Sum.inl j) + u' l0)
        linarith
      have h1 := hopt q hq
      have h2 : dualObj q = ∑ i, (u' (Sum.inl i) - u' l0) + ∑ j, (v' (Sum.inl j) + u' l0) := rfl
      have hsplitu : ∑ l, (u' l - u' l0) =
          ∑ i, (u' (Sum.inl i) - u' l0) + ∑ j, (u' (Sum.inr j) - u' l0) :=
        Fintype.sum_sum_type _
      have hsplitv : ∑ r, (v' r + u' l0) =
          ∑ j, (v' (Sum.inl j) + u' l0) + ∑ i, (v' (Sum.inr i) + u' l0) :=
        Fintype.sum_sum_type _
      have hnnu : 0 ≤ ∑ j, (u' (Sum.inr j) - u' l0) :=
        Finset.sum_nonneg (fun j _ => hu_nn _)
      have hnnv : 0 ≤ ∑ i, (v' (Sum.inr i) + u' l0) :=
        Finset.sum_nonneg (fun i _ => hv'' _)
      have hcalc : ∑ l, (u' l - u' l0) + ∑ r, (v' r + u' l0) = ∑ l, u' l + ∑ r, v' r := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
          Finset.card_univ, Finset.card_univ, hcard]
        simp only [nsmul_eq_mul]
        ring
      linarith
  obtain ⟨f, hinj, hf⟩ := ag_hall_dual b u0 v0 hfeas0 hmin
  have hbij : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard⟩
  have hsumv : ∑ l, v0 (f l) = ∑ r, v0 r := Function.Bijective.sum_comp hbij v0
  have hW : ∑ l, b l (f l) = dualObj p := by
    have h1 : ∀ l, b l (f l) = u0 l + v0 (f l) := fun l => (hf l).symm
    simp only [h1, Finset.sum_add_distrib, hsumv]
    exact hsum0
  let P : Finset (M × N) := Finset.univ.filter (fun ij => f (Sum.inl ij.1) = Sum.inl ij.2)
  have hPm : P ∈ matchings (univ : Finset M) (univ : Finset N) := by
    unfold matchings
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨by simp, by simp, ?_, ?_⟩
    · intro x hx y hy hxy
      simp only [P, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
      have h3 : (Sum.inl x.2 : N ⊕ M) = Sum.inl y.2 := by rw [← hx, ← hy, hxy]
      exact Prod.ext hxy (Sum.inl_injective h3)
    · intro x hx y hy hxy
      simp only [P, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
      have h3 : f (Sum.inl x.1) = f (Sum.inl y.1) := by rw [hx, hy, hxy]
      exact Prod.ext (Sum.inl_injective (hinj h3)) hxy
  have hPw : ∑ p ∈ P, a p.1 p.2 = ∑ l, b l (f l) := by
    rw [Fintype.sum_sum_type]
    have h0 : ∑ j, b (Sum.inr j) (f (Sum.inr j)) = 0 := by
      simp [b]
    rw [h0, add_zero, Finset.sum_filter, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    rcases h : f (Sum.inl i) with j0 | m
    · simp [b, h]
    · simp [b, h]
  have hle : ∑ p ∈ P, a p.1 p.2 ≤ worth a univ univ := by
    unfold worth
    exact Finset.le_sup' (fun P => ∑ p ∈ P, a p.1 p.2) hPm
  linarith

open AssignmentGame.CoreLP Finset in
theorem solution {M N : Type*} [Fintype M] [Fintype N]
    (a : M → N → ℝ) (ha : ∀ i j, 0 ≤ a i j) (p : (M → ℝ) × (N → ℝ))
    (hp : DualOptimal a p) :
    ∑ i, p.1 i + ∑ j, p.2 j = worth a univ univ := by
  classical
  obtain ⟨hfeas, hopt⟩ := hp
  have hstrong := ag_strong a ha p hfeas hopt
  have h1 := ag_weak a p hfeas Finset.univ Finset.univ
  unfold dualObj at hstrong
  linarith
