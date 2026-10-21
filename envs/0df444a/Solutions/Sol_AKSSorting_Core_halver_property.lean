-- Prove2me | solution 1 for AKSSorting.Core.halver_property
-- status  : ACCEPTED   (prove)
-- author  : @sattath
-- created : 2026-10-20T06:28:59.493369+00:00
-- url     : https://prove2.me/submissions/b06d779c-507e-4832-a358-7ab8f99e63c4

import Mathlib
import Definitions.Def_AKSSorting_Core_compareExchange
import Definitions.Def_AKSSorting_Core_IsExpander
import Definitions.Def_AKSSorting_Core_IsLowerSection

open AKSSorting.Core

section
variable {R : Type} [DecidableEq R] {α : Type} [LinearOrder α]

lemma ce_step (A B : Finset R) (hAB : Disjoint A B) (p : R × R) (hp1 : p.1 ∈ A) (hp2 : p.2 ∈ B)
    (x : R → α) :
    (∀ a ∈ A, compareExchange p.1 p.2 x a ≤ x a) ∧ (∀ b ∈ B, x b ≤ compareExchange p.1 p.2 x b) := by
  have hne : ∀ r, r ∈ A → r ≠ p.2 := fun r hr h => Finset.disjoint_left.mp hAB hr (h ▸ hp2)
  have hne' : ∀ r, r ∈ B → r ≠ p.1 := fun r hr h => Finset.disjoint_left.mp hAB (h ▸ hp1) hr
  constructor
  · intro a ha
    simp only [compareExchange, Function.update_apply, if_neg (hne a ha)]
    split_ifs with h
    · subst h; exact min_le_left _ _
    · exact le_rfl
  · intro b hb
    simp only [compareExchange, Function.update_apply, if_neg (hne' b hb)]
    split_ifs with h
    · subst h; exact le_max_right _ _
    · exact le_rfl

lemma fold_mono (A B : Finset R) (hAB : Disjoint A B) :
    ∀ (l : List (R × R)) (x : R → α), (∀ p ∈ l, p.1 ∈ A ∧ p.2 ∈ B) →
      (∀ a ∈ A, l.foldl (fun y p => compareExchange p.1 p.2 y) x a ≤ x a) ∧
      (∀ b ∈ B, x b ≤ l.foldl (fun y p => compareExchange p.1 p.2 y) x b) := by
  intro l
  induction l with
  | nil => intro x _; simp
  | cons p l ih =>
    intro x hl
    have hp := hl p (List.mem_cons_self ..)
    obtain ⟨h1, h2⟩ := ih (compareExchange p.1 p.2 x) (fun q hq => hl q (List.mem_cons_of_mem _ hq))
    obtain ⟨s1, s2⟩ := ce_step A B hAB p hp.1 hp.2 x
    simp only [List.foldl_cons]
    exact ⟨fun a ha => (h1 a ha).trans (s1 a ha), fun b hb => (s2 b hb).trans (h2 b hb)⟩

lemma fold_pair (A B : Finset R) (hAB : Disjoint A B) (l : List (R × R)) (x : R → α)
    (hl : ∀ p ∈ l, p.1 ∈ A ∧ p.2 ∈ B) (q : R × R) (hq : q ∈ l) :
    l.foldl (fun y p => compareExchange p.1 p.2 y) x q.1 ≤
      l.foldl (fun y p => compareExchange p.1 p.2 y) x q.2 := by
  obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hq
  have hq' := hl q hq
  have hne : q.1 ≠ q.2 := fun h => Finset.disjoint_left.mp hAB hq'.1 (h ▸ hq'.2)
  rw [List.foldl_append, List.foldl_cons]
  set y := compareExchange q.1 q.2 (l1.foldl (fun y p => compareExchange p.1 p.2 y) x)
  obtain ⟨h1, h2⟩ := fold_mono A B hAB l2 y (fun p hp => hl p (by simp [hp]))
  refine (h1 _ hq'.1).trans (le_trans ?_ (h2 _ hq'.2))
  simp only [y, compareExchange, Function.update_apply, if_neg hne]
  exact min_le_max

lemma ce_perm (i j : R) (x : R → α) : ∃ σ : Equiv.Perm R, compareExchange i j x = x ∘ σ := by
  by_cases hij : i = j
  · subst hij
    refine ⟨Equiv.refl _, ?_⟩
    funext r
    simp only [compareExchange, Function.update_apply, Function.comp_apply, Equiv.refl_apply]
    split_ifs with h
    · subst h; simp
    · rfl
  by_cases hle : x i ≤ x j
  · refine ⟨Equiv.refl _, ?_⟩
    funext r
    simp only [compareExchange, Function.update_apply, Function.comp_apply, Equiv.refl_apply,
      min_eq_left hle, max_eq_right hle]
    split_ifs with h1 h2 <;> subst_vars <;> rfl
  · refine ⟨Equiv.swap i j, ?_⟩
    have hle' : x j ≤ x i := le_of_lt (not_le.mp hle)
    funext r
    simp only [compareExchange, Function.update_apply, Function.comp_apply,
      min_eq_right hle', max_eq_left hle']
    split_ifs with h1 h2
    · subst h1; simp
    · subst h2; simp
    · rw [Equiv.swap_apply_of_ne_of_ne h2 h1]

lemma fold_inj : ∀ (l : List (R × R)) (x : R → α), Function.Injective x →
    Function.Injective (l.foldl (fun y p => compareExchange p.1 p.2 y) x) := by
  intro l
  induction l with
  | nil => intro x hx; simpa using hx
  | cons p l ih =>
    intro x hx
    simp only [List.foldl_cons]
    apply ih
    obtain ⟨σ, hσ⟩ := ce_perm p.1 p.2 x
    rw [hσ]
    exact hx.comp σ.injective

lemma halver_arith (ε y z s a : ℝ) (hε : 0 < ε) (h : (1 - ε) * (1 / ε) * min y (ε * a) < z)
    (hz : z + y ≤ s) (hs : s ≤ a) : y ≤ ε * s := by
  rcases le_total y (ε * a) with hm | hm
  · rw [min_eq_left hm] at h
    have : (1 - ε) * y < ε * z := by
      have := mul_lt_mul_of_pos_left h hε
      field_simp at this ⊢
      linarith
    nlinarith
  · rw [min_eq_right hm] at h
    have : (1 - ε) * (1 / ε) * (ε * a) = (1 - ε) * a := by field_simp
    rw [this] at h
    nlinarith
end

theorem solution {R : Type} [DecidableEq R] {α : Type} [LinearOrder α]
    (A B : Finset R) (hAB : Disjoint A B) (ε : ℝ) (hε : 0 < ε) (k : ℕ) (G : SimpleGraph R)
    (hG : IsExpander G A B k ε) (steps : List (R × R))
    (hsteps : ∀ p : R × R, p ∈ steps ↔ (p.1 ∈ A ∧ p.2 ∈ B ∧ G.Adj p.1 p.2))
    (hnodup : steps.Nodup) (F : R → α) (hF : Function.Injective F) :
    let F' := steps.foldl (fun x p => compareExchange p.1 p.2 x) F
    (∀ S : Finset α, IsLowerSection ((A ∪ B).image F') S → S.card ≤ A.card →
        ((S \ A.image F').card : ℝ) ≤ ε * S.card) ∧
    (∀ S : Finset α, IsUpperSection ((A ∪ B).image F') S → S.card ≤ B.card →
        ((S \ B.image F').card : ℝ) ≤ ε * S.card) := by
  intro F'
  obtain ⟨-, hbip, -, hexpA, hexpB⟩ := hG
  have hl : ∀ p ∈ steps, p.1 ∈ A ∧ p.2 ∈ B := fun p hp => by
    have := (hsteps p).mp hp; exact ⟨this.1, this.2.1⟩
  have hinj : Function.Injective F' := fold_inj steps F hF
  have hpair : ∀ a b, a ∈ A → b ∈ B → G.Adj a b → F' a ≤ F' b := fun a b ha hb hab =>
    fold_pair A B hAB steps F hl (a, b) ((hsteps (a, b)).mpr ⟨ha, hb, hab⟩)
  have hdisjAB : ∀ r, r ∈ A → r ∈ B → False := fun r ha hb => Finset.disjoint_left.mp hAB ha hb
  constructor
  · intro S hS hSA
    obtain ⟨hSJ, hSlow⟩ := hS
    set Y := B.filter (fun r => F' r ∈ S) with hY
    set Z := A.filter (fun r => F' r ∈ S) with hZ
    have h1 : (S \ A.image F').card ≤ Y.card := by
      calc (S \ A.image F').card ≤ (Y.image F').card := by
            apply Finset.card_le_card
            intro x hx
            obtain ⟨hxS, hxA⟩ := Finset.mem_sdiff.mp hx
            obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp (hSJ hxS)
            rcases Finset.mem_union.mp hr with hr | hr
            · exact absurd (Finset.mem_image_of_mem F' hr) hxA
            · exact Finset.mem_image_of_mem F' (Finset.mem_filter.mpr ⟨hr, hxS⟩)
        _ ≤ Y.card := Finset.card_image_le
    have h2 : Z.card + Y.card ≤ S.card := by
      rw [← Finset.card_image_of_injective Z hinj, ← Finset.card_image_of_injective Y hinj,
        ← Finset.card_union_of_disjoint]
      · apply Finset.card_le_card
        intro x hx
        rcases Finset.mem_union.mp hx with hx | hx <;>
        · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
          exact (Finset.mem_filter.mp hr).2
      · rw [Finset.disjoint_left]
        intro x hx1 hx2
        obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx1
        obtain ⟨r', hr', he⟩ := Finset.mem_image.mp hx2
        rw [hinj he] at hr'
        exact hdisjAB r (Finset.mem_filter.mp hr).1 (Finset.mem_filter.mp hr').1
    have h3 : (neighbours G Y).ncard ≤ Z.card := by
      rw [← Set.ncard_coe_finset Z]
      apply Set.ncard_le_ncard _ (Finset.finite_toSet Z)
      rintro v ⟨y, hy, hyv⟩
      obtain ⟨hyB, hyS⟩ := Finset.mem_filter.mp hy
      have hvA : v ∈ A := by
        rcases hbip y v hyv with h | h
        · exact absurd hyB (fun hb => hdisjAB y h.1 hb)
        · exact h.2
      have hle := hpair v y hvA hyB hyv.symm
      have hvJ : F' v ∈ (A ∪ B).image F' :=
        Finset.mem_image_of_mem F' (Finset.mem_union_left _ hvA)
      exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hvA, hSlow _ hvJ _ hyS hle⟩)
    rcases Finset.eq_empty_or_nonempty Y with hY0 | hYne
    · have : (S \ A.image F').card = 0 := by
        have := h1; rw [hY0, Finset.card_empty] at this; omega
      rw [this, Nat.cast_zero]; positivity
    · have hexp := hexpB Y (Finset.filter_subset _ _) hYne
      have hY' : (Y.card : ℝ) ≤ ε * S.card :=
        halver_arith ε Y.card (neighbours G Y).ncard S.card A.card hε hexp
          (by exact_mod_cast (Nat.add_le_add_right h3 _).trans h2) (by exact_mod_cast hSA)
      exact le_trans (by exact_mod_cast h1) hY'
  · intro S hS hSB
    obtain ⟨hSJ, hSup⟩ := hS
    set Y := A.filter (fun r => F' r ∈ S) with hY
    set Z := B.filter (fun r => F' r ∈ S) with hZ
    have h1 : (S \ B.image F').card ≤ Y.card := by
      calc (S \ B.image F').card ≤ (Y.image F').card := by
            apply Finset.card_le_card
            intro x hx
            obtain ⟨hxS, hxB⟩ := Finset.mem_sdiff.mp hx
            obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp (hSJ hxS)
            rcases Finset.mem_union.mp hr with hr | hr
            · exact Finset.mem_image_of_mem F' (Finset.mem_filter.mpr ⟨hr, hxS⟩)
            · exact absurd (Finset.mem_image_of_mem F' hr) hxB
        _ ≤ Y.card := Finset.card_image_le
    have h2 : Z.card + Y.card ≤ S.card := by
      rw [← Finset.card_image_of_injective Z hinj, ← Finset.card_image_of_injective Y hinj,
        ← Finset.card_union_of_disjoint]
      · apply Finset.card_le_card
        intro x hx
        rcases Finset.mem_union.mp hx with hx | hx <;>
        · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
          exact (Finset.mem_filter.mp hr).2
      · rw [Finset.disjoint_left]
        intro x hx1 hx2
        obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx1
        obtain ⟨r', hr', he⟩ := Finset.mem_image.mp hx2
        rw [hinj he] at hr'
        exact hdisjAB r (Finset.mem_filter.mp hr').1 (Finset.mem_filter.mp hr).1
    have h3 : (neighbours G Y).ncard ≤ Z.card := by
      rw [← Set.ncard_coe_finset Z]
      apply Set.ncard_le_ncard _ (Finset.finite_toSet Z)
      rintro v ⟨y, hy, hyv⟩
      obtain ⟨hyA, hyS⟩ := Finset.mem_filter.mp hy
      have hvB : v ∈ B := by
        rcases hbip y v hyv with h | h
        · exact h.2
        · exact absurd h.1 (fun hb => hdisjAB y hyA hb)
      have hle := hpair y v hyA hvB hyv
      have hvJ : F' v ∈ (A ∪ B).image F' :=
        Finset.mem_image_of_mem F' (Finset.mem_union_right _ hvB)
      exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hvB, hSup _ hvJ _ hyS hle⟩)
    rcases Finset.eq_empty_or_nonempty Y with hY0 | hYne
    · have : (S \ B.image F').card = 0 := by
        have := h1; rw [hY0, Finset.card_empty] at this; omega
      rw [this, Nat.cast_zero]; positivity
    · have hexp := hexpA Y (Finset.filter_subset _ _) hYne
      have hY' : (Y.card : ℝ) ≤ ε * S.card :=
        halver_arith ε Y.card (neighbours G Y).ncard S.card B.card hε hexp
          (by exact_mod_cast (Nat.add_le_add_right h3 _).trans h2) (by exact_mod_cast hSB)
      exact le_trans (by exact_mod_cast h1) hY'
