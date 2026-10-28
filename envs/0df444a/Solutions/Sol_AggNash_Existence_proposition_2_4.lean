-- Prove2me | solution 1 for AggNash.Existence.proposition_2_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-24T17:38:47.255949+00:00
-- url     : https://prove2.me/submissions/5e815e01-4cbe-41cf-ba17-66fe0b7302d6

import Mathlib
import Definitions.Def_AggNash_Existence_Model

/-!
# Brouwer library (staged build for 6f936c65)

Stage S1: Sperner's lemma on Kuhn's triangulation of the cube (door-to-door parity,
induction on the dimension) and Brouwer's fixed point theorem on the unit cube.

Everything here is free of Arrow-Debreu definitions.
-/

set_option autoImplicit false


namespace BrouwerLib

open Finset

/-! ## Parity of an involution -/

/-- An involution on a finite set has as many fixed points as the set has elements, mod 2. -/
theorem card_zmod_two_eq_card_fixed {α : Type*} [DecidableEq α] (s : Finset α) (g : α → α)
    (hmem : ∀ a ∈ s, g a ∈ s) (hinv : ∀ a ∈ s, g (g a) = a) :
    ((s.card : ℕ) : ZMod 2) = ((s.filter (fun a => g a = a)).card : ZMod 2) := by
  have h1 : ∑ a ∈ s.filter (fun a => ¬ g a = a), (1 : ZMod 2) = 0 := by
    refine Finset.sum_involution (fun a _ => g a) ?_ ?_ ?_ ?_
    · intro a _; decide
    · intro a ha _; exact (Finset.mem_filter.mp ha).2
    · intro a ha
      obtain ⟨has, hne⟩ := Finset.mem_filter.mp ha
      refine Finset.mem_filter.mpr ⟨hmem a has, ?_⟩
      rw [hinv a has]; exact fun h => hne h.symm
    · intro a ha; exact hinv a (Finset.mem_filter.mp ha).1
  have h2 := Finset.card_filter_add_card_filter_not (s := s) (fun a => g a = a)
  rw [← h2]
  push_cast
  have h3 : (((s.filter (fun a => ¬ g a = a)).card : ℕ) : ZMod 2)
      = ∑ a ∈ s.filter (fun a => ¬ g a = a), (1 : ZMod 2) := by simp
  rw [h3, h1, add_zero]

/-! ## Kuhn simplices -/

/-- Vertex `j` of the Kuhn simplex with base `v` and rank permutation `r`: coordinate `i` is
incremented at step `r i`, so vertex `j` is `v + ∑_{r i < j} e_i`. -/
def kvert {n : ℕ} (v : Fin n → ℕ) (r : Equiv.Perm (Fin n)) (j : ℕ) : Fin n → ℕ :=
  fun i => v i + if ((r i : Fin n) : ℕ) < j then 1 else 0

/-- Door condition: the facet opposite vertex `k` carries every label `1, …, n`. -/
def Door {n : ℕ} (ℓ : (Fin n → ℕ) → ℕ) (v : Fin n → ℕ) (r : Equiv.Perm (Fin n))
    (k : Fin (n + 1)) : Prop :=
  ∀ c, 1 ≤ c → c ≤ n → ∃ j : Fin (n + 1), j ≠ k ∧ ℓ (kvert v r j) = c

/-- A completely labelled Kuhn simplex: its `n + 1` vertices carry all labels `0, …, n`. -/
def FullyLabelled {n : ℕ} (ℓ : (Fin n → ℕ) → ℕ) (v : Fin n → ℕ) (r : Equiv.Perm (Fin n)) :
    Prop :=
  ∀ c, c ≤ n → ∃ j : Fin (n + 1), ℓ (kvert v r j) = c

/-- The base points of the Kuhn simplices of the grid `{0, …, p}^n`. -/
def kgrid (n p : ℕ) : Finset (Fin n → ℕ) := Fintype.piFinset fun _ : Fin n => Finset.range p

theorem mem_kgrid {n p : ℕ} (v : Fin n → ℕ) : v ∈ kgrid n p ↔ ∀ i, v i < p := by
  simp [kgrid, Fintype.mem_piFinset]

/-- On a door, the labels of the other `n` vertices are exactly `1, …, n`. -/
theorem door_image {n : ℕ} {ℓ : (Fin n → ℕ) → ℕ} {v : Fin n → ℕ} {r : Equiv.Perm (Fin n)}
    {k : Fin (n + 1)} (hd : Door ℓ v r k) :
    ((Finset.univ.erase k).image (fun j : Fin (n + 1) => ℓ (kvert v r j))) = Finset.Icc 1 n := by
  apply Finset.eq_of_superset_of_card_ge
  · intro c hc
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hc
    obtain ⟨j, hjk, hj⟩ := hd c h1 h2
    exact Finset.mem_image.mpr ⟨j, Finset.mem_erase.mpr ⟨hjk, Finset.mem_univ _⟩, hj⟩
  · calc ((Finset.univ.erase k).image (fun j : Fin (n + 1) => ℓ (kvert v r j))).card
        ≤ (Finset.univ.erase k).card := Finset.card_image_le
      _ = n := by simp
      _ = (Finset.Icc 1 n).card := by simp

theorem door_label_pos {n : ℕ} {ℓ : (Fin n → ℕ) → ℕ} {v : Fin n → ℕ} {r : Equiv.Perm (Fin n)}
    {k : Fin (n + 1)} (hd : Door ℓ v r k) (j : Fin (n + 1)) (hj : j ≠ k) :
    1 ≤ ℓ (kvert v r j) := by
  have hmem : ℓ (kvert v r j) ∈
      ((Finset.univ.erase k).image (fun j : Fin (n + 1) => ℓ (kvert v r j))) :=
    Finset.mem_image.mpr ⟨j, Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩, rfl⟩
  rw [door_image hd] at hmem
  exact (Finset.mem_Icc.mp hmem).1

theorem door_inj {n : ℕ} {ℓ : (Fin n → ℕ) → ℕ} {v : Fin n → ℕ} {r : Equiv.Perm (Fin n)}
    {k : Fin (n + 1)} (hd : Door ℓ v r k) (j₁ j₂ : Fin (n + 1)) (h₁ : j₁ ≠ k) (h₂ : j₂ ≠ k)
    (h : ℓ (kvert v r j₁) = ℓ (kvert v r j₂)) : j₁ = j₂ := by
  have hinj : Set.InjOn (fun j : Fin (n + 1) => ℓ (kvert v r j)) (Finset.univ.erase k : Finset _) := by
    rw [← Finset.card_image_iff, door_image hd]
    simp
  exact hinj (by simpa using h₁) (by simpa using h₂) h

/-! ## Counting doors -/

section Counting

open scoped Classical

/-- The Kuhn simplices of the grid `{0, …, p}^n`, as (base, rank permutation). -/
noncomputable def ksimp (n p : ℕ) : Finset ((Fin n → ℕ) × Equiv.Perm (Fin n)) :=
  kgrid n p ×ˢ Finset.univ

/-- Pairs (simplex, vertex index) whose opposite facet is a door. -/
noncomputable def kdoors (n p : ℕ) (ℓ : (Fin n → ℕ) → ℕ) :
    Finset (((Fin n → ℕ) × Equiv.Perm (Fin n)) × Fin (n + 1)) :=
  (ksimp n p ×ˢ Finset.univ).filter (fun x => Door ℓ x.1.1 x.1.2 x.2)

/-- The completely labelled Kuhn simplices. -/
noncomputable def kfull (n p : ℕ) (ℓ : (Fin n → ℕ) → ℕ) :
    Finset ((Fin n → ℕ) × Equiv.Perm (Fin n)) :=
  (ksimp n p).filter (fun σ => FullyLabelled ℓ σ.1 σ.2)

/-- Door-to-door inside a simplex: move to the other vertex carrying the same label. -/
noncomputable def gA {n : ℕ} (ℓ : (Fin n → ℕ) → ℕ)
    (x : ((Fin n → ℕ) × Equiv.Perm (Fin n)) × Fin (n + 1)) :
    ((Fin n → ℕ) × Equiv.Perm (Fin n)) × Fin (n + 1) :=
  if h : ∃ j : Fin (n + 1), j ≠ x.2 ∧ ℓ (kvert x.1.1 x.1.2 j) = ℓ (kvert x.1.1 x.1.2 x.2) ∧
      ℓ (kvert x.1.1 x.1.2 x.2) ≠ 0 then (x.1, h.choose) else x

theorem gA_of_zero {n : ℕ} (ℓ : (Fin n → ℕ) → ℕ)
    (x : ((Fin n → ℕ) × Equiv.Perm (Fin n)) × Fin (n + 1))
    (h0 : ℓ (kvert x.1.1 x.1.2 x.2) = 0) : gA ℓ x = x := by
  unfold gA
  rw [dif_neg]
  rintro ⟨j, -, -, h⟩
  exact h h0

theorem gA_spec {n : ℕ} (ℓ : (Fin n → ℕ) → ℕ) (hle : ∀ y, ℓ y ≤ n)
    (x : ((Fin n → ℕ) × Equiv.Perm (Fin n)) × Fin (n + 1))
    (hx : Door ℓ x.1.1 x.1.2 x.2) (hne : ℓ (kvert x.1.1 x.1.2 x.2) ≠ 0) :
    (gA ℓ x).1 = x.1 ∧ (gA ℓ x).2 ≠ x.2 ∧
      ℓ (kvert x.1.1 x.1.2 (gA ℓ x).2) = ℓ (kvert x.1.1 x.1.2 x.2) := by
  have hex : ∃ j : Fin (n + 1), j ≠ x.2 ∧ ℓ (kvert x.1.1 x.1.2 j) = ℓ (kvert x.1.1 x.1.2 x.2) ∧
      ℓ (kvert x.1.1 x.1.2 x.2) ≠ 0 := by
    obtain ⟨j, hj, hj'⟩ := hx _ (Nat.one_le_iff_ne_zero.mpr hne) (hle _)
    exact ⟨j, hj, hj', hne⟩
  unfold gA
  rw [dif_pos hex]
  exact ⟨rfl, hex.choose_spec.1, hex.choose_spec.2.1⟩

theorem gA_mem {n p : ℕ} (ℓ : (Fin n → ℕ) → ℕ) (hle : ∀ y, ℓ y ≤ n)
    (x : ((Fin n → ℕ) × Equiv.Perm (Fin n)) × Fin (n + 1)) (hx : x ∈ kdoors n p ℓ) :
    gA ℓ x ∈ kdoors n p ℓ := by
  by_cases h0 : ℓ (kvert x.1.1 x.1.2 x.2) = 0
  · rw [gA_of_zero ℓ x h0]; exact hx
  obtain ⟨hxs, hd⟩ := Finset.mem_filter.mp hx
  obtain ⟨e1, e2, e3⟩ := gA_spec ℓ hle x hd h0
  refine Finset.mem_filter.mpr ⟨?_, ?_⟩
  · refine Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩
    rw [e1]; exact (Finset.mem_product.mp hxs).1
  · rw [e1]
    intro c hc1 hc2
    obtain ⟨j, hjk, hj⟩ := hd c hc1 hc2
    by_cases hj2 : j = (gA ℓ x).2
    · refine ⟨x.2, fun h => e2 h.symm, ?_⟩
      rw [← e3, ← hj2]; exact hj
    · exact ⟨j, hj2, hj⟩

theorem gA_inv {n p : ℕ} (ℓ : (Fin n → ℕ) → ℕ) (hle : ∀ y, ℓ y ≤ n)
    (x : ((Fin n → ℕ) × Equiv.Perm (Fin n)) × Fin (n + 1)) (hx : x ∈ kdoors n p ℓ) :
    gA ℓ (gA ℓ x) = x := by
  by_cases h0 : ℓ (kvert x.1.1 x.1.2 x.2) = 0
  · rw [gA_of_zero ℓ x h0, gA_of_zero ℓ x h0]
  obtain ⟨-, hd⟩ := Finset.mem_filter.mp hx
  obtain ⟨e1, e2, e3⟩ := gA_spec ℓ hle x hd h0
  have hy := gA_mem ℓ hle x hx
  obtain ⟨-, hdy⟩ := Finset.mem_filter.mp hy
  have h0y : ℓ (kvert (gA ℓ x).1.1 (gA ℓ x).1.2 (gA ℓ x).2) ≠ 0 := by
    rw [e1, e3]; exact h0
  obtain ⟨f1, f2, f3⟩ := gA_spec ℓ hle (gA ℓ x) hdy h0y
  rw [e1] at hdy f3
  have key : (gA ℓ (gA ℓ x)).2 = x.2 := by
    apply door_inj hdy _ _ f2 (fun h => e2 h.symm)
    rw [f3]; exact e3
  exact Prod.ext (by rw [f1, e1]) key

theorem gA_fixed_iff {n p : ℕ} (ℓ : (Fin n → ℕ) → ℕ) (hle : ∀ y, ℓ y ≤ n)
    (x : ((Fin n → ℕ) × Equiv.Perm (Fin n)) × Fin (n + 1)) (hx : x ∈ kdoors n p ℓ) :
    gA ℓ x = x ↔ ℓ (kvert x.1.1 x.1.2 x.2) = 0 := by
  constructor
  · intro h
    by_contra h0
    obtain ⟨-, hd⟩ := Finset.mem_filter.mp hx
    obtain ⟨-, e2, -⟩ := gA_spec ℓ hle x hd h0
    exact e2 (by rw [h])
  · exact gA_of_zero ℓ x

/-- Step A: the number of doors has the parity of the number of completely labelled simplices. -/
theorem stepA {n p : ℕ} (ℓ : (Fin n → ℕ) → ℕ) (hle : ∀ y, ℓ y ≤ n) :
    (((kdoors n p ℓ).card : ℕ) : ZMod 2) = ((kfull n p ℓ).card : ZMod 2) := by
  rw [card_zmod_two_eq_card_fixed (kdoors n p ℓ) (gA ℓ) (gA_mem ℓ hle) (gA_inv ℓ hle)]
  congr 1
  apply Finset.card_bij (fun x _ => x.1)
  · intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
    obtain ⟨hxs, hd⟩ := Finset.mem_filter.mp hx1
    have h0 := (gA_fixed_iff ℓ hle x hx1).mp hx2
    refine Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hxs).1, ?_⟩
    intro c hc
    rcases Nat.eq_zero_or_pos c with rfl | hc0
    · exact ⟨x.2, h0⟩
    · obtain ⟨j, -, hj⟩ := hd c hc0 hc
      exact ⟨j, hj⟩
  · intro x hx y hy hxy
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
    obtain ⟨hy1, hy2⟩ := Finset.mem_filter.mp hy
    obtain ⟨-, hdx⟩ := Finset.mem_filter.mp hx1
    have h0y := (gA_fixed_iff ℓ hle y hy1).mp hy2
    refine Prod.ext hxy ?_
    by_contra hne
    have := door_label_pos hdx y.2 (fun h => hne h.symm)
    rw [hxy, h0y] at this
    exact absurd this (by norm_num)
  · intro σ hσ
    obtain ⟨hσs, hfl⟩ := Finset.mem_filter.mp hσ
    obtain ⟨k, hk⟩ := hfl 0 (Nat.zero_le _)
    have hmem : (σ, k) ∈ kdoors n p ℓ := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hσs, Finset.mem_univ _⟩, ?_⟩
      intro c hc1 hc2
      obtain ⟨j, hj⟩ := hfl c hc2
      refine ⟨j, ?_, hj⟩
      rintro rfl
      omega
    exact ⟨(σ, k), Finset.mem_filter.mpr ⟨hmem, gA_of_zero ℓ _ hk⟩, rfl⟩

/-! ## Door-to-door across facets -/

theorem door_transfer {n : ℕ} {ℓ : (Fin n → ℕ) → ℕ} {v v' : Fin n → ℕ}
    {r r' : Equiv.Perm (Fin n)} {k k' : Fin (n + 1)} (φ : Fin (n + 1) → Fin (n + 1))
    (hφ : ∀ j, j ≠ k → φ j ≠ k' ∧ kvert v' r' (φ j) = kvert v r j) (hd : Door ℓ v r k) :
    Door ℓ v' r' k' := by
  intro c h1 h2
  obtain ⟨j, hj, hjc⟩ := hd c h1 h2
  obtain ⟨ha, hb⟩ := hφ j hj
  exact ⟨φ j, ha, by rw [hb]; exact hjc⟩

theorem finRotate_symm_zero (m : ℕ) : (finRotate (m + 1)).symm 0 = Fin.last m := by
  rw [Equiv.symm_apply_eq, finRotate_last]


theorem val_ne_zero_of_ne {n : ℕ} {a : Fin (n + 1)} (h : a ≠ 0) : (a : ℕ) ≠ 0 :=
  fun h' => h (Fin.ext (by rw [h', Fin.val_zero]))

theorem val_ne_of_ne_last {n : ℕ} {a : Fin (n + 1)} (h : a ≠ Fin.last n) : (a : ℕ) ≠ n :=
  fun h' => h (Fin.ext (by rw [h', Fin.val_last]))

theorem last_ne_zero' (m : ℕ) : (Fin.last (m + 1) : Fin (m + 2)) ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  rw [Fin.val_last, Fin.val_zero] at this
  omega

theorem kvert_move_zero {m : ℕ} (v : Fin (m + 1) → ℕ) (r : Equiv.Perm (Fin (m + 1))) (j : ℕ)
    (hj : j ≤ m) :
    kvert (Function.update v (r.symm 0) (v (r.symm 0) + 1)) (r.trans (finRotate (m + 1)).symm) j
      = kvert v r (j + 1) := by
  funext i
  unfold kvert
  by_cases hi : i = r.symm 0
  · subst hi
    simp only [Function.update_self, Equiv.trans_apply, Equiv.apply_symm_apply,
      finRotate_symm_zero, Fin.val_last, Fin.val_zero]
    split_ifs <;> omega
  · rw [Function.update_of_ne hi, Equiv.trans_apply]
    have hr : r i ≠ 0 := fun h => hi (by rw [← h, Equiv.symm_apply_apply])
    rw [coe_finRotate_symm_of_ne_zero hr]
    have : ((r i : Fin (m + 1)) : ℕ) ≠ 0 := val_ne_zero_of_ne hr
    split_ifs <;> omega

theorem kvert_move_last {m : ℕ} (v : Fin (m + 1) → ℕ) (r : Equiv.Perm (Fin (m + 1))) (j : ℕ)
    (hj : j ≤ m) (hv : 0 < v (r.symm (Fin.last m))) :
    kvert (Function.update v (r.symm (Fin.last m)) (v (r.symm (Fin.last m)) - 1))
      (r.trans (finRotate (m + 1))) (j + 1) = kvert v r j := by
  funext i
  unfold kvert
  by_cases hi : i = r.symm (Fin.last m)
  · subst hi
    simp only [Function.update_self, Equiv.trans_apply, Equiv.apply_symm_apply,
      finRotate_last, Fin.val_last, Fin.val_zero]
    split_ifs <;> omega
  · rw [Function.update_of_ne hi, Equiv.trans_apply]
    have hr : r i ≠ Fin.last m := fun h => hi (by rw [← h, Equiv.symm_apply_apply])
    rw [coe_finRotate_of_ne_last hr]
    split_ifs <;> omega

theorem kvert_swap {m : ℕ} (v : Fin (m + 1) → ℕ) (r : Equiv.Perm (Fin (m + 1)))
    (k : Fin (m + 2)) (hk0 : k ≠ 0) (hkl : k ≠ Fin.last (m + 1)) (j : ℕ) (hj : j ≠ (k : ℕ)) :
    kvert v (r.trans (Equiv.swap (k.pred hk0) (k.castPred hkl))) j = kvert v r j := by
  funext i
  unfold kvert
  rw [Equiv.trans_apply]
  have h1 : ((k.pred hk0 : Fin (m + 1)) : ℕ) = k - 1 := Fin.val_pred k hk0
  have h2 : ((k.castPred hkl : Fin (m + 1)) : ℕ) = k := Fin.coe_castPred k hkl
  have hkpos : (k : ℕ) ≠ 0 := val_ne_zero_of_ne hk0
  rcases eq_or_ne (r i) (k.pred hk0) with ha | ha
  · rw [ha, Equiv.swap_apply_left, h1, h2]
    split_ifs <;> omega
  · rcases eq_or_ne (r i) (k.castPred hkl) with hb | hb
    · rw [hb, Equiv.swap_apply_right, h1, h2]
      split_ifs <;> omega
    · rw [Equiv.swap_apply_of_ne_of_ne ha hb]

/-- Door-to-door across a facet of a Kuhn simplex (dimension `m + 1`). -/
noncomputable def gB {m : ℕ} (p : ℕ)
    (x : ((Fin (m + 1) → ℕ) × Equiv.Perm (Fin (m + 1))) × Fin (m + 2)) :
    ((Fin (m + 1) → ℕ) × Equiv.Perm (Fin (m + 1))) × Fin (m + 2) :=
  if hk0 : x.2 = 0 then
    (if x.1.1 (x.1.2.symm 0) + 1 < p then
      ((Function.update x.1.1 (x.1.2.symm 0) (x.1.1 (x.1.2.symm 0) + 1),
        x.1.2.trans (finRotate (m + 1)).symm), Fin.last (m + 1))
    else x)
  else if hkl : x.2 = Fin.last (m + 1) then
    (if 0 < x.1.1 (x.1.2.symm (Fin.last m)) then
      ((Function.update x.1.1 (x.1.2.symm (Fin.last m)) (x.1.1 (x.1.2.symm (Fin.last m)) - 1),
        x.1.2.trans (finRotate (m + 1))), 0)
    else x)
  else ((x.1.1, x.1.2.trans (Equiv.swap (x.2.pred hk0) (x.2.castPred hkl))), x.2)

theorem gB_zero_move {m p : ℕ} (v : Fin (m + 1) → ℕ) (r : Equiv.Perm (Fin (m + 1)))
    (h : v (r.symm 0) + 1 < p) :
    gB p ((v, r), 0) = ((Function.update v (r.symm 0) (v (r.symm 0) + 1),
        r.trans (finRotate (m + 1)).symm), Fin.last (m + 1)) := by
  simp [gB, h]

theorem gB_zero_stay {m p : ℕ} (v : Fin (m + 1) → ℕ) (r : Equiv.Perm (Fin (m + 1)))
    (h : ¬ v (r.symm 0) + 1 < p) : gB p ((v, r), 0) = ((v, r), 0) := by
  simp [gB, h]

theorem gB_last_move {m p : ℕ} (v : Fin (m + 1) → ℕ) (r : Equiv.Perm (Fin (m + 1)))
    (h : 0 < v (r.symm (Fin.last m))) :
    gB p ((v, r), Fin.last (m + 1)) =
      ((Function.update v (r.symm (Fin.last m)) (v (r.symm (Fin.last m)) - 1),
        r.trans (finRotate (m + 1))), 0) := by
  simp [gB, h, last_ne_zero' m]

theorem gB_last_stay {m p : ℕ} (v : Fin (m + 1) → ℕ) (r : Equiv.Perm (Fin (m + 1)))
    (h : ¬ 0 < v (r.symm (Fin.last m))) :
    gB p ((v, r), Fin.last (m + 1)) = ((v, r), Fin.last (m + 1)) := by
  simp [gB, h, last_ne_zero' m]

theorem gB_mid {m p : ℕ} (v : Fin (m + 1) → ℕ) (r : Equiv.Perm (Fin (m + 1)))
    (k : Fin (m + 2)) (hk0 : k ≠ 0) (hkl : k ≠ Fin.last (m + 1)) :
    gB p ((v, r), k) = ((v, r.trans (Equiv.swap (k.pred hk0) (k.castPred hkl))), k) := by
  simp [gB, hk0, hkl]

theorem gB_mem {m p : ℕ} (ℓ : (Fin (m + 1) → ℕ) → ℕ)
    (x : ((Fin (m + 1) → ℕ) × Equiv.Perm (Fin (m + 1))) × Fin (m + 2))
    (hx : x ∈ kdoors (m + 1) p ℓ) : gB p x ∈ kdoors (m + 1) p ℓ := by
  obtain ⟨⟨v, r⟩, k⟩ := x
  obtain ⟨hxs, hd⟩ := Finset.mem_filter.mp hx
  have hv : ∀ i, v i < p :=
    (mem_kgrid v).mp (Finset.mem_product.mp (Finset.mem_product.mp hxs).1).1
  simp only at hd
  by_cases hk0 : k = 0
  · subst hk0
    by_cases h : v (r.symm 0) + 1 < p
    · rw [gB_zero_move v r h]
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · refine Finset.mem_product.mpr ⟨Finset.mem_product.mpr
          ⟨(mem_kgrid _).mpr ?_, Finset.mem_univ _⟩, Finset.mem_univ _⟩
        intro i
        simp only [Function.update_apply]
        split_ifs with hi
        · exact h
        · exact hv i
      · refine door_transfer (fun j => ⟨(j : ℕ) - 1, by omega⟩) ?_ hd
        intro j hj
        have hj0 : (j : ℕ) ≠ 0 := val_ne_zero_of_ne hj
        have hjlt := j.isLt
        refine ⟨?_, ?_⟩
        · simp only [ne_eq, Fin.ext_iff, Fin.val_last]
          omega
        · have := kvert_move_zero v r ((j : ℕ) - 1) (by omega)
          rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hj0)] at this
          exact this
    · rw [gB_zero_stay v r h]; exact hx
  · by_cases hkl : k = Fin.last (m + 1)
    · subst hkl
      by_cases h : 0 < v (r.symm (Fin.last m))
      · rw [gB_last_move v r h]
        refine Finset.mem_filter.mpr ⟨?_, ?_⟩
        · refine Finset.mem_product.mpr ⟨Finset.mem_product.mpr
            ⟨(mem_kgrid _).mpr ?_, Finset.mem_univ _⟩, Finset.mem_univ _⟩
          intro i
          simp only [Function.update_apply]
          split_ifs with hi
          · have := hv (r.symm (Fin.last m)); omega
          · exact hv i
        · refine door_transfer (fun j => ⟨min ((j : ℕ) + 1) (m + 1), by omega⟩) ?_ hd
          intro j hj
          have hjl : (j : ℕ) ≠ m + 1 := val_ne_of_ne_last hj
          have hjlt := j.isLt
          refine ⟨?_, ?_⟩
          · simp only [ne_eq, Fin.ext_iff, Fin.val_zero]
            omega
          · have := kvert_move_last v r (j : ℕ) (by omega) h
            have e : min ((j : ℕ) + 1) (m + 1) = (j : ℕ) + 1 := by omega
            dsimp only
            rw [e]
            exact this
      · rw [gB_last_stay v r h]; exact hx
    · rw [gB_mid v r k hk0 hkl]
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr
          ⟨(mem_kgrid _).mpr hv, Finset.mem_univ _⟩, Finset.mem_univ _⟩
      · refine door_transfer id ?_ hd
        intro j hj
        exact ⟨hj, kvert_swap v r k hk0 hkl j (fun h => hj (Fin.ext h))⟩

theorem gB_inv {m p : ℕ} (ℓ : (Fin (m + 1) → ℕ) → ℕ)
    (x : ((Fin (m + 1) → ℕ) × Equiv.Perm (Fin (m + 1))) × Fin (m + 2))
    (hx : x ∈ kdoors (m + 1) p ℓ) : gB p (gB p x) = x := by
  obtain ⟨⟨v, r⟩, k⟩ := x
  obtain ⟨hxs, -⟩ := Finset.mem_filter.mp hx
  have hv : ∀ i, v i < p :=
    (mem_kgrid v).mp (Finset.mem_product.mp (Finset.mem_product.mp hxs).1).1
  by_cases hk0 : k = 0
  · subst hk0
    by_cases h : v (r.symm 0) + 1 < p
    · rw [gB_zero_move v r h]
      have e1 : (r.trans (finRotate (m + 1)).symm).symm (Fin.last m) = r.symm 0 := by
        rw [Equiv.symm_trans_apply, Equiv.symm_symm, finRotate_last]
      have h' : 0 < Function.update v (r.symm 0) (v (r.symm 0) + 1)
          ((r.trans (finRotate (m + 1)).symm).symm (Fin.last m)) := by
        rw [e1, Function.update_self]; omega
      rw [gB_last_move _ _ h']
      refine Prod.ext (Prod.ext ?_ ?_) rfl
      · simp only [e1, Function.update_self, Function.update_idem, Nat.add_sub_cancel,
          Function.update_eq_self]
      · exact Equiv.ext fun i => by simp
    · rw [gB_zero_stay v r h, gB_zero_stay v r h]
  · by_cases hkl : k = Fin.last (m + 1)
    · subst hkl
      by_cases h : 0 < v (r.symm (Fin.last m))
      · rw [gB_last_move v r h]
        have e1 : (r.trans (finRotate (m + 1))).symm 0 = r.symm (Fin.last m) := by
          rw [Equiv.symm_trans_apply, finRotate_symm_zero]
        have h' : Function.update v (r.symm (Fin.last m)) (v (r.symm (Fin.last m)) - 1)
            ((r.trans (finRotate (m + 1))).symm 0) + 1 < p := by
          rw [e1, Function.update_self]; have := hv (r.symm (Fin.last m)); omega
        rw [gB_zero_move _ _ h']
        refine Prod.ext (Prod.ext ?_ ?_) rfl
        · simp only [e1, Function.update_self, Function.update_idem, Nat.sub_add_cancel h,
            Function.update_eq_self]
        · exact Equiv.ext fun i => by simp
      · rw [gB_last_stay v r h, gB_last_stay v r h]
    · rw [gB_mid v r k hk0 hkl, gB_mid v _ k hk0 hkl]
      refine Prod.ext (Prod.ext rfl ?_) rfl
      exact Equiv.ext fun i => by simp [Equiv.swap_apply_self]

theorem gB_fixed_facts {m p : ℕ} (ℓ : (Fin (m + 1) → ℕ) → ℕ)
    (h0 : ∀ x (i : Fin (m + 1)), x i = 0 → ℓ x ≠ (i : ℕ) + 1)
    (hP : ∀ x (i : Fin (m + 1)), x i = p → (i : ℕ) + 1 ≤ ℓ x)
    (x : ((Fin (m + 1) → ℕ) × Equiv.Perm (Fin (m + 1))) × Fin (m + 2))
    (hx : x ∈ kdoors (m + 1) p ℓ) (hfix : gB p x = x) :
    x.2 = 0 ∧ x.1.1 0 = p - 1 ∧ x.1.2 0 = 0 := by
  obtain ⟨⟨v, r⟩, k⟩ := x
  obtain ⟨hxs, hd⟩ := Finset.mem_filter.mp hx
  have hv : ∀ i, v i < p :=
    (mem_kgrid v).mp (Finset.mem_product.mp (Finset.mem_product.mp hxs).1).1
  simp only at hd ⊢
  by_cases hk0 : k = 0
  · subst hk0
    by_cases h : v (r.symm 0) + 1 < p
    · rw [gB_zero_move v r h] at hfix
      simp [Fin.ext_iff] at hfix
    · have hvp0 := hv (r.symm 0)
      have hvp : v (r.symm 0) = p - 1 := by omega
      obtain ⟨j, hj, hjl⟩ := hd 1 le_rfl (by omega)
      have hj0 : (j : ℕ) ≠ 0 := val_ne_zero_of_ne hj
      have hcoord : kvert v r j (r.symm 0) = p := by
        simp only [kvert, Equiv.apply_symm_apply, Fin.val_zero]
        rw [if_pos (by omega)]
        omega
      have hle := hP _ _ hcoord
      rw [hjl] at hle
      have hi0 : r.symm 0 = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
      refine ⟨rfl, ?_, ?_⟩
      · rw [← hi0]; exact hvp
      · exact ((Equiv.symm_apply_eq r).mp hi0).symm
  · by_cases hkl : k = Fin.last (m + 1)
    · subst hkl
      by_cases h : 0 < v (r.symm (Fin.last m))
      · rw [gB_last_move v r h] at hfix
        exact absurd (congrArg Prod.snd hfix).symm (last_ne_zero' m)
      · exfalso
        have hv0 : v (r.symm (Fin.last m)) = 0 := by omega
        have hilt := (r.symm (Fin.last m)).isLt
        obtain ⟨j, hj, hjl⟩ := hd ((r.symm (Fin.last m) : ℕ) + 1) (by omega) (by omega)
        have hjm : (j : ℕ) ≤ m := by
          have := j.isLt
          have : (j : ℕ) ≠ m + 1 := val_ne_of_ne_last hj
          omega
        have hcoord : kvert v r j (r.symm (Fin.last m)) = 0 := by
          simp only [kvert, Equiv.apply_symm_apply, Fin.val_last]
          rw [if_neg (by omega)]
          omega
        exact h0 _ _ hcoord hjl
    · rw [gB_mid v r k hk0 hkl] at hfix
      exfalso
      have h2 := congrArg (fun y => y.1.2 (r.symm (k.pred hk0))) hfix
      simp only [Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.swap_apply_left] at h2
      have h3 := congrArg Fin.val h2
      rw [Fin.coe_castPred, Fin.val_pred] at h3
      have hkpos : (k : ℕ) ≠ 0 := val_ne_zero_of_ne hk0
      omega

theorem kvert_face {m : ℕ} (p : ℕ) (hp : 0 < p) (v : Fin m → ℕ) (r : Equiv.Perm (Fin m))
    (j : ℕ) :
    kvert (Fin.cons (p - 1) v : Fin (m + 1) → ℕ) (Equiv.Perm.decomposeFin.symm (0, r)) (j + 1)
      = (Fin.cons p (kvert v r j) : Fin (m + 1) → ℕ) := by
  funext i
  induction i using Fin.cases with
  | zero =>
    simp only [kvert, Fin.cons_zero, Equiv.Perm.decomposeFin_symm_apply_zero, Fin.val_zero]
    rw [if_pos (by omega)]
    omega
  | succ i =>
    simp only [kvert, Fin.cons_succ, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self,
      Equiv.refl_apply, Fin.val_succ]
    split_ifs <;> omega

theorem face_door_iff {m p : ℕ} (hp : 0 < p) (ℓ : (Fin (m + 1) → ℕ) → ℕ)
    (hP0 : ∀ y : Fin m → ℕ, 1 ≤ ℓ (Fin.cons p y)) (v : Fin m → ℕ) (r : Equiv.Perm (Fin m)) :
    Door ℓ (Fin.cons (p - 1) v) (Equiv.Perm.decomposeFin.symm (0, r)) 0 ↔
      FullyLabelled (fun y => ℓ (Fin.cons p y) - 1) v r := by
  constructor
  · intro hd c hc
    obtain ⟨j, hj, hjc⟩ := hd (c + 1) (by omega) (by omega)
    obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.mpr hj
    refine ⟨j', ?_⟩
    rw [Fin.val_succ, kvert_face p hp] at hjc
    simp only
    omega
  · intro hfl c hc1 hc2
    obtain ⟨j', hj'⟩ := hfl (c - 1) (by omega)
    refine ⟨j'.succ, Fin.succ_ne_zero _, ?_⟩
    rw [Fin.val_succ, kvert_face p hp]
    have := hP0 (kvert v r j')
    simp only at hj'
    omega

theorem perm_decompose_of_zero {m : ℕ} (r : Equiv.Perm (Fin (m + 1))) (hr : r 0 = 0) :
    Equiv.Perm.decomposeFin.symm (0, (Equiv.Perm.decomposeFin r).2) = r := by
  obtain ⟨a, e, hae⟩ : ∃ a e, Equiv.Perm.decomposeFin r = (a, e) := ⟨_, _, rfl⟩
  have hr' : r = Equiv.Perm.decomposeFin.symm (a, e) := by rw [← hae, Equiv.symm_apply_apply]
  have ha : a = 0 := by
    have := Equiv.Perm.decomposeFin_symm_apply_zero a e
    rw [← hr', hr] at this
    exact this.symm
  rw [hae, ha, ← ha, ← hr']

theorem fixed_eq_face {m p : ℕ}
    (x : ((Fin (m + 1) → ℕ) × Equiv.Perm (Fin (m + 1))) × Fin (m + 2))
    (e0 : x.2 = 0) (ev : x.1.1 0 = p - 1) (er : x.1.2 0 = 0) :
    ((Fin.cons (p - 1) (Fin.tail x.1.1),
      Equiv.Perm.decomposeFin.symm (0, (Equiv.Perm.decomposeFin x.1.2).2)), 0) = x := by
  obtain ⟨⟨v, r⟩, k⟩ := x
  simp only at e0 ev er ⊢
  rw [perm_decompose_of_zero r er, e0, ← ev, Fin.cons_self_tail]

/-- Step B: the number of doors has the parity of the number of completely labelled simplices
of the face `x₀ = p`, with the induced labelling. -/
theorem stepB {m p : ℕ} (hp : 0 < p) (ℓ : (Fin (m + 1) → ℕ) → ℕ)
    (h0 : ∀ x (i : Fin (m + 1)), x i = 0 → ℓ x ≠ (i : ℕ) + 1)
    (hP : ∀ x (i : Fin (m + 1)), x i = p → (i : ℕ) + 1 ≤ ℓ x) :
    (((kdoors (m + 1) p ℓ).card : ℕ) : ZMod 2) =
      ((kfull m p (fun y => ℓ (Fin.cons p y) - 1)).card : ZMod 2) := by
  have hP0 : ∀ y : Fin m → ℕ, 1 ≤ ℓ (Fin.cons p y) := fun y => by
    simpa using hP (Fin.cons p y) 0 (by simp)
  rw [card_zmod_two_eq_card_fixed (kdoors (m + 1) p ℓ) (gB p) (gB_mem ℓ) (gB_inv ℓ)]
  congr 1
  apply Finset.card_nbij' (fun x => (Fin.tail x.1.1, (Equiv.Perm.decomposeFin x.1.2).2))
    (fun σ => ((Fin.cons (p - 1) σ.1, Equiv.Perm.decomposeFin.symm (0, σ.2)), 0))
  · intro x hx
    rw [Finset.mem_coe] at hx ⊢
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
    obtain ⟨e0, ev, er⟩ := gB_fixed_facts ℓ h0 hP x hx1 hx2
    obtain ⟨hxs, hd⟩ := Finset.mem_filter.mp hx1
    have hv : ∀ i, x.1.1 i < p :=
      (mem_kgrid _).mp (Finset.mem_product.mp (Finset.mem_product.mp hxs).1).1
    have hd' : Door ℓ (Fin.cons (p - 1) (Fin.tail x.1.1))
        (Equiv.Perm.decomposeFin.symm (0, (Equiv.Perm.decomposeFin x.1.2).2)) 0 := by
      have h := fixed_eq_face x e0 ev er
      rw [← h] at hd
      exact hd
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨(mem_kgrid _).mpr (fun i => hv i.succ), Finset.mem_univ _⟩, ?_⟩
    exact (face_door_iff hp ℓ hP0 _ _).mp hd'
  · intro σ hσ
    rw [Finset.mem_coe] at hσ ⊢
    obtain ⟨hσs, hfl⟩ := Finset.mem_filter.mp hσ
    have hv : ∀ i, σ.1 i < p := (mem_kgrid _).mp (Finset.mem_product.mp hσs).1
    have hmem : ((Fin.cons (p - 1) σ.1, Equiv.Perm.decomposeFin.symm (0, σ.2)), 0)
        ∈ kdoors (m + 1) p ℓ := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr
        ⟨(mem_kgrid _).mpr ?_, Finset.mem_univ _⟩, Finset.mem_univ _⟩,
        (face_door_iff hp ℓ hP0 _ _).mpr hfl⟩
      intro i
      induction i using Fin.cases with
      | zero => simp only [Fin.cons_zero]; omega
      | succ i => simp only [Fin.cons_succ]; exact hv i
    refine Finset.mem_filter.mpr ⟨hmem, ?_⟩
    have hR : (Equiv.Perm.decomposeFin.symm (0, σ.2)).symm 0 = 0 := by
      rw [Equiv.symm_apply_eq, Equiv.Perm.decomposeFin_symm_apply_zero]
    apply gB_zero_stay
    rw [hR, Fin.cons_zero]
    omega
  · intro x hx
    rw [Finset.mem_coe] at hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
    obtain ⟨e0, ev, er⟩ := gB_fixed_facts ℓ h0 hP x hx1 hx2
    exact fixed_eq_face x e0 ev er
  · intro σ _
    simp

/-- The number of completely labelled Kuhn simplices is odd (induction on the dimension). -/
theorem kfull_card_odd (n : ℕ) : ∀ (p : ℕ), 0 < p → ∀ (ℓ : (Fin n → ℕ) → ℕ), (∀ y, ℓ y ≤ n) →
    (∀ x (i : Fin n), x i = 0 → ℓ x ≠ (i : ℕ) + 1) →
    (∀ x (i : Fin n), x i = p → (i : ℕ) + 1 ≤ ℓ x) → Odd (kfull n p ℓ).card := by
  induction n with
  | zero =>
    intro p hp ℓ hle h0 hP
    have hfull : kfull 0 p ℓ = ksimp 0 p := by
      apply Finset.filter_true_of_mem
      intro σ _ c hc
      refine ⟨0, ?_⟩
      have := hle (kvert σ.1 σ.2 0)
      simp only [Fin.val_zero]
      omega
    rw [hfull]
    have hc : (ksimp 0 p).card = 1 := by
      simp [ksimp, kgrid]
    rw [hc]
    exact odd_one
  | succ m ih =>
    intro p hp ℓ hle h0 hP
    have hA := stepA (p := p) ℓ hle
    have hB := stepB hp ℓ h0 hP
    have hodd := ih p hp (fun y => ℓ (Fin.cons p y) - 1)
      (fun y => by
        show ℓ (Fin.cons p y) - 1 ≤ m
        have := hle (Fin.cons p y)
        omega)
      (fun y i hy => by
        show ℓ (Fin.cons p y) - 1 ≠ (i : ℕ) + 1
        have h1 := h0 (Fin.cons p y) i.succ (by simpa using hy)
        have h2 := hP (Fin.cons p y) 0 (by simp)
        simp only [Fin.val_succ, Fin.val_zero] at h1 h2
        omega)
      (fun y i hy => by
        show (i : ℕ) + 1 ≤ ℓ (Fin.cons p y) - 1
        have h1 := hP (Fin.cons p y) i.succ (by simpa using hy)
        simp only [Fin.val_succ] at h1
        omega)
    rw [← ZMod.natCast_eq_one_iff_odd] at hodd ⊢
    rw [← hA, hB, hodd]

end Counting

/-- **Sperner's lemma** on Kuhn's triangulation of the cube `[0, p]^n`.

Label the lattice points `x : Fin n → ℕ` by `ℓ x ∈ {0, …, n}` such that a point with `x i = 0`
never carries label `i + 1`, and a point with `x i = p` carries a label `≥ i + 1`. Then some
Kuhn simplex (base `v` with `v i < p`, vertices `kvert v r j`, `j = 0, …, n`) is completely
labelled. (In fact their number is odd: `kfull_card_odd`.) -/
theorem sperner_kuhn (n p : ℕ) (hp : 0 < p) (ℓ : (Fin n → ℕ) → ℕ) (hle : ∀ y, ℓ y ≤ n)
    (h0 : ∀ x (i : Fin n), x i = 0 → ℓ x ≠ (i : ℕ) + 1)
    (hP : ∀ x (i : Fin n), x i = p → (i : ℕ) + 1 ≤ ℓ x) :
    ∃ (v : Fin n → ℕ) (r : Equiv.Perm (Fin n)), (∀ i, v i < p) ∧ FullyLabelled ℓ v r := by
  classical
  obtain ⟨σ, hσ⟩ := Finset.card_pos.mp (kfull_card_odd n p hp ℓ hle h0 hP).pos
  obtain ⟨hs, hfl⟩ := Finset.mem_filter.mp hσ
  exact ⟨σ.1, σ.2, (mem_kgrid _).mp (Finset.mem_product.mp hs).1, hfl⟩

/-! ## Brouwer's fixed point theorem on the unit cube -/

section BrouwerCube

open Filter Topology

theorem mem_cube_iff {N : ℕ} (x : Fin N → ℝ) :
    x ∈ Set.Icc (0 : Fin N → ℝ) 1 ↔ ∀ i, 0 ≤ x i ∧ x i ≤ 1 := by
  simp only [Set.mem_Icc, Pi.le_def, Pi.zero_apply, Pi.one_apply]
  exact ⟨fun h i => ⟨h.1 i, h.2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩

/-- The point of the unit cube represented by the lattice point `x` of `{0, …, p}^N`
(coordinates clamped at `p`). -/
noncomputable def cubePt {N : ℕ} (p : ℕ) (x : Fin N → ℕ) : Fin N → ℝ :=
  fun i => ((min (x i) p : ℕ) : ℝ) / p

theorem cubePt_mem {N p : ℕ} (hp : 0 < p) (x : Fin N → ℕ) :
    cubePt p x ∈ Set.Icc (0 : Fin N → ℝ) 1 := by
  rw [mem_cube_iff]
  intro i
  have hp' : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  refine ⟨by unfold cubePt; positivity, ?_⟩
  unfold cubePt
  rw [div_le_one hp']
  exact_mod_cast min_le_right _ _

open scoped Classical in
/-- Kuhn's labelling for a self-map `f` of the cube: `0` if no coordinate is pushed down,
otherwise `1 +` the largest coordinate `i` with `x i ≠ 0` and `f x i ≤ x i`. -/
noncomputable def cubeLabel {N : ℕ} (f : (Fin N → ℝ) → (Fin N → ℝ)) (p : ℕ) (x : Fin N → ℕ) :
    ℕ :=
  (Finset.univ.filter (fun i : Fin N => cubePt p x i ≠ 0 ∧ f (cubePt p x) i ≤ cubePt p x i)).sup
    (fun i => (i : ℕ) + 1)

theorem cubeLabel_le {N : ℕ} (f : (Fin N → ℝ) → (Fin N → ℝ)) (p : ℕ) (x : Fin N → ℕ) :
    cubeLabel f p x ≤ N := by
  unfold cubeLabel
  apply Finset.sup_le
  intro i _
  exact i.isLt

theorem cubeLabel_mem {N : ℕ} (f : (Fin N → ℝ) → (Fin N → ℝ)) (p : ℕ) (x : Fin N → ℕ)
    (i : Fin N) (h : cubeLabel f p x = (i : ℕ) + 1) :
    cubePt p x i ≠ 0 ∧ f (cubePt p x) i ≤ cubePt p x i := by
  classical
  unfold cubeLabel at h
  set s := Finset.univ.filter
    (fun i : Fin N => cubePt p x i ≠ 0 ∧ f (cubePt p x) i ≤ cubePt p x i) with hs
  rcases s.eq_empty_or_nonempty with he | hne
  · rw [he, Finset.sup_empty] at h
    exact absurd h (by simp)
  · obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup s hne (fun i : Fin N => (i : ℕ) + 1)
    rw [hjeq] at h
    have hji : j = i := Fin.ext (by have h' : (j : ℕ) + 1 = (i : ℕ) + 1 := h; omega)
    subst hji
    exact (Finset.mem_filter.mp hj).2

theorem cubeLabel_zero {N : ℕ} (f : (Fin N → ℝ) → (Fin N → ℝ))
    (hmap : Set.MapsTo f (Set.Icc 0 1) (Set.Icc 0 1)) (p : ℕ) (hp : 0 < p) (x : Fin N → ℕ)
    (h : cubeLabel f p x = 0) (i : Fin N) : cubePt p x i ≤ f (cubePt p x) i := by
  classical
  by_contra hlt
  rw [not_le] at hlt
  have hfx := (mem_cube_iff _).mp (hmap (cubePt_mem hp x)) i
  have hmem : i ∈ Finset.univ.filter
      (fun i : Fin N => cubePt p x i ≠ 0 ∧ f (cubePt p x) i ≤ cubePt p x i) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hlt.le⟩
    intro h0
    rw [h0] at hlt
    linarith [hfx.1]
  have := Finset.le_sup (f := fun i : Fin N => (i : ℕ) + 1) hmem
  unfold cubeLabel at h
  omega

theorem cubeLabel_h0 {N : ℕ} (f : (Fin N → ℝ) → (Fin N → ℝ)) (p : ℕ) (x : Fin N → ℕ)
    (i : Fin N) (hx : x i = 0) : cubeLabel f p x ≠ (i : ℕ) + 1 := by
  intro h
  have := (cubeLabel_mem f p x i h).1
  apply this
  simp [cubePt, hx]

theorem cubeLabel_hP {N : ℕ} (f : (Fin N → ℝ) → (Fin N → ℝ))
    (hmap : Set.MapsTo f (Set.Icc 0 1) (Set.Icc 0 1)) (p : ℕ) (hp : 0 < p) (x : Fin N → ℕ)
    (i : Fin N) (hx : x i = p) : (i : ℕ) + 1 ≤ cubeLabel f p x := by
  classical
  have hp' : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hpt : cubePt p x i = 1 := by
    simp only [cubePt, hx, min_self]
    exact div_self hp'.ne'
  have hfx := (mem_cube_iff _).mp (hmap (cubePt_mem hp x)) i
  have hmem : i ∈ Finset.univ.filter
      (fun i : Fin N => cubePt p x i ≠ 0 ∧ f (cubePt p x) i ≤ cubePt p x i) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
    · rw [hpt]; exact one_ne_zero
    · rw [hpt]; exact hfx.2
  have := Finset.le_sup (f := fun i : Fin N => (i : ℕ) + 1) hmem
  unfold cubeLabel
  exact this

theorem dist_cubePt_kvert_le {N p : ℕ} (hp : 0 < p) (v : Fin N → ℕ) (hv : ∀ i, v i < p)
    (r : Equiv.Perm (Fin N)) (j : ℕ) :
    dist (cubePt p (kvert v r j)) (cubePt p v) ≤ 1 / (p : ℝ) := by
  have hp' : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  rw [dist_pi_le_iff (by positivity)]
  intro i
  have h1 : min (kvert v r j i) p = kvert v r j i :=
    min_eq_left (by unfold kvert; have := hv i; split_ifs <;> omega)
  have h2 : min (v i) p = v i := min_eq_left (hv i).le
  simp only [cubePt, h1, h2, Real.dist_eq]
  unfold kvert
  split_ifs
  · push_cast
    rw [show ((v i : ℝ) + 1) / p - v i / p = 1 / p by ring, abs_of_pos (by positivity)]
  · simp only [add_zero, sub_self, abs_zero]
    positivity

/-- Approximate fixed points from Sperner's lemma: at mesh `1 / (k + 1)` there is a base point
`b`, a nearby point `a` pushed up in every coordinate, and for each coordinate `i` a nearby
point `c i` pushed down in coordinate `i`. -/
theorem cube_approx {N : ℕ} (f : (Fin N → ℝ) → (Fin N → ℝ))
    (hmap : Set.MapsTo f (Set.Icc 0 1) (Set.Icc 0 1)) (k : ℕ) :
    ∃ (b a : Fin N → ℝ) (c : Fin N → Fin N → ℝ),
      b ∈ Set.Icc (0 : Fin N → ℝ) 1 ∧ a ∈ Set.Icc (0 : Fin N → ℝ) 1 ∧
      (∀ i, c i ∈ Set.Icc (0 : Fin N → ℝ) 1) ∧
      dist a b ≤ 1 / ((k : ℝ) + 1) ∧ (∀ i, dist (c i) b ≤ 1 / ((k : ℝ) + 1)) ∧
      (∀ i, a i ≤ f a i) ∧ (∀ i, f (c i) i ≤ c i i) := by
  have hp : 0 < k + 1 := Nat.succ_pos k
  obtain ⟨v, r, hv, hfl⟩ := sperner_kuhn N (k + 1) hp (cubeLabel f (k + 1))
    (cubeLabel_le f (k + 1)) (fun x i hx => cubeLabel_h0 f (k + 1) x i hx)
    (fun x i hx => cubeLabel_hP f hmap (k + 1) hp x i hx)
  obtain ⟨j0, hj0⟩ := hfl 0 (Nat.zero_le _)
  have hJ : ∀ i : Fin N, ∃ j : Fin (N + 1), cubeLabel f (k + 1) (kvert v r j) = (i : ℕ) + 1 :=
    fun i => hfl _ (by omega)
  choose J hJ using hJ
  have hk : (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 := by push_cast; ring
  refine ⟨cubePt (k + 1) v, cubePt (k + 1) (kvert v r j0),
    fun i => cubePt (k + 1) (kvert v r (J i)),
    cubePt_mem hp v, cubePt_mem hp _, fun i => cubePt_mem hp _, ?_, ?_, ?_, ?_⟩
  · rw [← hk]; exact dist_cubePt_kvert_le hp v hv r _
  · intro i; rw [← hk]; exact dist_cubePt_kvert_le hp v hv r _
  · exact cubeLabel_zero f hmap (k + 1) hp _ hj0
  · intro i
    exact (cubeLabel_mem f (k + 1) _ i (hJ i)).2

/-- **Brouwer's fixed point theorem** on the unit cube `[0, 1]^N`, for `f` continuous on the
cube and mapping it into itself. -/
theorem brouwer_cube_Icc {N : ℕ} (f : (Fin N → ℝ) → (Fin N → ℝ))
    (hf : ContinuousOn f (Set.Icc 0 1)) (hmap : Set.MapsTo f (Set.Icc 0 1) (Set.Icc 0 1)) :
    ∃ x ∈ Set.Icc (0 : Fin N → ℝ) 1, f x = x := by
  choose b a c hb ha hc hab hcb ha' hc' using cube_approx f hmap
  obtain ⟨x, hx, φ, hφ, hlim⟩ :=
    (isCompact_Icc (a := (0 : Fin N → ℝ)) (b := 1)).tendsto_subseq hb
  refine ⟨x, hx, ?_⟩
  have hε : Tendsto (fun k => 1 / ((φ k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  have hlimA : Tendsto (fun k => a (φ k)) atTop (𝓝 x) := by
    refine hlim.congr_dist ?_
    refine squeeze_zero (fun _ => dist_nonneg) (fun k => ?_) hε
    rw [dist_comm]
    exact hab (φ k)
  have hlimC : ∀ i, Tendsto (fun k => c (φ k) i) atTop (𝓝 x) := fun i => by
    refine hlim.congr_dist ?_
    refine squeeze_zero (fun _ => dist_nonneg) (fun k => ?_) hε
    rw [dist_comm]
    exact hcb (φ k) i
  have hfx : ∀ u : ℕ → Fin N → ℝ, (∀ k, u k ∈ Set.Icc (0 : Fin N → ℝ) 1) →
      Tendsto u atTop (𝓝 x) → Tendsto (fun k => f (u k)) atTop (𝓝 (f x)) := fun u hu hlu =>
    (hf x hx).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hlu, Filter.Eventually.of_forall hu⟩)
  funext i
  apply le_antisymm
  · have h1 := ((continuous_apply i).tendsto (f x)).comp
      (hfx (fun k => c (φ k) i) (fun k => hc (φ k) i) (hlimC i))
    have h2 := ((continuous_apply i).tendsto x).comp (hlimC i)
    exact le_of_tendsto_of_tendsto' h1 h2 (fun k => hc' (φ k) i)
  · have h1 := ((continuous_apply i).tendsto (f x)).comp
      (hfx (fun k => a (φ k)) (fun k => ha (φ k)) hlimA)
    have h2 := ((continuous_apply i).tendsto x).comp hlimA
    exact le_of_tendsto_of_tendsto' h2 h1 (fun k => ha' (φ k) i)

/-- **Brouwer's fixed point theorem** on the unit cube, coordinate form, for `f` continuous on
the cube. -/
theorem brouwer_cube_continuousOn (N : ℕ) (f : (Fin N → ℝ) → (Fin N → ℝ))
    (hf : ContinuousOn f {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1})
    (hmap : ∀ x, (∀ i, 0 ≤ x i ∧ x i ≤ 1) → ∀ i, 0 ≤ f x i ∧ f x i ≤ 1) :
    ∃ x, (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ f x = x := by
  have hset : {x : Fin N → ℝ | ∀ i, 0 ≤ x i ∧ x i ≤ 1} = Set.Icc 0 1 :=
    Set.ext fun x => (mem_cube_iff x).symm
  rw [hset] at hf
  obtain ⟨x, hx, hfx⟩ := brouwer_cube_Icc f hf
    (fun x hx => (mem_cube_iff _).mpr (hmap x ((mem_cube_iff x).mp hx)))
  exact ⟨x, (mem_cube_iff x).mp hx, hfx⟩

/-- **Brouwer's fixed point theorem** on the unit cube: a continuous `f : ℝ^N → ℝ^N` mapping
the cube `{x | ∀ i, 0 ≤ x i ≤ 1}` into itself has a fixed point in the cube. -/
theorem brouwer_cube (N : ℕ) (f : (Fin N → ℝ) → (Fin N → ℝ)) (hf : Continuous f)
    (hmap : ∀ x, (∀ i, 0 ≤ x i ∧ x i ≤ 1) → ∀ i, 0 ≤ f x i ∧ f x i ≤ 1) :
    ∃ x, (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ f x = x :=
  brouwer_cube_continuousOn N f hf.continuousOn hmap

end BrouwerCube

end BrouwerLib


set_option autoImplicit false

namespace AggNashP

open AggNash.Existence

/-! ### Elementary facts about aggregates and the convexified cost -/

theorem sum_update_eq {n d q : ℕ} (A : Fin n → (E d →L[ℝ] E q)) (u : Fin n → E d) (i : Fin n)
    (w : E d) :
    ∑ j, A j (Function.update u i w j) = ∑ j, A j (u j) + (A i w - A i (u i)) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have : ∑ j ∈ Finset.univ.erase i, A j (Function.update u i w j)
      = ∑ j ∈ Finset.univ.erase i, A j (u j) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [this, Function.update_self]
  abel

theorem agg_update_dist {n d q : ℕ} (A : Fin n → (E d →L[ℝ] E q)) (M : ℝ)
    (hA : ∀ i, ‖A i‖ ≤ M) (u v : Fin n → E d) (i : Fin n) (w : E d) :
    ‖aggregate A (Function.update u i w) - aggregate A (Function.update v i w)‖
      ≤ (n : ℝ)⁻¹ * (‖∑ j, A j (u j) - ∑ j, A j (v j)‖ + M * ‖u i - v i‖) := by
  unfold aggregate
  rw [← smul_sub, norm_smul, sum_update_eq, sum_update_eq, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h1 : ∑ j, A j (u j) + (A i w - A i (u i)) - (∑ j, A j (v j) + (A i w - A i (v i)))
      = (∑ j, A j (u j) - ∑ j, A j (v j)) - A i (u i - v i) := by
    rw [map_sub]; abel
  rw [h1]
  refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
  exact ((A i).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hA i) (norm_nonneg _))

theorem aggSet_subset {n d q : ℕ} {X : Fin n → Set (E d)} {A : Fin n → (E d →L[ℝ] E q)}
    {Ω : Set (E q)} {Δ M : ℝ} (hstd : StandingHyp X A Ω Δ M) : aggSet X A ⊆ Ω :=
  subset_of_mem_nhdsSet hstd.2.2.2.2.2.2

theorem agg_mem {n d q : ℕ} {X : Fin n → Set (E d)} {A : Fin n → (E d →L[ℝ] E q)}
    {Ω : Set (E q)} {Δ M : ℝ} (hstd : StandingHyp X A Ω Δ M) (x : Fin n → E d)
    (hx : ∀ j, x j ∈ convexHull ℝ (X j)) : aggregate A x ∈ Ω :=
  aggSet_subset hstd ⟨x, hx, rfl⟩

theorem update_mem_conv {n d : ℕ} {X : Fin n → Set (E d)} (x : Fin n → E d)
    (hx : ∀ j, x j ∈ convexHull ℝ (X j)) (i : Fin n) (z : E d) (hz : z ∈ convexHull ℝ (X i)) :
    ∀ j, Function.update x i z j ∈ convexHull ℝ (X j) := by
  intro j
  by_cases h : j = i
  · subst h; simpa using hz
  · rw [Function.update_of_ne h]; exact hx j

theorem dist_le_conv {n d : ℕ} {X : Fin n → Set (E d)} {Δ : ℝ} (hc : ∀ i, IsCompact (X i))
    (hdiam : ∀ i, Metric.diam (X i) ≤ Δ) (i : Fin n) (a b : E d)
    (ha : a ∈ convexHull ℝ (X i)) (hb : b ∈ convexHull ℝ (X i)) : ‖a - b‖ ≤ Δ := by
  rw [← dist_eq_norm]
  have hB : Bornology.IsBounded (convexHull ℝ (X i)) :=
    isBounded_convexHull.2 (hc i).isBounded
  exact (Metric.dist_le_diam_of_mem hB ha hb).trans ((convexHull_diam (X i)).le.trans (hdiam i))

/-- The set whose infimum is the convexified cost is bounded below. -/
theorem convCost_bdd {n d q : ℕ} {X : Fin n → Set (E d)} {A : Fin n → (E d →L[ℝ] E q)}
    {θ : Fin n → E d → E q → ℝ} {Ω : Set (E q)} {Δ M H γ : ℝ}
    (hstd : StandingHyp X A Ω Δ M) (hA1 : Assumption1 X Ω θ H γ) (i : Fin n)
    (x : Fin n → E d) (hx : ∀ j, x j ∈ convexHull ℝ (X j)) :
    ∃ m, (∀ z ∈ X i, m ≤ cost θ A i (Function.update x i z)) ∧
      BddBelow {v | ∃ α ∈ stdSimplex ℝ (Fin (d + 1)), ∃ z : Fin (d + 1) → E d, (∀ k, z k ∈ X i) ∧
        ∑ k, α k • z k = x i ∧ v = ∑ k, α k * cost θ A i (Function.update x i (z k))} := by
  obtain ⟨hc, hne, hΔ, hdiam, hM, hA, -⟩ := id hstd
  obtain ⟨hlsc, hH, hγ, hhol⟩ := hA1
  set y0 := aggregate A x
  have hy0 : y0 ∈ Ω := agg_mem hstd x hx
  obtain ⟨m0, hm0⟩ := (hlsc i y0 hy0).bddBelow_of_isCompact (hc i)
  set B : ℝ := (n : ℝ)⁻¹ * (M * Δ)
  have hlow : ∀ z ∈ X i, m0 - H * B ^ γ ≤ cost θ A i (Function.update x i z) := by
    intro z hz
    have hzc : z ∈ convexHull ℝ (X i) := subset_convexHull ℝ _ hz
    have hmem : aggregate A (Function.update x i z) ∈ Ω :=
      agg_mem hstd _ (update_mem_conv x hx i z hzc)
    have h1 := hhol i z hz y0 hy0 _ hmem
    have h2 : m0 ≤ θ i z y0 := hm0 ⟨z, hz, rfl⟩
    have hd : ‖aggregate A (Function.update x i z) - y0‖ ≤ B := by
      have he : aggregate A (Function.update x i z) - y0 = (n : ℝ)⁻¹ • A i (z - x i) := by
        simp only [y0, aggregate]
        rw [← smul_sub, sum_update_eq, map_sub]
        congr 1; abel
      rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have hzx : ‖z - x i‖ ≤ Δ := dist_le_conv hc hdiam i z (x i) hzc (hx i)
      exact ((A i).le_opNorm _).trans (mul_le_mul (hA i) hzx (norm_nonneg _) hM.le)
    have hp : ‖aggregate A (Function.update x i z) - y0‖ ^ γ ≤ B ^ γ :=
      Real.rpow_le_rpow (norm_nonneg _) hd hγ.le
    unfold cost
    simp only [Function.update_self]
    have := (abs_le.1 h1).1
    nlinarith [mul_le_mul_of_nonneg_left hp hH.le]
  refine ⟨m0 - H * B ^ γ, hlow, m0 - H * B ^ γ, ?_⟩
  rintro v ⟨α, hα, z, hz, -, rfl⟩
  calc m0 - H * B ^ γ = ∑ k, α k * (m0 - H * B ^ γ) := by
        rw [← Finset.sum_mul, hα.2, one_mul]
    _ ≤ ∑ k, α k * cost θ A i (Function.update x i (z k)) :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hlow _ (hz k)) (hα.1 k)

theorem convCost_le_cost {n d q : ℕ} {X : Fin n → Set (E d)} {A : Fin n → (E d →L[ℝ] E q)}
    {θ : Fin n → E d → E q → ℝ} {Ω : Set (E q)} {Δ M H γ : ℝ}
    (hstd : StandingHyp X A Ω Δ M) (hA1 : Assumption1 X Ω θ H γ) (i : Fin n)
    (x : Fin n → E d) (hx : ∀ j, x j ∈ convexHull ℝ (X j)) (hxi : x i ∈ X i) :
    convCost X θ A i x ≤ cost θ A i x := by
  obtain ⟨m, -, hb⟩ := convCost_bdd hstd hA1 i x hx
  unfold convCost
  apply csInf_le hb
  refine ⟨Pi.single 0 1, single_mem_stdSimplex _ _, fun _ => x i, fun _ => hxi, ?_, ?_⟩
  · rw [← Finset.sum_smul]; simp
  · rw [← Finset.sum_mul]; simp

/-- Facts about a generator at a PNE of the convexified game. -/
theorem gen_facts {n d q : ℕ} {X : Fin n → Set (E d)} {A : Fin n → (E d →L[ℝ] E q)}
    {θ : Fin n → E d → E q → ℝ} {Ω : Set (E q)} {Δ M H γ : ℝ}
    (hstd : StandingHyp X A Ω Δ M) (hA1 : Assumption1 X Ω θ H γ) (xt : Fin n → E d)
    (hxt : IsEpsPNE (fun i => convexHull ℝ (X i)) (convCost X θ A) 0 xt) (i : Fin n)
    (Z : Set (E d)) (hZ : IsGenerator X θ A i xt Z) :
    (∀ y ∈ Z, cost θ A i (Function.update xt i y) = convCost X θ A i xt) ∧
    (∀ y ∈ X i, convCost X θ A i xt ≤ cost θ A i (Function.update xt i y)) ∧
    Z ⊆ X i ∧ Z.Finite ∧ xt i ∈ convexHull ℝ Z := by
  have G2 : ∀ y ∈ X i, convCost X θ A i xt ≤ cost θ A i (Function.update xt i y) := by
    intro y hy
    have hc := convCost_le_cost hstd hA1 i (Function.update xt i y)
      (update_mem_conv xt hxt.1 i y (subset_convexHull ℝ _ hy)) (by simpa using hy)
    have hp := hxt.2 i y (subset_convexHull ℝ _ hy)
    linarith
  obtain ⟨α, hα, z, hz, hsum, hval, rfl⟩ := hZ
  refine ⟨?_, G2, ?_, ?_, ?_⟩
  · rintro y ⟨k, hk, rfl⟩
    set c := convCost X θ A i xt
    have hnn : ∀ l ∈ Finset.univ, 0 ≤ α l * (cost θ A i (Function.update xt i (z l)) - c) :=
      fun l _ => mul_nonneg (hα.1 l) (sub_nonneg.2 (G2 _ (hz l)))
    have hs0 : ∑ l, α l * (cost θ A i (Function.update xt i (z l)) - c) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hα.2, one_mul, hval, sub_self]
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hs0 k (Finset.mem_univ k)
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hk.ne'
    · linarith
  · rintro y ⟨k, -, rfl⟩; exact hz k
  · exact (Set.finite_range z).subset (by rintro y ⟨k, -, rfl⟩; exact ⟨k, rfl⟩)
  · have hne : ∀ k ∈ (Finset.univ : Finset (Fin (d + 1))), α k ≠ 0 → 0 < α k :=
      fun k _ h => lt_of_le_of_ne (hα.1 k) (Ne.symm h)
    have e1 : ∑ k ∈ Finset.univ.filter (fun k => 0 < α k), α k • z k = xt i := by
      rw [Finset.sum_filter_of_ne, hsum]
      intro k hk h; exact hne k hk (fun h0 => h (by simp [h0]))
    have e2 : ∑ k ∈ Finset.univ.filter (fun k => 0 < α k), α k = 1 := by
      rw [Finset.sum_filter_of_ne, hα.2]; exact hne
    rw [← e1]
    refine (convex_convexHull ℝ _).sum_mem (fun k _ => hα.1 k) e2 ?_
    intro k hk
    exact subset_convexHull ℝ _ ⟨k, (Finset.mem_filter.1 hk).2, rfl⟩

/-- Conjunct 2 given the Shapley–Folkman–Starr bound for the chosen profile. -/
theorem conj2 {n d q : ℕ} {X : Fin n → Set (E d)} {A : Fin n → (E d →L[ℝ] E q)}
    {θ : Fin n → E d → E q → ℝ} {Ω : Set (E q)} {Δ M H γ : ℝ}
    (hstd : StandingHyp X A Ω Δ M) (hA1 : Assumption1 X Ω θ H γ) (xt : Fin n → E d)
    (hxt : IsEpsPNE (fun i => convexHull ℝ (X i)) (convCost X θ A) 0 xt)
    (Z : Fin n → Set (E d)) (hZ : ∀ i, IsGenerator X θ A i xt (Z i))
    (xs : Fin n → E d) (hxs : ∀ i, xs i ∈ Z i)
    (hD : ‖∑ i, A i (xt i) - ∑ i, A i (xs i)‖ ≤ Real.sqrt (q : ℝ) * M * Δ) :
    IsEpsPNE X (cost θ A)
        (2 * H * (((Real.sqrt (q : ℝ) + 1) * M * Δ) / (n : ℝ)) ^ γ) xs := by
  have gf := fun i => gen_facts hstd hA1 xt hxt i (Z i) (hZ i)
  have hxsX : ∀ i, xs i ∈ X i := fun i => (gf i).2.2.1 (hxs i)
  refine ⟨hxsX, fun i y hy => ?_⟩
  obtain ⟨hc, hne, hΔ, hdiam, hM, hA, -⟩ := id hstd
  obtain ⟨-, hH, hγ, hhol⟩ := hA1
  set B : ℝ := ((Real.sqrt (q : ℝ) + 1) * M * Δ) / (n : ℝ)
  have hxsc : ∀ j, xs j ∈ convexHull ℝ (X j) := fun j => subset_convexHull ℝ _ (hxsX j)
  have hgap : ∀ w, ‖aggregate A (Function.update xs i w) - aggregate A (Function.update xt i w)‖
      ≤ B := by
    intro w
    refine (agg_update_dist A M hA xs xt i w).trans ?_
    have h1 : ‖xs i - xt i‖ ≤ Δ := dist_le_conv hc hdiam i _ _ (hxsc i) (hxt.1 i)
    have h2 : ‖∑ j, A j (xs j) - ∑ j, A j (xt j)‖ ≤ Real.sqrt (q : ℝ) * M * Δ := by
      rw [norm_sub_rev]; exact hD
    have h3 : (n : ℝ)⁻¹ * (‖∑ j, A j (xs j) - ∑ j, A j (xt j)‖ + M * ‖xs i - xt i‖)
        ≤ (n : ℝ)⁻¹ * (Real.sqrt (q : ℝ) * M * Δ + M * Δ) :=
      mul_le_mul_of_nonneg_left (add_le_add h2 (mul_le_mul_of_nonneg_left h1 hM.le))
        (by positivity)
    refine h3.trans (le_of_eq ?_)
    simp only [B]; rw [div_eq_inv_mul]; ring
  have hol : ∀ w ∈ X i, |θ i w (aggregate A (Function.update xs i w))
      - θ i w (aggregate A (Function.update xt i w))| ≤ H * B ^ γ := by
    intro w hw
    have hwc : w ∈ convexHull ℝ (X i) := subset_convexHull ℝ _ hw
    refine (hhol i w hw _ (agg_mem hstd _ (update_mem_conv xt hxt.1 i w hwc)) _
      (agg_mem hstd _ (update_mem_conv xs hxsc i w hwc))).trans ?_
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) (hgap w) hγ.le) hH.le
  have e1 := (gf i).1 (xs i) (hxs i)
  have e2 := (gf i).2.1 y hy
  have k1 := (abs_le.1 (hol (xs i) (hxsX i))).2
  have k2 := (abs_le.1 (hol y hy)).1
  unfold cost at e1 e2 ⊢
  simp only [Function.update_self] at e1 e2 k1 k2 ⊢
  rw [Function.update_eq_self] at k1
  linarith

/-! ### Shapley–Folkman–Starr -/

/-- Conic Carathéodory / vertex reduction: a nonnegative combination can be rewritten with at most
`finrank` positive weights. -/
theorem vertex {κ W : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    [DecidableEq κ] (v : κ → W) (T : Finset κ) :
    ∀ (N : ℕ) (l : κ → ℝ), (∀ t ∈ T, 0 ≤ l t) → (T.filter (fun t => 0 < l t)).card = N →
    ∃ μ : κ → ℝ, (∀ t ∈ T, 0 ≤ μ t) ∧ ∑ t ∈ T, μ t • v t = ∑ t ∈ T, l t • v t ∧
      (T.filter (fun t => 0 < μ t)).card ≤ Module.finrank ℝ W := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro l hl hN
  set P := T.filter (fun t => 0 < l t) with hP
  by_cases hc : P.card ≤ Module.finrank ℝ W
  · exact ⟨l, hl, rfl, hc⟩
  push Not at hc
  have hni : ¬ LinearIndependent ℝ (fun p : P => v p) := by
    intro h
    have := h.fintype_card_le_finrank
    rw [Fintype.card_coe] at this
    omega
  obtain ⟨g, hg0, p0, hp0⟩ := Fintype.not_linearIndependent_iff.1 hni
  set g' : κ → ℝ := fun t => if h : t ∈ P then g ⟨t, h⟩ else 0 with hg'
  have hg'0 : ∑ t ∈ P, g' t • v t = 0 := by
    rw [← Finset.sum_coe_sort P]
    rw [← hg0]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp [g', p.2]
  have hgp0 : g' p0 ≠ 0 := by simpa [g', p0.2] using hp0
  have hout : ∀ t, t ∉ P → g' t = 0 := fun t ht => by simp [g', ht]
  -- choose the sign so that some coefficient is positive
  obtain ⟨G, hG0, hGout, t1, ht1P, ht1⟩ : ∃ G : κ → ℝ, ∑ t ∈ P, G t • v t = 0 ∧
      (∀ t, t ∉ P → G t = 0) ∧ ∃ t1 ∈ P, 0 < G t1 := by
    rcases lt_or_gt_of_ne hgp0 with h | h
    · refine ⟨fun t => -g' t, ?_, fun t ht => by simp [hout t ht], p0, p0.2, by linarith⟩
      simp only [neg_smul, Finset.sum_neg_distrib, hg'0, neg_zero]
    · exact ⟨g', hg'0, hout, p0, p0.2, h⟩
  set P' := P.filter (fun t => 0 < G t)
  have hP'ne : P'.Nonempty := ⟨t1, Finset.mem_filter.2 ⟨ht1P, ht1⟩⟩
  obtain ⟨ts, htsP', hmin⟩ := P'.exists_min_image (fun t => l t / G t) hP'ne
  obtain ⟨htsP, htsG⟩ := Finset.mem_filter.1 htsP'
  have hlts : 0 < l ts := (Finset.mem_filter.1 htsP).2
  set c := l ts / G ts
  set μ : κ → ℝ := fun t => l t - c * G t
  have hzero : ∀ t ∈ T, t ∉ P → l t = 0 := by
    intro t ht htP
    have : ¬ 0 < l t := fun h => htP (Finset.mem_filter.2 ⟨ht, h⟩)
    linarith [hl t ht]
  have hμ0 : ∀ t ∈ T, 0 ≤ μ t := by
    intro t ht
    by_cases htP : t ∈ P
    · by_cases hGt : 0 < G t
      · have hm := hmin t (Finset.mem_filter.2 ⟨htP, hGt⟩)
        have : c * G t ≤ l t := by
          rw [le_div_iff₀ hGt] at hm
          exact hm
        simp only [μ]; linarith
      · push Not at hGt
        have hc0 : 0 ≤ c := div_nonneg (hl ts (Finset.mem_filter.1 htsP).1) htsG.le
        simp only [μ]; nlinarith [hl t ht]
    · simp [μ, hzero t ht htP, hGout t htP]
  have hsum : ∑ t ∈ T, μ t • v t = ∑ t ∈ T, l t • v t := by
    simp only [μ, sub_smul, Finset.sum_sub_distrib, mul_smul]
    rw [← Finset.smul_sum]
    have : ∑ t ∈ T, G t • v t = ∑ t ∈ P, G t • v t := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) fun t _ htP => ?_
      simp [hGout t htP]
    rw [this, hG0, smul_zero, sub_zero]
  have hsub : T.filter (fun t => 0 < μ t) ⊂ P := by
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨ts, htsP, fun h => ?_⟩
      have := (Finset.mem_filter.1 h).2
      simp only [μ, c] at this
      rw [div_mul_cancel₀ _ htsG.ne', sub_self] at this
      exact lt_irrefl _ this
    · intro t ht
      obtain ⟨htT, hμt⟩ := Finset.mem_filter.1 ht
      by_contra htP
      simp [μ, hzero t htT htP, hGout t htP] at hμt
  have hlt := Finset.card_lt_card hsub
  obtain ⟨μ', h1, h2, h3⟩ := ih _ (hN ▸ hlt) μ hμ0 rfl
  exact ⟨μ', h1, h2.trans hsum, h3⟩

/-- Greedy rounding step (Starr): from a point of a convex hull, a point of the set can be chosen
increasing the squared error by at most `D²`. -/
theorem greedy {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (S : Set V) (x v : V)
    (hx : x ∈ convexHull ℝ S) (D : ℝ) (hD : ∀ s ∈ S, ‖x - s‖ ≤ D) :
    ∃ s ∈ S, ‖v + (x - s)‖ ^ 2 ≤ ‖v‖ ^ 2 + D ^ 2 := by
  by_contra hcon
  push Not at hcon
  have hsub : S ⊆ {p | inner ℝ v p < inner ℝ v x} := by
    intro s hs
    have h1 := hcon s hs
    rw [norm_add_sq_real] at h1
    have h2 := hD s hs
    have h3 : ‖x - s‖ ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    have h4 : 0 < inner ℝ v (x - s) := by linarith
    rw [inner_sub_right] at h4
    show inner ℝ v s < inner ℝ v x
    linarith
  have hconv : Convex ℝ {p | inner ℝ v p < inner ℝ v x} :=
    convex_halfSpace_lt ⟨fun a b => inner_add_right v a b, fun c a => inner_smul_right v a c⟩ _
  have h := convexHull_min hsub hconv hx
  exact lt_irrefl _ (show inner ℝ v x < inner ℝ v x from h)

set_option maxHeartbeats 1000000 in
theorem sf_starr {n d q : ℕ} (A : Fin n → (E d →L[ℝ] E q)) (Z : Fin n → Set (E d))
    (xt : Fin n → E d) (M Δ : ℝ) (hM : 0 ≤ M) (hΔ : 0 ≤ Δ) (hA : ∀ i, ‖A i‖ ≤ M)
    (hZ : ∀ i, (Z i).Finite) (hx : ∀ i, xt i ∈ convexHull ℝ (Z i))
    (hdiam : ∀ i, ∀ a ∈ Z i, ∀ b ∈ Z i, ‖a - b‖ ≤ Δ) :
    ∃ x' : Fin n → E d, (∀ i, x' i ∈ Z i) ∧
      ‖∑ i, A i (xt i) - ∑ i, A i (x' i)‖ ≤ Real.sqrt (q : ℝ) * M * Δ := by
  classical
  set Zf : Fin n → Finset (E d) := fun j => (hZ j).toFinset with hZf
  have hmemZf : ∀ j z, z ∈ Zf j ↔ z ∈ Z j := fun j z => (hZ j).mem_toFinset
  have hrep : ∀ j, ∃ w : E d → ℝ, (∀ y ∈ Z j, 0 ≤ w y) ∧ ∑ y ∈ Zf j, w y = 1 ∧
      (Zf j).centerMass w id = xt j := by
    intro j
    have := hx j
    rw [(hZ j).convexHull_eq] at this
    exact this
  choose w hw0 hw1 hwc using hrep
  set T : Finset (Σ _ : Fin n, E d) := Finset.univ.sigma Zf
  set l : (Σ _ : Fin n, E d) → ℝ := fun t => w t.1 t.2
  set v : (Σ _ : Fin n, E d) → (Fin n → ℝ) × E q :=
    fun t => (Pi.single t.1 1, A t.1 t.2)
  have hl0 : ∀ t ∈ T, 0 ≤ l t := by
    intro t ht
    obtain ⟨-, h2⟩ := Finset.mem_sigma.1 ht
    exact hw0 _ _ ((hmemZf _ _).1 h2)
  obtain ⟨μ, hμ0, hμs, hμc⟩ := vertex v T _ l hl0 rfl
  have hfr : Module.finrank ℝ ((Fin n → ℝ) × E q) = n + q := by
    rw [Module.finrank_prod, Module.finrank_fin_fun, finrank_euclideanSpace_fin]
  rw [hfr] at hμc
  -- per-player sums
  have hfst := congrArg Prod.fst hμs
  have hsnd := congrArg Prod.snd hμs
  simp only [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, v] at hfst hsnd
  have hmemT : ∀ j z, z ∈ Zf j → (⟨j, z⟩ : Σ _ : Fin n, E d) ∈ T :=
    fun j z hz => Finset.mem_sigma.2 ⟨Finset.mem_univ _, hz⟩
  have key : ∀ (f : (Σ _ : Fin n, E d) → ℝ) (j : Fin n),
      (∑ t ∈ T, f t • (Pi.single t.1 (1 : ℝ) : Fin n → ℝ)) j = ∑ z ∈ Zf j, f ⟨j, z⟩ := by
    intro f j
    rw [Finset.sum_apply, Finset.sum_sigma, Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      refine Finset.sum_eq_zero fun z _ => ?_
      simp [Pi.single_apply, Ne.symm hb]
    · simp
  have hμ1 : ∀ j, ∑ z ∈ Zf j, μ ⟨j, z⟩ = 1 := by
    intro j
    have := congrFun hfst j
    rw [key, key] at this
    rw [this]; exact hw1 j
  set y : Fin n → E q := fun j => ∑ z ∈ Zf j, μ ⟨j, z⟩ • A j z with hy
  have hagg : ∑ j, y j = ∑ j, A j (xt j) := by
    have h := hsnd
    simp only [T, Finset.sum_sigma] at h
    simp only [y]
    rw [h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hwc j, Finset.centerMass_eq_of_sum_1 _ _ (hw1 j), map_sum]
    simp [l, map_smul]
  have hy_conv : ∀ j, y j ∈ convexHull ℝ (A j '' Z j) := by
    intro j
    refine (convex_convexHull ℝ _).sum_mem (fun z hz => hμ0 _ (hmemT j z hz)) (hμ1 j) ?_
    intro z hz
    exact subset_convexHull ℝ _ ⟨z, (hmemZf j z).1 hz, rfl⟩
  have hy_near : ∀ j, ∀ p ∈ A j '' Z j, ‖y j - p‖ ≤ M * Δ := by
    rintro j _ ⟨z0, hz0, rfl⟩
    have hsub : A j '' Z j ⊆ Metric.closedBall (A j z0) (M * Δ) := by
      rintro _ ⟨z, hz, rfl⟩
      rw [Metric.mem_closedBall, dist_eq_norm, ← map_sub]
      exact ((A j).le_opNorm _).trans
        (mul_le_mul (hA j) (hdiam j z hz z0 hz0) (norm_nonneg _) hM)
    have := convexHull_min hsub (convex_closedBall _ _) (hy_conv j)
    rwa [Metric.mem_closedBall, dist_eq_norm] at this
  set Pos : Fin n → Finset (E d) := fun j => (Zf j).filter (fun z => 0 < μ ⟨j, z⟩)
  have hcard : (T.filter (fun t => 0 < μ t)).card = ∑ j, (Pos j).card := by
    simp only [T, Pos, Finset.card_filter, Finset.sum_sigma]
  have hPos_ne : ∀ j, (Pos j).Nonempty := by
    intro j
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have h0 : ∀ z ∈ Zf j, μ ⟨j, z⟩ = 0 := by
      intro z hz
      refine le_antisymm (not_lt.1 fun hz' => ?_) (hμ0 _ (hmemT j z hz))
      have hm : z ∈ Pos j := Finset.mem_filter.2 ⟨hz, hz'⟩
      rw [h] at hm
      exact absurd hm (Finset.notMem_empty z)
    have := hμ1 j
    rw [Finset.sum_eq_zero h0] at this
    exact zero_ne_one this
  set F := Finset.univ.filter (fun j => 2 ≤ (Pos j).card)
  have hF : F.card ≤ q := by
    have hsplit : ∑ j ∈ F, (Pos j).card + ∑ j ∈ Finset.univ.filter
        (fun j => ¬ 2 ≤ (Pos j).card), (Pos j).card = ∑ j, (Pos j).card :=
      Finset.sum_filter_add_sum_filter_not _ _ _
    have hA1' : 2 * F.card ≤ ∑ j ∈ F, (Pos j).card := by
      rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_le_sum fun j hj => (Finset.mem_filter.1 hj).2
    have hA2 : (Finset.univ.filter (fun j => ¬ 2 ≤ (Pos j).card)).card
        ≤ ∑ j ∈ Finset.univ.filter (fun j => ¬ 2 ≤ (Pos j).card), (Pos j).card := by
      rw [Finset.card_eq_sum_ones]
      exact Finset.sum_le_sum fun j _ => Finset.card_pos.2 (hPos_ne j)
    have hcnt : F.card + (Finset.univ.filter (fun j => ¬ 2 ≤ (Pos j).card)).card = n := by
      rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
    have : (T.filter (fun t => 0 < μ t)).card ≤ n + q := hμc
    rw [hcard] at this
    omega
  have hnf : ∀ j, j ∉ F → ∃ z ∈ Z j, y j = A j z := by
    intro j hj
    have h1 : (Pos j).card = 1 := by
      have : ¬ 2 ≤ (Pos j).card := fun h => hj (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
      have := Finset.card_pos.2 (hPos_ne j)
      omega
    obtain ⟨z0, hz0⟩ := Finset.card_eq_one.1 h1
    have hz0m : z0 ∈ Pos j := by rw [hz0]; exact Finset.mem_singleton_self z0
    have hz0Z : z0 ∈ Zf j := (Finset.mem_filter.1 hz0m).1
    have hred : ∀ (g : E d → E q), (∀ z ∈ Zf j, μ ⟨j, z⟩ = 0 → g z = 0) →
        ∑ z ∈ Zf j, g z = g z0 := by
      intro g hg
      rw [← Finset.sum_filter_of_ne (p := fun z => 0 < μ ⟨j, z⟩)]
      · show ∑ z ∈ Pos j, g z = g z0
        rw [hz0, Finset.sum_singleton]
      · intro z hz hgz
        exact lt_of_le_of_ne (hμ0 _ (hmemT j z hz)) (fun h => hgz (hg z hz h.symm))
    have hred' : ∑ z ∈ Zf j, μ ⟨j, z⟩ = μ ⟨j, z0⟩ := by
      rw [← Finset.sum_filter_of_ne (p := fun z => 0 < μ ⟨j, z⟩)]
      · show ∑ z ∈ Pos j, μ ⟨j, z⟩ = μ ⟨j, z0⟩
        rw [hz0, Finset.sum_singleton]
      · intro z hz hgz
        exact lt_of_le_of_ne (hμ0 _ (hmemT j z hz)) (Ne.symm hgz)
    have hμz0 : μ ⟨j, z0⟩ = 1 := by rw [← hred']; exact hμ1 j
    refine ⟨z0, (hmemZf j z0).1 hz0Z, ?_⟩
    simp only [y]
    rw [hred (fun z => μ ⟨j, z⟩ • A j z) (fun z _ h => by simp [h]), hμz0, one_smul]
  have hZne : ∀ j, (Z j).Nonempty := fun j =>
    convexHull_nonempty_iff.1 ⟨xt j, hx j⟩
  have hgr : ∀ F' : Finset (Fin n), ∃ s : Fin n → E d, (∀ j, s j ∈ Z j) ∧
      ‖∑ j ∈ F', (y j - A j (s j))‖ ^ 2 ≤ F'.card * (M * Δ) ^ 2 := by
    intro F'
    induction F' using Finset.induction_on with
    | empty =>
      refine ⟨fun j => (hZne j).some, fun j => (hZne j).some_mem, ?_⟩
      simp
    | insert j F' hj ih =>
      obtain ⟨s, hs, hb⟩ := ih
      obtain ⟨p, ⟨z, hz, rfl⟩, hp⟩ := greedy (A j '' Z j) (y j)
        (∑ k ∈ F', (y k - A k (s k))) (hy_conv j) (M * Δ) (hy_near j)
      refine ⟨Function.update s j z, ?_, ?_⟩
      · intro k
        by_cases hk : k = j
        · subst hk; simpa using hz
        · rw [Function.update_of_ne hk]; exact hs k
      · rw [Finset.sum_insert hj, Function.update_self]
        have : ∑ k ∈ F', (y k - A k (Function.update s j z k)) = ∑ k ∈ F', (y k - A k (s k)) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [Function.update_of_ne (fun (h : k = j) => hj (h ▸ hk))]
        rw [this, add_comm, Finset.card_insert_of_notMem hj]
        push_cast
        linarith
  obtain ⟨s, hs, hb⟩ := hgr F
  refine ⟨fun j => if h : j ∈ F then s j else (hnf j h).choose, ?_, ?_⟩
  · intro j
    by_cases h : j ∈ F
    · simp only [h, dite_true]; exact hs j
    · simp only [h, dite_false]; exact (hnf j h).choose_spec.1
  · have hdiff : ∑ i, A i (xt i) - ∑ i, A i ((fun j => if h : j ∈ F then s j
        else (hnf j h).choose) i) = ∑ j ∈ F, (y j - A j (s j)) := by
      rw [← hagg, ← Finset.sum_sub_distrib]
      rw [← Finset.sum_subset (Finset.subset_univ F)]
      · refine Finset.sum_congr rfl fun j hj => ?_
        simp only [hj, dite_true]
      · intro j _ hj
        simp only [hj, dite_false]
        rw [sub_eq_zero]
        exact (hnf j hj).choose_spec.2
    rw [hdiff]
    have hq : (F.card : ℝ) ≤ q := by exact_mod_cast hF
    have h2 : ‖∑ j ∈ F, (y j - A j (s j))‖ ^ 2 ≤ (Real.sqrt (q : ℝ) * M * Δ) ^ 2 := by
      have hsq : (Real.sqrt (q : ℝ)) ^ 2 = q := Real.sq_sqrt (Nat.cast_nonneg q)
      calc _ ≤ (F.card : ℝ) * (M * Δ) ^ 2 := hb
        _ ≤ q * (M * Δ) ^ 2 := mul_le_mul_of_nonneg_right hq (sq_nonneg _)
        _ = _ := by rw [mul_assoc, mul_pow (Real.sqrt (q : ℝ)), hsq]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2

/-- Proposition 2.4 assuming (a) a PNE of the convexified game exists and (b) generators exist. -/
theorem prop24_of {n d q : ℕ} (X : Fin n → Set (E d)) (A : Fin n → (E d →L[ℝ] E q))
    (θ : Fin n → E d → E q → ℝ) (Ω : Set (E q)) (Δ M H γ : ℝ)
    (hstd : StandingHyp X A Ω Δ M) (hA1 : Assumption1 X Ω θ H γ)
    (hPNE : ∃ xt : Fin n → E d, IsEpsPNE (fun i => convexHull ℝ (X i)) (convCost X θ A) 0 xt)
    (hgen : ∀ xt : Fin n → E d, (∀ j, xt j ∈ convexHull ℝ (X j)) →
      ∀ i, ∃ Z, IsGenerator X θ A i xt Z) :
    (∃ x : Fin n → E d, IsEpsPNE X (cost θ A)
      (2 * H * (((Real.sqrt (q : ℝ) + 1) * M * Δ) / (n : ℝ)) ^ γ) x) ∧
    ∀ xt : Fin n → E d, IsEpsPNE (fun i => convexHull ℝ (X i)) (convCost X θ A) 0 xt →
      ∀ Z : Fin n → Set (E d), (∀ i, IsGenerator X θ A i xt (Z i)) →
      ∀ xs : Fin n → E d, (∀ i, xs i ∈ Z i) →
      (∀ x' : Fin n → E d, (∀ i, x' i ∈ Z i) →
        ‖∑ i, A i (xt i) - ∑ i, A i (xs i)‖ ^ 2 ≤ ‖∑ i, A i (xt i) - ∑ i, A i (x' i)‖ ^ 2) →
      IsEpsPNE X (cost θ A)
        (2 * H * (((Real.sqrt (q : ℝ) + 1) * M * Δ) / (n : ℝ)) ^ γ) xs := by
  obtain ⟨hc, hne, hΔ, hdiam, hM, hA, -⟩ := id hstd
  have part2 : ∀ xt : Fin n → E d,
      IsEpsPNE (fun i => convexHull ℝ (X i)) (convCost X θ A) 0 xt →
      ∀ Z : Fin n → Set (E d), (∀ i, IsGenerator X θ A i xt (Z i)) →
      ∀ xs : Fin n → E d, (∀ i, xs i ∈ Z i) →
      (∀ x' : Fin n → E d, (∀ i, x' i ∈ Z i) →
        ‖∑ i, A i (xt i) - ∑ i, A i (xs i)‖ ^ 2 ≤ ‖∑ i, A i (xt i) - ∑ i, A i (x' i)‖ ^ 2) →
      IsEpsPNE X (cost θ A)
        (2 * H * (((Real.sqrt (q : ℝ) + 1) * M * Δ) / (n : ℝ)) ^ γ) xs := by
    intro xt hxt Z hZ xs hxs hmin
    have gf := fun i => gen_facts hstd hA1 xt hxt i (Z i) (hZ i)
    obtain ⟨x', hx', hD'⟩ := sf_starr A Z xt M Δ hM.le hΔ.le hA (fun i => (gf i).2.2.2.1)
      (fun i => (gf i).2.2.2.2)
      (fun i a ha b hb => dist_le_conv hc hdiam i a b (subset_convexHull ℝ _ ((gf i).2.2.1 ha))
        (subset_convexHull ℝ _ ((gf i).2.2.1 hb)))
    have h1 := hmin x' hx'
    have h2 : ‖∑ i, A i (xt i) - ∑ i, A i (xs i)‖ ≤ ‖∑ i, A i (xt i) - ∑ i, A i (x' i)‖ :=
      (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h1
    exact conj2 hstd hA1 xt hxt Z hZ xs hxs (h2.trans hD')
  refine ⟨?_, part2⟩
  obtain ⟨xt, hxt⟩ := hPNE
  choose Z hZ using hgen xt hxt.1
  have gf := fun i => gen_facts hstd hA1 xt hxt i (Z i) (hZ i)
  have hfin : (Set.pi Set.univ Z).Finite := Set.Finite.pi fun i => (gf i).2.2.2.1
  have hZne : ∀ i, (Z i).Nonempty := fun i =>
    convexHull_nonempty_iff.1 ⟨xt i, (gf i).2.2.2.2⟩
  have hne' : (Set.pi Set.univ Z).Nonempty := Set.univ_pi_nonempty_iff.2 hZne
  obtain ⟨xs, hxs, hmin⟩ := Set.exists_min_image _
    (fun x : Fin n → E d => ‖∑ i, A i (xt i) - ∑ i, A i (x i)‖ ^ 2) hfin hne'
  refine ⟨xs, part2 xt hxt Z hZ xs (fun i => hxs i (Set.mem_univ i)) fun x' hx' => ?_⟩
  exact hmin x' (fun i _ => hx' i)


/-! ### Objective-aware vertex reduction (Carathéodory with an objective) -/

theorem vertex2 {κ W : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    [DecidableEq κ] (v : κ → W) (ob : κ → ℝ) (φ : W →ₗ[ℝ] ℝ) (T : Finset κ)
    (hφ : ∀ t ∈ T, φ (v t) = 1) :
    ∀ (N : ℕ) (l : κ → ℝ), (∀ t ∈ T, 0 ≤ l t) → (T.filter (fun t => 0 < l t)).card = N →
    ∃ μ : κ → ℝ, (∀ t ∈ T, 0 ≤ μ t) ∧ ∑ t ∈ T, μ t • v t = ∑ t ∈ T, l t • v t ∧
      ∑ t ∈ T, μ t * ob t ≤ ∑ t ∈ T, l t * ob t ∧
      (T.filter (fun t => 0 < μ t)).card ≤ Module.finrank ℝ W := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro l hl hN
  set P := T.filter (fun t => 0 < l t) with hP
  by_cases hc : P.card ≤ Module.finrank ℝ W
  · exact ⟨l, hl, rfl, le_rfl, hc⟩
  push Not at hc
  have hni : ¬ LinearIndependent ℝ (fun p : P => v p) := by
    intro h
    have := h.fintype_card_le_finrank
    rw [Fintype.card_coe] at this
    omega
  obtain ⟨g, hg0, p0, hp0⟩ := Fintype.not_linearIndependent_iff.1 hni
  set g' : κ → ℝ := fun t => if h : t ∈ P then g ⟨t, h⟩ else 0 with hg'
  have hg'0 : ∑ t ∈ P, g' t • v t = 0 := by
    rw [← Finset.sum_coe_sort P]
    rw [← hg0]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp [g', p.2]
  have hgp0 : g' p0 ≠ 0 := by simpa [g', p0.2] using hp0
  have hout : ∀ t, t ∉ P → g' t = 0 := fun t ht => by simp [g', ht]
  have hPT : ∀ t ∈ P, t ∈ T := fun t ht => (Finset.mem_filter.1 ht).1
  have hsum0 : ∀ G : κ → ℝ, ∑ t ∈ P, G t • v t = 0 → ∑ t ∈ P, G t = 0 := by
    intro G hG
    have := congrArg φ hG
    rw [map_sum, map_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [map_smul, hφ t (hPT t ht), smul_eq_mul, mul_one]
  -- choose the sign so that the objective does not increase
  obtain ⟨G, hG0, hGout, hGob, hGp0⟩ : ∃ G : κ → ℝ, ∑ t ∈ P, G t • v t = 0 ∧
      (∀ t, t ∉ P → G t = 0) ∧ 0 ≤ ∑ t ∈ P, G t * ob t ∧ G p0 ≠ 0 := by
    by_cases hs : 0 ≤ ∑ t ∈ P, g' t * ob t
    · exact ⟨g', hg'0, hout, hs, hgp0⟩
    · push Not at hs
      refine ⟨fun t => -g' t, ?_, fun t ht => by simp [hout t ht], ?_, by simpa using hgp0⟩
      · simp only [neg_smul, Finset.sum_neg_distrib, hg'0, neg_zero]
      · simp only [neg_mul, Finset.sum_neg_distrib]; linarith
  have hGs := hsum0 G hG0
  obtain ⟨t1, ht1P, ht1⟩ : ∃ t1 ∈ P, 0 < G t1 := by
    by_contra hneg
    push Not at hneg
    have := (Finset.sum_eq_zero_iff_of_nonpos hneg).1 hGs p0 p0.2
    exact hGp0 this
  set P' := P.filter (fun t => 0 < G t)
  have hP'ne : P'.Nonempty := ⟨t1, Finset.mem_filter.2 ⟨ht1P, ht1⟩⟩
  obtain ⟨ts, htsP', hmin⟩ := P'.exists_min_image (fun t => l t / G t) hP'ne
  obtain ⟨htsP, htsG⟩ := Finset.mem_filter.1 htsP'
  have hlts : 0 < l ts := (Finset.mem_filter.1 htsP).2
  set c := l ts / G ts
  have hc0 : 0 ≤ c := div_nonneg (hl ts (Finset.mem_filter.1 htsP).1) htsG.le
  set μ : κ → ℝ := fun t => l t - c * G t
  have hzero : ∀ t ∈ T, t ∉ P → l t = 0 := by
    intro t ht htP
    have : ¬ 0 < l t := fun h => htP (Finset.mem_filter.2 ⟨ht, h⟩)
    linarith [hl t ht]
  have hμ0 : ∀ t ∈ T, 0 ≤ μ t := by
    intro t ht
    by_cases htP : t ∈ P
    · by_cases hGt : 0 < G t
      · have hm := hmin t (Finset.mem_filter.2 ⟨htP, hGt⟩)
        have : c * G t ≤ l t := by
          rw [le_div_iff₀ hGt] at hm
          exact hm
        simp only [μ]; linarith
      · push Not at hGt
        simp only [μ]; nlinarith [hl t ht]
    · simp [μ, hzero t ht htP, hGout t htP]
  have hTP : ∀ F : κ → ℝ, ∑ t ∈ T, G t * F t = ∑ t ∈ P, G t * F t := by
    intro F
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) fun t _ htP => ?_
    simp [hGout t htP]
  have hsum : ∑ t ∈ T, μ t • v t = ∑ t ∈ T, l t • v t := by
    simp only [μ, sub_smul, Finset.sum_sub_distrib, mul_smul]
    rw [← Finset.smul_sum]
    have : ∑ t ∈ T, G t • v t = ∑ t ∈ P, G t • v t := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) fun t _ htP => ?_
      simp [hGout t htP]
    rw [this, hG0, smul_zero, sub_zero]
  have hob : ∑ t ∈ T, μ t * ob t ≤ ∑ t ∈ T, l t * ob t := by
    simp only [μ, sub_mul, Finset.sum_sub_distrib, mul_assoc]
    rw [← Finset.mul_sum, hTP ob]
    nlinarith [mul_nonneg hc0 hGob]
  have hsub : T.filter (fun t => 0 < μ t) ⊂ P := by
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨ts, htsP, fun h => ?_⟩
      have := (Finset.mem_filter.1 h).2
      simp only [μ, c] at this
      rw [div_mul_cancel₀ _ htsG.ne', sub_self] at this
      exact lt_irrefl _ this
    · intro t ht
      obtain ⟨htT, hμt⟩ := Finset.mem_filter.1 ht
      by_contra htP
      simp [μ, hzero t htT htP, hGout t htP] at hμt
  have hlt := Finset.card_lt_card hsub
  obtain ⟨μ', h1, h2, h3, h4⟩ := ih _ (hN ▸ hlt) μ hμ0 rfl
  exact ⟨μ', h1, h2.trans hsum, h3.trans hob, h4⟩

theorem sum_extend {κ ι β M : Type*} [Fintype κ] [Fintype ι] [AddCommMonoid M]
    (P : Finset κ) (e : P ↪ ι) (μ : κ → ℝ) (z : κ → β) (b0 : β) (f : ℝ → β → M)
    (hf : ∀ b, f 0 b = 0) (hμ : ∀ t ∉ P, μ t = 0) :
    ∑ k, f (Function.extend e (fun p : P => μ p) 0 k)
        (Function.extend e (fun p : P => z p) (fun _ => b0) k) = ∑ t, f (μ t) (z t) := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ P) (fun t _ ht => by rw [hμ t ht, hf])]
  rw [← Finset.sum_coe_sort P]
  symm
  refine Fintype.sum_of_injective e e.injective _ _ ?_ ?_
  · intro k hk
    rw [Function.extend_apply' _ _ _ hk]
    simp [hf]
  · intro p
    simp [e.injective.extend_apply]

/-- Reduction of a finite convex representation to `d + 1` points without increasing the
objective. -/
theorem rep_fin {d : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ] (S : Set (E d)) (x0 : E d)
    (hx0 : x0 ∈ S) (ob : E d → ℝ) (l : κ → ℝ) (z : κ → E d) (hl : ∀ t, 0 ≤ l t)
    (hl1 : ∑ t, l t = 1) (hz : ∀ t, z t ∈ S) :
    ∃ α ∈ stdSimplex ℝ (Fin (d + 1)), ∃ w : Fin (d + 1) → E d, (∀ k, w k ∈ S) ∧
      ∑ k, α k • w k = ∑ t, l t • z t ∧ ∑ k, α k * ob (w k) ≤ ∑ t, l t * ob (z t) := by
  classical
  obtain ⟨μ, hμ0, hμv, hμob, hcard⟩ := vertex2 (W := ℝ × E d) (fun t => ((1 : ℝ), z t))
    (fun t => ob (z t)) (LinearMap.fst ℝ ℝ (E d)) Finset.univ (fun t _ => rfl) _ l
    (fun t _ => hl t) rfl
  have hfr : Module.finrank ℝ (ℝ × E d) = d + 1 := by
    rw [Module.finrank_prod, finrank_euclideanSpace_fin, Module.finrank_self]; omega
  have hv1 : ∑ t, μ t = ∑ t, l t := by
    have := congrArg Prod.fst hμv
    simpa [Prod.fst_sum] using this
  have hv2 : ∑ t, μ t • z t = ∑ t, l t • z t := by
    have := congrArg Prod.snd hμv
    simpa [Prod.snd_sum] using this
  set P := Finset.univ.filter (fun t => 0 < μ t) with hP
  have hcardP : Fintype.card P ≤ Fintype.card (Fin (d + 1)) := by
    rw [Fintype.card_coe, Fintype.card_fin]; rw [hfr] at hcard; exact hcard
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcardP
  have hout : ∀ t ∉ P, μ t = 0 := by
    intro t ht
    have : ¬ 0 < μ t := fun h => ht (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    linarith [hμ0 t (Finset.mem_univ _)]
  refine ⟨Function.extend e (fun p : P => μ p) 0, ⟨fun k => ?_, ?_⟩,
    Function.extend e (fun p : P => z p) (fun _ => x0), fun k => ?_, ?_, ?_⟩
  · by_cases hk : ∃ p, e p = k
    · obtain ⟨p, rfl⟩ := hk
      rw [e.injective.extend_apply]; exact hμ0 p (Finset.mem_univ _)
    · rw [Function.extend_apply' _ _ _ hk]; exact le_rfl
  · have := sum_extend P e μ z x0 (fun a _ => a) (fun _ => rfl) hout
    rw [this, hv1, hl1]
  · by_cases hk : ∃ p, e p = k
    · obtain ⟨p, rfl⟩ := hk
      rw [e.injective.extend_apply]; exact hz p
    · rw [Function.extend_apply' _ _ _ hk]; exact hx0
  · have := sum_extend P e μ z x0 (fun a b => a • b) (fun b => zero_smul ℝ b) hout
    rw [this, hv2]
  · have := sum_extend P e μ z x0 (fun a b => a * ob b) (fun b => zero_mul _) hout
    rw [this]; exact hμob

/-! ### Lower semicontinuity and existence of generators -/

theorem lsc_mul {α : Type*} [TopologicalSpace α] {s : Set α} {a b : α → ℝ}
    (ha : ContinuousOn a s) (hb : LowerSemicontinuousOn b s) (ha0 : ∀ p ∈ s, 0 ≤ a p)
    (hb0 : ∀ p ∈ s, 0 ≤ b p) : LowerSemicontinuousOn (fun p => a p * b p) s := by
  intro p hp y hy
  by_cases hy0 : y < 0
  · filter_upwards [self_mem_nhdsWithin] with p' hp'
    exact hy0.trans_le (mul_nonneg (ha0 p' hp') (hb0 p' hp'))
  push Not at hy0
  have hap : 0 < a p := by
    by_contra h
    push Not at h
    have : a p = 0 := le_antisymm h (ha0 p hp)
    simp only [this, zero_mul] at hy; linarith
  have hbp : 0 < b p := by
    by_contra h
    push Not at h
    have : b p = 0 := le_antisymm h (hb0 p hp)
    simp only [this, mul_zero] at hy; linarith
  have hyb : y / a p < b p := by
    rw [div_lt_iff₀ hap]; simpa [mul_comm] using hy
  obtain ⟨b', hb1, hb2⟩ := exists_between hyb
  have hb'pos : 0 < b' := lt_of_le_of_lt (div_nonneg hy0 hap.le) hb1
  have hya : y / b' < a p := by
    rw [div_lt_iff₀ hap] at hb1
    rw [div_lt_iff₀ hb'pos]; linarith [mul_comm b' (a p)]
  obtain ⟨a', ha1, ha2⟩ := exists_between hya
  have hEa : ∀ᶠ p' in nhdsWithin p s, a' < a p' := (ha p hp).eventually (lt_mem_nhds ha2)
  have hEb : ∀ᶠ p' in nhdsWithin p s, b' < b p' := hb p hp b' hb2
  filter_upwards [hEa, hEb] with p' h1 h2
  have ha'0 : 0 ≤ a' := le_of_lt (lt_of_le_of_lt (div_nonneg hy0 hb'pos.le) ha1)
  have : y < a' * b' := by rw [div_lt_iff₀ hb'pos] at ha1; linarith
  exact this.trans_le (mul_le_mul h1.le h2.le hb'pos.le (ha'0.trans h1.le))

theorem lsc_comp {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {g : β → ℝ}
    {T : Set β} {π : α → β} {s : Set α} (hg : LowerSemicontinuousOn g T)
    (hπ : ContinuousOn π s) (hmap : Set.MapsTo π s T) :
    LowerSemicontinuousOn (fun p => g (π p)) s :=
  fun p hp y hy => ((hπ p hp).tendsto_nhdsWithin hmap).eventually (hg (π p) (hmap hp) y hy)

theorem agg_update_cont {n d q : ℕ} (A : Fin n → (E d →L[ℝ] E q)) (x : Fin n → E d)
    (i : Fin n) : Continuous fun z => aggregate A (Function.update x i z) := by
  unfold aggregate
  exact (continuous_finsetSum _ fun j _ =>
    (A j).continuous.comp ((continuous_apply j).comp (continuous_const.update i continuous_id))).const_smul
      ((n : ℝ)⁻¹)

theorem lsc_g {n d q : ℕ} {X : Fin n → Set (E d)} {A : Fin n → (E d →L[ℝ] E q)}
    {θ : Fin n → E d → E q → ℝ} {Ω : Set (E q)} {Δ M H γ : ℝ}
    (hstd : StandingHyp X A Ω Δ M) (hA1 : Assumption1 X Ω θ H γ) (x : Fin n → E d)
    (hx : ∀ j, x j ∈ convexHull ℝ (X j)) (i : Fin n) :
    LowerSemicontinuousOn (fun z => cost θ A i (Function.update x i z)) (X i) := by
  intro z0 hz0 y hy
  change y < cost θ A i (Function.update x i z0) at hy
  show ∀ᶠ z in nhdsWithin z0 (X i), y < cost θ A i (Function.update x i z)
  set ag := fun z => aggregate A (Function.update x i z) with hag
  have hcont : Continuous ag := agg_update_cont A x i
  have hmem : ∀ z ∈ X i, ag z ∈ Ω := fun z hz =>
    agg_mem hstd _ (update_mem_conv x hx i z (subset_convexHull ℝ _ hz))
  obtain ⟨hlsc, hH, hγ, hHol⟩ := hA1
  have hcost : ∀ z, cost θ A i (Function.update x i z) = θ i z (ag z) := by
    intro z; simp [cost, ag]
  rw [hcost] at hy
  set ε := (θ i z0 (ag z0) - y) / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  have h1 : ∀ᶠ z in nhdsWithin z0 (X i), θ i z0 (ag z0) - ε < θ i z (ag z0) :=
    hlsc i (ag z0) (hmem z0 hz0) z0 hz0 _ (by linarith)
  have hc2 : Continuous fun z => H * ‖ag z - ag z0‖ ^ γ :=
    continuous_const.mul ((hcont.sub continuous_const).norm.rpow_const fun _ => Or.inr hγ.le)
  have h2 : ∀ᶠ z in nhdsWithin z0 (X i), H * ‖ag z - ag z0‖ ^ γ < ε := by
    apply nhdsWithin_le_nhds
    have h0 : H * ‖ag z0 - ag z0‖ ^ γ = 0 := by
      rw [sub_self, norm_zero, Real.zero_rpow hγ.ne', mul_zero]
    exact hc2.continuousAt.eventually (gt_mem_nhds (show H * ‖ag z0 - ag z0‖ ^ γ < ε by rw [h0]; exact hεpos))
  filter_upwards [h1, h2, self_mem_nhdsWithin] with z hz1 hz2 hz
  rw [hcost]
  have := hHol i z hz (ag z0) (hmem z0 hz0) (ag z) (hmem z hz)
  rw [abs_le] at this
  linarith [this.1]

theorem gen_exists {n d q : ℕ} {X : Fin n → Set (E d)} {A : Fin n → (E d →L[ℝ] E q)}
    {θ : Fin n → E d → E q → ℝ} {Ω : Set (E q)} {Δ M H γ : ℝ}
    (hstd : StandingHyp X A Ω Δ M) (hA1 : Assumption1 X Ω θ H γ) (x : Fin n → E d)
    (hx : ∀ j, x j ∈ convexHull ℝ (X j)) (i : Fin n) : ∃ Z, IsGenerator X θ A i x Z := by
  classical
  obtain ⟨m, hm, -⟩ := convCost_bdd hstd hA1 i x hx
  set g := fun z => cost θ A i (Function.update x i z) with hg
  have hgl : LowerSemicontinuousOn (fun z => g z - m) (X i) := by
    intro z hz y hy
    exact (lsc_g hstd hA1 x hx i z hz (y + m) (by simp only [hg] at hy ⊢; linarith)).mono
      fun z h => by simp only [hg] at h ⊢; linarith
  set R : Set ((Fin (d + 1) → ℝ) × (Fin (d + 1) → E d)) :=
    {p | p.1 ∈ stdSimplex ℝ (Fin (d + 1)) ∧ (∀ k, p.2 k ∈ X i) ∧ ∑ k, p.1 k • p.2 k = x i}
    with hR
  have hRc : IsCompact R := by
    have : R = (stdSimplex ℝ (Fin (d + 1)) ×ˢ Set.pi Set.univ (fun _ => X i)) ∩
        {p | ∑ k, p.1 k • p.2 k = x i} := by
      ext p; simp [R, and_assoc]
    rw [this]
    exact ((isCompact_stdSimplex ℝ (Fin (d + 1))).prod (isCompact_univ_pi fun _ => hstd.1 i)).inter_right
      (isClosed_eq (by fun_prop) continuous_const)
  have hRne : R.Nonempty := by
    obtain ⟨ι, hι, w, z, hw0, hw1, hz, hwz⟩ := mem_convexHull_iff_exists_fintype.1 (hx i)
    obtain ⟨x0, hx0⟩ := hstd.2.1 i
    obtain ⟨α, hα, w', hw', hs, -⟩ := rep_fin (X i) x0 hx0 g w z hw0 hw1 hz
    exact ⟨(α, w'), hα, hw', hs.trans hwz⟩
  set F : (Fin (d + 1) → ℝ) × (Fin (d + 1) → E d) → ℝ :=
    fun p => ∑ k, p.1 k * (g (p.2 k) - m) with hF
  have hFl : LowerSemicontinuousOn F R := by
    refine lowerSemicontinuousOn_sum fun k _ => lsc_mul ?_ ?_ ?_ ?_
    · exact ((continuous_apply k).comp continuous_fst).continuousOn
    · exact lsc_comp hgl ((continuous_apply k).comp continuous_snd).continuousOn
        fun p hp => hp.2.1 k
    · exact fun p hp => hp.1.1 k
    · exact fun p hp => by simp only [hg]; linarith [hm _ (hp.2.1 k)]
  obtain ⟨p, hpR, hpmin⟩ := hFl.exists_isMinOn hRne hRc
  refine ⟨{y | ∃ k, 0 < p.1 k ∧ p.2 k = y}, p.1, hpR.1, p.2, hpR.2.1, hpR.2.2, ?_, rfl⟩
  have hFe : ∀ q ∈ R, F q = ∑ k, q.1 k * g (q.2 k) - m := by
    intro q hq
    simp only [hF, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hq.1.2, one_mul]
  unfold convCost
  symm
  apply IsLeast.csInf_eq
  constructor
  · exact ⟨p.1, hpR.1, p.2, hpR.2.1, hpR.2.2, rfl⟩
  · rintro v ⟨α, hα, z, hz, hsum, rfl⟩
    have hq : (α, z) ∈ R := ⟨hα, hz, hsum⟩
    have := isMinOn_iff.1 hpmin _ hq
    rw [hFe p hpR, hFe _ hq] at this
    simp only [hg] at this
    linarith

/-! ### The convexified cost as a function of the own action -/

/-- The infimum (2.2) at a unilateral deviation is attained and is a lower bound. -/
theorem attain {n d q : ℕ} {X : Fin n → Set (E d)} {A : Fin n → (E d →L[ℝ] E q)}
    {θ : Fin n → E d → E q → ℝ} {Ω : Set (E q)} {Δ M H γ : ℝ}
    (hstd : StandingHyp X A Ω Δ M) (hA1 : Assumption1 X Ω θ H γ) (x : Fin n → E d)
    (hx : ∀ j, x j ∈ convexHull ℝ (X j)) (i : Fin n) (y : E d) (hy : y ∈ convexHull ℝ (X i)) :
    ∃ α ∈ stdSimplex ℝ (Fin (d + 1)), ∃ z : Fin (d + 1) → E d, (∀ k, z k ∈ X i) ∧
      ∑ k, α k • z k = y ∧
      ∑ k, α k * cost θ A i (Function.update x i (z k)) = convCost X θ A i (Function.update x i y) ∧
      ∀ α' ∈ stdSimplex ℝ (Fin (d + 1)), ∀ z' : Fin (d + 1) → E d, (∀ k, z' k ∈ X i) →
        ∑ k, α' k • z' k = y →
        convCost X θ A i (Function.update x i y) ≤ ∑ k, α' k * cost θ A i (Function.update x i (z' k)) := by
  have hx' := update_mem_conv x hx i y hy
  obtain ⟨Z, α, hα, z, hz, hsum, hval, -⟩ := gen_exists hstd hA1 _ hx' i
  obtain ⟨m, -, hb⟩ := convCost_bdd hstd hA1 i _ hx'
  simp only [Function.update_idem, Function.update_self] at hsum hval
  refine ⟨α, hα, z, hz, hsum, hval, fun α' hα' z' hz' hs' => ?_⟩
  have key : convCost X θ A i (Function.update x i y) ≤
      ∑ k, α' k * cost θ A i (Function.update (Function.update x i y) i (z' k)) :=
    csInf_le hb ⟨α', hα', z', hz', by simpa using hs', rfl⟩
  simpa [Function.update_idem] using key

theorem conv_own {n d q : ℕ} {X : Fin n → Set (E d)} {A : Fin n → (E d →L[ℝ] E q)}
    {θ : Fin n → E d → E q → ℝ} {Ω : Set (E q)} {Δ M H γ : ℝ}
    (hstd : StandingHyp X A Ω Δ M) (hA1 : Assumption1 X Ω θ H γ) (x : Fin n → E d)
    (hx : ∀ j, x j ∈ convexHull ℝ (X j)) (i : Fin n) :
    ConvexOn ℝ (convexHull ℝ (X i)) (fun y => convCost X θ A i (Function.update x i y)) := by
  classical
  refine ⟨convex_convexHull ℝ _, ?_⟩
  intro y1 hy1 y2 hy2 a b ha hb hab
  show convCost X θ A i (Function.update x i (a • y1 + b • y2)) ≤
    a • convCost X θ A i (Function.update x i y1) + b • convCost X θ A i (Function.update x i y2)
  obtain ⟨α1, hα1, z1, hz1, hs1, hv1, -⟩ := attain hstd hA1 x hx i y1 hy1
  obtain ⟨α2, hα2, z2, hz2, hs2, hv2, -⟩ := attain hstd hA1 x hx i y2 hy2
  have hym : a • y1 + b • y2 ∈ convexHull ℝ (X i) := (convex_convexHull ℝ _) hy1 hy2 ha hb hab
  obtain ⟨-, -, -, -, -, -, hlow⟩ := attain hstd hA1 x hx i _ hym
  obtain ⟨x0, hx0⟩ := hstd.2.1 i
  obtain ⟨α, hα, w, hw, hsw, hob⟩ := rep_fin (X i) x0 hx0
    (fun z => cost θ A i (Function.update x i z))
    (Sum.elim (fun k => a * α1 k) (fun k => b * α2 k)) (Sum.elim z1 z2)
    (by rintro (k | k) <;> simp [mul_nonneg ha (hα1.1 k), mul_nonneg hb (hα2.1 k)])
    (by simp [Fintype.sum_sum_type, ← Finset.mul_sum, hα1.2, hα2.2, hab])
    (by rintro (k | k) <;> simp [hz1 k, hz2 k])
  have := hlow α hα w hw (by
    rw [hsw]; simp [Fintype.sum_sum_type, mul_smul, ← Finset.smul_sum, hs1, hs2])
  refine this.trans (hob.trans (le_of_eq ?_))
  rw [← hv1, ← hv2]
  simp [Fintype.sum_sum_type, Finset.mul_sum, mul_assoc, smul_eq_mul]

theorem agg_diff {n d q : ℕ} (A : Fin n → (E d →L[ℝ] E q)) (x x' : Fin n → E d) (i : Fin n)
    (z y : E d) :
    aggregate A (Function.update x' i z) - aggregate A (Function.update x i z) =
      aggregate A (Function.update x' i y) - aggregate A (Function.update x i y) := by
  unfold aggregate
  rw [← smul_sub, ← smul_sub, sum_update_eq, sum_update_eq, sum_update_eq, sum_update_eq]
  congr 1
  abel

/-- Uniform Hölder dependence of the convexified cost on the other players' actions. -/
theorem holder_others {n d q : ℕ} {X : Fin n → Set (E d)} {A : Fin n → (E d →L[ℝ] E q)}
    {θ : Fin n → E d → E q → ℝ} {Ω : Set (E q)} {Δ M H γ : ℝ}
    (hstd : StandingHyp X A Ω Δ M) (hA1 : Assumption1 X Ω θ H γ) (x x' : Fin n → E d)
    (hx : ∀ j, x j ∈ convexHull ℝ (X j)) (hx' : ∀ j, x' j ∈ convexHull ℝ (X j)) (i : Fin n)
    (y : E d) (hy : y ∈ convexHull ℝ (X i)) :
    convCost X θ A i (Function.update x' i y) ≤ convCost X θ A i (Function.update x i y) +
      H * ‖aggregate A (Function.update x' i y) - aggregate A (Function.update x i y)‖ ^ γ := by
  obtain ⟨α, hα, z, hz, hs, hval, -⟩ := attain hstd hA1 x hx i y hy
  obtain ⟨-, -, -, -, -, -, hlow⟩ := attain hstd hA1 x' hx' i y hy
  refine (hlow α hα z hz hs).trans ?_
  rw [← hval]
  have hk : ∀ k, cost θ A i (Function.update x' i (z k)) ≤ cost θ A i (Function.update x i (z k)) +
      H * ‖aggregate A (Function.update x' i y) - aggregate A (Function.update x i y)‖ ^ γ := by
    intro k
    have h1 := hA1.2.2.2 i (z k) (hz k) _
      (agg_mem hstd _ (update_mem_conv x hx i _ (subset_convexHull ℝ _ (hz k)))) _
      (agg_mem hstd _ (update_mem_conv x' hx' i _ (subset_convexHull ℝ _ (hz k))))
    rw [agg_diff A x x' i (z k) y, abs_le] at h1
    simp only [cost, Function.update_self]
    linarith [h1.2]
  calc ∑ k, α k * cost θ A i (Function.update x' i (z k))
      ≤ ∑ k, α k * (cost θ A i (Function.update x i (z k)) +
          H * ‖aggregate A (Function.update x' i y) - aggregate A (Function.update x i y)‖ ^ γ) :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hk k) (hα.1 k)
    _ = _ := by simp [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hα.2]

/-- Lower semicontinuity of the convexified cost in the own action. -/
theorem lsc_own {n d q : ℕ} {X : Fin n → Set (E d)} {A : Fin n → (E d →L[ℝ] E q)}
    {θ : Fin n → E d → E q → ℝ} {Ω : Set (E q)} {Δ M H γ : ℝ}
    (hstd : StandingHyp X A Ω Δ M) (hA1 : Assumption1 X Ω θ H γ) (x : Fin n → E d)
    (hx : ∀ j, x j ∈ convexHull ℝ (X j)) (i : Fin n) :
    LowerSemicontinuousOn (fun y => convCost X θ A i (Function.update x i y))
      (convexHull ℝ (X i)) := by
  intro y0 hy0 c hc
  change c < convCost X θ A i (Function.update x i y0) at hc
  show ∀ᶠ y in nhdsWithin y0 (convexHull ℝ (X i)), c < convCost X θ A i (Function.update x i y)
  obtain ⟨m, hm, -⟩ := convCost_bdd hstd hA1 i x hx
  set g := fun z => cost θ A i (Function.update x i z) with hg
  have hgl : LowerSemicontinuousOn (fun z => g z - m) (X i) := by
    intro z hz y hy
    exact (lsc_g hstd hA1 x hx i z hz (y + m) (by simp only [hg] at hy ⊢; linarith)).mono
      fun z h => by simp only [hg] at h ⊢; linarith
  set S : Set ((Fin (d + 1) → ℝ) × (Fin (d + 1) → E d)) :=
    stdSimplex ℝ (Fin (d + 1)) ×ˢ Set.pi Set.univ (fun _ => X i) with hS
  have hSc : IsCompact S := (isCompact_stdSimplex ℝ _).prod (isCompact_univ_pi fun _ => hstd.1 i)
  set F : (Fin (d + 1) → ℝ) × (Fin (d + 1) → E d) → ℝ :=
    fun p => ∑ k, p.1 k * (g (p.2 k) - m) with hF
  have hFl : LowerSemicontinuousOn F S := by
    refine lowerSemicontinuousOn_sum fun k _ => lsc_mul ?_ ?_ ?_ ?_
    · exact ((continuous_apply k).comp continuous_fst).continuousOn
    · exact lsc_comp hgl ((continuous_apply k).comp continuous_snd).continuousOn
        fun p hp => hp.2 k (Set.mem_univ k)
    · exact fun p hp => hp.1.1 k
    · exact fun p hp => by simp only [hg]; linarith [hm _ (hp.2 k (Set.mem_univ k))]
  have hFe : ∀ p ∈ S, F p = ∑ k, p.1 k * g (p.2 k) - m := by
    intro p hp
    simp only [hF, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp.1.2, one_mul]
  obtain ⟨v, hv, hQ⟩ := lowerSemicontinuousOn_iff_preimage_Iic.1 hFl (c - m)
  have hQc : IsCompact (S ∩ v) := hSc.inter_right hv
  have hπ : Continuous fun p : (Fin (d + 1) → ℝ) × (Fin (d + 1) → E d) => ∑ k, p.1 k • p.2 k := by
    fun_prop
  have hcl : IsClosed ((fun p : (Fin (d + 1) → ℝ) × (Fin (d + 1) → E d) => ∑ k, p.1 k • p.2 k) ''
      (S ∩ v)) := (hQc.image hπ).isClosed
  have hnot : y0 ∉ (fun p : (Fin (d + 1) → ℝ) × (Fin (d + 1) → E d) => ∑ k, p.1 k • p.2 k) ''
      (S ∩ v) := by
    rintro ⟨p, hpQ, hpy⟩
    have hpS : p ∈ S := hpQ.1
    have hpQ' := hpQ
    rw [← hQ] at hpQ'
    have hFp : F p ≤ c - m := hpQ'.2
    obtain ⟨-, -, -, -, -, -, hlow⟩ := attain hstd hA1 x hx i y0 hy0
    have := hlow p.1 hpS.1 p.2 (fun k => hpS.2 k (Set.mem_univ k)) hpy
    rw [hFe p hpS] at hFp
    simp only [hg] at hFp
    linarith
  have hO := hcl.isOpen_compl.mem_nhds hnot
  filter_upwards [nhdsWithin_le_nhds hO, self_mem_nhdsWithin] with y hyQ hy
  by_contra hle
  push Not at hle
  obtain ⟨α, hα, z, hz, hs, hval, -⟩ := attain hstd hA1 x hx i y hy
  apply hyQ
  have hpS : ((α, z) : (Fin (d + 1) → ℝ) × (Fin (d + 1) → E d)) ∈ S := ⟨hα, fun k _ => hz k⟩
  refine ⟨(α, z), ?_, hs⟩
  rw [← hQ]
  refine ⟨hpS, ?_⟩
  show F (α, z) ≤ c - m
  rw [hFe _ hpS]
  simp only [hg]
  linarith

/-! ### The proximal best-response map -/

theorem conv_compact {d : ℕ} (S : Set (E d)) (hc : IsCompact S) : IsCompact (convexHull ℝ S) := by
  classical
  rcases S.eq_empty_or_nonempty with hS | ⟨x0, hx0⟩
  · rw [hS, convexHull_empty]; exact isCompact_empty
  have : convexHull ℝ S =
      (fun p : (Fin (d + 1) → ℝ) × (Fin (d + 1) → E d) => ∑ k, p.1 k • p.2 k) ''
        (stdSimplex ℝ (Fin (d + 1)) ×ˢ Set.pi Set.univ (fun _ => S)) := by
    ext y
    constructor
    · intro hy
      obtain ⟨ι, hι, w, z, hw0, hw1, hz, hwz⟩ := mem_convexHull_iff_exists_fintype.1 hy
      obtain ⟨α, hα, w', hw', hs, -⟩ := rep_fin S x0 hx0 (fun _ => 0) w z hw0 hw1 hz
      exact ⟨(α, w'), ⟨hα, fun k _ => hw' k⟩, hs.trans hwz⟩
    · rintro ⟨p, ⟨hα, hz⟩, rfl⟩
      exact (convex_convexHull ℝ S).sum_mem (fun k _ => hα.1 k) hα.2
        (fun k _ => subset_convexHull ℝ S (hz k (Set.mem_univ k)))
  rw [this]
  exact ((isCompact_stdSimplex ℝ _).prod (isCompact_univ_pi fun _ => hc)).image (by fun_prop)

/-- The proximal objective of player `i` at the profile `x`. -/
noncomputable def psi {n d q : ℕ} (X : Fin n → Set (E d)) (θ : Fin n → E d → E q → ℝ)
    (A : Fin n → (E d →L[ℝ] E q)) (i : Fin n) (x : Fin n → E d) (y : E d) : ℝ :=
  convCost X θ A i (Function.update x i y) + ‖y - x i‖ ^ 2

theorem psi_lsc {n d q : ℕ} {X : Fin n → Set (E d)} {A : Fin n → (E d →L[ℝ] E q)}
    {θ : Fin n → E d → E q → ℝ} {Ω : Set (E q)} {Δ M H γ : ℝ}
    (hstd : StandingHyp X A Ω Δ M) (hA1 : Assumption1 X Ω θ H γ) (x : Fin n → E d)
    (hx : ∀ j, x j ∈ convexHull ℝ (X j)) (i : Fin n) :
    LowerSemicontinuousOn (psi X θ A i x) (convexHull ℝ (X i)) := by
  have h2 : Continuous fun y : E d => ‖y - x i‖ ^ 2 := by fun_prop
  exact (lsc_own hstd hA1 x hx i).add h2.continuousOn.lowerSemicontinuousOn

theorem prox_exists {n d q : ℕ} {X : Fin n → Set (E d)} {A : Fin n → (E d →L[ℝ] E q)}
    {θ : Fin n → E d → E q → ℝ} {Ω : Set (E q)} {Δ M H γ : ℝ}
    (hstd : StandingHyp X A Ω Δ M) (hA1 : Assumption1 X Ω θ H γ) (x : Fin n → E d)
    (hx : ∀ j, x j ∈ convexHull ℝ (X j)) (i : Fin n) :
    ∃ y ∈ convexHull ℝ (X i), ∀ w ∈ convexHull ℝ (X i), psi X θ A i x y ≤ psi X θ A i x w := by
  obtain ⟨y, hy, hmin⟩ := (psi_lsc hstd hA1 x hx i).exists_isMinOn ⟨x i, hx i⟩
    (conv_compact _ (hstd.1 i))
  exact ⟨y, hy, fun w hw => isMinOn_iff.1 hmin w hw⟩

theorem prox_unique {n d q : ℕ} {X : Fin n → Set (E d)} {A : Fin n → (E d →L[ℝ] E q)}
    {θ : Fin n → E d → E q → ℝ} {Ω : Set (E q)} {Δ M H γ : ℝ}
    (hstd : StandingHyp X A Ω Δ M) (hA1 : Assumption1 X Ω θ H γ) (x : Fin n → E d)
    (hx : ∀ j, x j ∈ convexHull ℝ (X j)) (i : Fin n) (y1 y2 : E d)
    (hy1 : y1 ∈ convexHull ℝ (X i)) (hy2 : y2 ∈ convexHull ℝ (X i))
    (h1 : ∀ w ∈ convexHull ℝ (X i), psi X θ A i x y1 ≤ psi X θ A i x w)
    (h2 : ∀ w ∈ convexHull ℝ (X i), psi X θ A i x y2 ≤ psi X θ A i x w) : y1 = y2 := by
  have hm : (1 / 2 : ℝ) • y1 + (1 / 2 : ℝ) • y2 ∈ convexHull ℝ (X i) :=
    convex_convexHull ℝ _ hy1 hy2 (by norm_num) (by norm_num) (by norm_num)
  have hcv := (conv_own hstd hA1 x hx i).2 hy1 hy2 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hcv
  have hpar : ‖(1 / 2 : ℝ) • y1 + (1 / 2 : ℝ) • y2 - x i‖ ^ 2 =
      (‖y1 - x i‖ ^ 2 + ‖y2 - x i‖ ^ 2) / 2 - ‖y1 - y2‖ ^ 2 / 4 := by
    have e1 : (1 / 2 : ℝ) • y1 + (1 / 2 : ℝ) • y2 - x i = (1 / 2 : ℝ) • ((y1 - x i) + (y2 - x i)) := by
      module
    have e2 : y1 - y2 = (y1 - x i) - (y2 - x i) := by abel
    have hp := parallelogram_law_with_norm ℝ (y1 - x i) (y2 - x i)
    rw [e1, e2, norm_smul, mul_pow, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    linear_combination (1 / 4 : ℝ) * hp
  have a1 := h1 _ hm
  have a2 := h2 y1 hy1
  have a3 := h1 y2 hy2
  simp only [psi] at a1 a2 a3
  rw [hpar] at a1
  have h0 : ‖y1 - y2‖ = 0 := by nlinarith [norm_nonneg (y1 - y2)]
  exact sub_eq_zero.1 (norm_eq_zero.1 h0)

theorem sq_diff (a b D Δ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (haΔ : a ≤ Δ) (hbΔ : b ≤ Δ)
    (h : |a - b| ≤ D) : |a ^ 2 - b ^ 2| ≤ 2 * Δ * D := by
  rw [abs_le] at *
  obtain ⟨h1, h2⟩ := h
  constructor <;> nlinarith

theorem agg_cont {n d q : ℕ} (A : Fin n → (E d →L[ℝ] E q)) :
    Continuous fun u : Fin n → E d => aggregate A u := by
  unfold aggregate
  exact (continuous_finsetSum _ fun j _ => (A j).continuous.comp (continuous_apply j)).const_smul
    ((n : ℝ)⁻¹)

theorem prox_cont {n d q : ℕ} {X : Fin n → Set (E d)} {A : Fin n → (E d →L[ℝ] E q)}
    {θ : Fin n → E d → E q → ℝ} {Ω : Set (E q)} {Δ M H γ : ℝ}
    (hstd : StandingHyp X A Ω Δ M) (hA1 : Assumption1 X Ω θ H γ)
    (Φ : (Fin n → E d) → Fin n → E d)
    (hΦ : ∀ x, (∀ j, x j ∈ convexHull ℝ (X j)) → ∀ i, Φ x i ∈ convexHull ℝ (X i) ∧
      ∀ w ∈ convexHull ℝ (X i), psi X θ A i x (Φ x i) ≤ psi X θ A i x w) :
    ContinuousOn Φ {x | ∀ j, x j ∈ convexHull ℝ (X j)} := by
  obtain ⟨hc, -, -, hdiam, -, -, -⟩ := id hstd
  have hγ := hA1.2.2.1
  intro x hx
  rw [continuousWithinAt_pi]
  intro i
  apply (conv_compact _ (hstd.1 i)).tendsto_nhds_of_unique_mapClusterPt
  · filter_upwards [self_mem_nhdsWithin] with x' hx' using (hΦ x' hx' i).1
  intro a ha hcl
  refine prox_unique hstd hA1 x hx i a (Φ x i) ha (hΦ x hx i).1 ?_ (hΦ x hx i).2
  intro w hw
  by_contra hlt
  push Not at hlt
  set ε := (psi X θ A i x a - psi X θ A i x w) / 4 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  have E1 : ∀ᶠ y' in nhds a, y' ∈ convexHull ℝ (X i) → psi X θ A i x a - ε < psi X θ A i x y' :=
    eventually_nhdsWithin_iff.1 (psi_lsc hstd hA1 x hx i a ha _ (by linarith))
  have F1 := hcl.frequently E1
  set e : (Fin n → E d) → ℝ := fun x' =>
    H * ‖aggregate A (Function.update x' i w) - aggregate A (Function.update x i w)‖ ^ γ +
      2 * Δ * ‖x' i - x i‖ with hedef
  have he : Continuous e := by
    have hu : Continuous fun x' : Fin n → E d => aggregate A (Function.update x' i w) :=
      (agg_cont A).comp (continuous_id.update i continuous_const)
    exact (continuous_const.mul ((hu.sub continuous_const).norm.rpow_const
      fun _ => Or.inr hγ.le)).add
      (continuous_const.mul (((continuous_apply i).sub continuous_const).norm))
  have he0 : e x = 0 := by simp [hedef, Real.zero_rpow hγ.ne']
  have E2 : ∀ᶠ x' in nhdsWithin x {x | ∀ j, x j ∈ convexHull ℝ (X j)},
      (∀ j, x' j ∈ convexHull ℝ (X j)) ∧ e x' < ε :=
    Filter.Eventually.and (self_mem_nhdsWithin (s := {x | ∀ j, x j ∈ convexHull ℝ (X j)}) (a := x))
      (nhdsWithin_le_nhds
      (he.continuousAt.eventually (gt_mem_nhds (show e x < ε by rw [he0]; exact hε))))
  obtain ⟨x', hfr, hx'K, hex'⟩ := (F1.and_eventually E2).exists
  have hy' := hΦ x' hx'K i
  have b1 := hfr hy'.1
  have b2 := hy'.2 w hw
  have hcomp : ∀ y ∈ convexHull ℝ (X i), |psi X θ A i x' y - psi X θ A i x y| ≤ e x' := by
    intro y hy
    have ha1 := holder_others hstd hA1 x x' hx hx'K i y hy
    have hb1 := holder_others hstd hA1 x' x hx'K hx i y hy
    rw [agg_diff A x x' i y w] at ha1
    rw [norm_sub_rev, agg_diff A x x' i y w] at hb1
    have hd : |‖y - x' i‖ - ‖y - x i‖| ≤ ‖x' i - x i‖ := by
      have := abs_norm_sub_norm_le (y - x' i) (y - x i)
      rwa [show (y - x' i) - (y - x i) = x i - x' i by abel, norm_sub_rev (x i) (x' i)] at this
    have hsq := sq_diff _ _ _ _ (norm_nonneg _) (norm_nonneg _)
      (dist_le_conv hc hdiam i _ _ hy (hx'K i)) (dist_le_conv hc hdiam i _ _ hy (hx i)) hd
    simp only [psi, hedef]
    rw [abs_le] at hsq ⊢
    constructor <;> linarith [hsq.1, hsq.2]
  have c1 := hcomp _ hy'.1
  have c2 := hcomp w hw
  rw [abs_le] at c1 c2
  linarith [c1.1, c1.2, c2.1, c2.2]

/-- A fixed point of the proximal map is a pure Nash equilibrium of the convexified game. -/
theorem fixed_pne {n d q : ℕ} {X : Fin n → Set (E d)} {A : Fin n → (E d →L[ℝ] E q)}
    {θ : Fin n → E d → E q → ℝ} {Ω : Set (E q)} {Δ M H γ : ℝ}
    (hstd : StandingHyp X A Ω Δ M) (hA1 : Assumption1 X Ω θ H γ) (x : Fin n → E d)
    (hx : ∀ j, x j ∈ convexHull ℝ (X j))
    (hfix : ∀ i, ∀ w ∈ convexHull ℝ (X i), psi X θ A i x (x i) ≤ psi X θ A i x w) :
    IsEpsPNE (fun i => convexHull ℝ (X i)) (convCost X θ A) 0 x := by
  refine ⟨hx, fun i w hw => ?_⟩
  rw [add_zero]
  have hcv := conv_own hstd hA1 x hx i
  apply le_of_forall_pos_le_add
  intro ε hε
  set D := ‖w - x i‖ ^ 2 with hD
  have hD0 : 0 ≤ D := by positivity
  set t := min 1 (ε / (D + 1)) with ht
  have ht0 : 0 < t := lt_min one_pos (div_pos hε (by linarith))
  have ht1 : t ≤ 1 := min_le_left _ _
  have htD : t * D ≤ ε := by
    have h1 : t ≤ ε / (D + 1) := min_le_right _ _
    have h2 : t * (D + 1) ≤ ε := by rwa [le_div_iff₀ (by linarith)] at h1
    nlinarith
  have hyt : (1 - t) • x i + t • w ∈ convexHull ℝ (X i) :=
    convex_convexHull ℝ _ (hx i) hw (by linarith) ht0.le (by ring)
  have hconv := hcv.2 (hx i) hw (by linarith : (0 : ℝ) ≤ 1 - t) ht0.le (by ring)
  simp only [smul_eq_mul, Function.update_eq_self] at hconv
  have hmin := hfix i _ hyt
  simp only [psi, Function.update_eq_self, sub_self, norm_zero] at hmin
  have hn : ‖(1 - t) • x i + t • w - x i‖ ^ 2 = t ^ 2 * D := by
    rw [show (1 - t) • x i + t • w - x i = t • (w - x i) by module, norm_smul,
      Real.norm_of_nonneg ht0.le, mul_pow]
  rw [hn] at hmin
  have key : t * convCost X θ A i x ≤ t * (convCost X θ A i (Function.update x i w) + t * D) := by
    nlinarith
  have := le_of_mul_le_mul_left key ht0
  linarith

/-! ### Brouwer's theorem on the product of the convexified action sets -/

/-- Brouwer via a retraction onto `K` and a left-invertible continuous chart into a cube space. -/
theorem brouwer_chart {V : Type*} [TopologicalSpace V] {N : ℕ} (h : V → (Fin N → ℝ))
    (h' : (Fin N → ℝ) → V) (hh : Continuous h) (hh' : Continuous h') (hinv : ∀ u, h' (h u) = u)
    (K : Set V) (hK : IsCompact K) (r : V → V) (hr : Continuous r) (hrK : ∀ u, r u ∈ K)
    (hrfix : ∀ u ∈ K, r u = u) (f : V → V) (hf : ContinuousOn f K) (hfK : Set.MapsTo f K K) :
    ∃ u ∈ K, f u = u := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hh.continuousOn
  set R := max C 1 with hR
  have hR1 : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hb : ∀ u ∈ K, ∀ j, |h u j| ≤ R := by
    intro u hu j
    have := (norm_le_pi_norm (h u) j).trans (hC u hu)
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  set s : (Fin N → ℝ) → (Fin N → ℝ) := fun v j => 2 * R * v j - R with hs
  set g : (Fin N → ℝ) → (Fin N → ℝ) := fun v j => (h (f (r (h' (s v)))) j + R) / (2 * R) with hg
  have hfr : Continuous fun w => f (r w) := hf.comp_continuous hr hrK
  have hsc : Continuous s := by
    simp only [hs]
    exact continuous_pi fun j => (continuous_const.mul (continuous_apply j)).sub continuous_const
  have hgc : Continuous g := by
    have h1 : Continuous fun v => h (f (r (h' (s v)))) := hh.comp (hfr.comp (hh'.comp hsc))
    exact continuous_pi fun j =>
      (((continuous_apply j).comp h1).add continuous_const).div_const _
  obtain ⟨v, -, hfix⟩ := BrouwerLib.brouwer_cube N g hgc (by
    intro v _ j
    have hm := hb _ (hfK (hrK (h' (s v)))) j
    rw [abs_le] at hm
    constructor
    · simp only [hg]; exact div_nonneg (by linarith) (by linarith)
    · simp only [hg]; rw [div_le_one (by linarith)]; linarith)
  have hsv : h (f (r (h' (s v)))) = s v := by
    funext j
    have := congrFun hfix j
    simp only [hg] at this
    rw [div_eq_iff (by positivity)] at this
    simp only [hs]
    linarith
  have hfu : f (r (h' (s v))) = h' (s v) := by
    have := congrArg h' hsv
    rwa [hinv] at this
  refine ⟨r (h' (s v)), hrK _, ?_⟩
  have h2 : r (f (r (h' (s v)))) = f (r (h' (s v))) := hrfix _ (hfK (hrK _))
  rw [hfu] at h2
  rw [hfu, h2]

noncomputable def chart {n d : ℕ} (x : Fin n → E d) : Fin (n * d) → ℝ :=
  fun j => (EuclideanSpace.equiv (Fin d) ℝ) (x (finProdFinEquiv.symm j).1) (finProdFinEquiv.symm j).2

noncomputable def unchart {n d : ℕ} (u : Fin (n * d) → ℝ) : Fin n → E d :=
  fun a => (EuclideanSpace.equiv (Fin d) ℝ).symm (fun b => u (finProdFinEquiv (a, b)))

theorem unchart_chart {n d : ℕ} (x : Fin n → E d) : unchart (chart x) = x := by
  funext a
  simp [chart, unchart]

theorem chart_cont {n d : ℕ} : Continuous (chart (n := n) (d := d)) :=
  continuous_pi fun j => (continuous_apply _).comp
    ((EuclideanSpace.equiv (Fin d) ℝ).continuous.comp (continuous_apply _))

theorem unchart_cont {n d : ℕ} : Continuous (unchart (n := n) (d := d)) :=
  continuous_pi fun a => (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous.comp
    (continuous_pi fun b => continuous_apply _)

/-- Metric projection onto a nonempty compact convex set: a continuous retraction. -/
theorem proj_exists {d : ℕ} (C : Set (E d)) (hC : IsCompact C) (hcv : Convex ℝ C)
    (hne : C.Nonempty) : ∃ P : E d → E d, Continuous P ∧ (∀ y, P y ∈ C) ∧ ∀ y ∈ C, P y = y := by
  have hex : ∀ u : E d, ∃ v ∈ C, ∀ w ∈ C, inner ℝ (u - v) (w - v) ≤ 0 := by
    intro u
    obtain ⟨v, hv, hvn⟩ := exists_norm_eq_iInf_of_complete_convex hne hC.isComplete hcv u
    exact ⟨v, hv, (norm_eq_iInf_iff_real_inner_le_zero hcv hv).1 hvn⟩
  choose P hPC hPi using hex
  refine ⟨P, ?_, hPC, fun y hy => ?_⟩
  · refine (LipschitzWith.of_dist_le_mul (K := 1) fun x y => ?_).continuous
    have h1 := hPi x (P y) (hPC y)
    have h2 := hPi y (P x) (hPC x)
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
    have hxy : x - y = (x - P x) - (y - P y) + (P x - P y) := by abel
    have h1' : 0 ≤ inner ℝ (x - P x) (P x - P y) := by
      rw [show P y - P x = -(P x - P y) by abel, inner_neg_right] at h1
      linarith
    have key : ‖P x - P y‖ ^ 2 ≤ inner ℝ (x - y) (P x - P y) := by
      rw [hxy, inner_add_left, inner_sub_left, real_inner_self_eq_norm_sq]
      linarith
    have cs := real_inner_le_norm (x - y) (P x - P y)
    by_cases h0 : ‖P x - P y‖ = 0
    · rw [h0]; exact norm_nonneg _
    · have hpos : 0 < ‖P x - P y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      nlinarith
  · have h0 := hPi y y hy
    rw [real_inner_self_eq_norm_sq] at h0
    have : ‖y - P y‖ = 0 := by nlinarith [norm_nonneg (y - P y)]
    exact (sub_eq_zero.1 (norm_eq_zero.1 this)).symm

theorem brouwer_K {n d q : ℕ} {X : Fin n → Set (E d)} {A : Fin n → (E d →L[ℝ] E q)}
    {Ω : Set (E q)} {Δ M : ℝ} (hstd : StandingHyp X A Ω Δ M) (f : (Fin n → E d) → Fin n → E d)
    (hf : ContinuousOn f {x | ∀ j, x j ∈ convexHull ℝ (X j)})
    (hfK : Set.MapsTo f {x | ∀ j, x j ∈ convexHull ℝ (X j)} {x | ∀ j, x j ∈ convexHull ℝ (X j)}) :
    ∃ x ∈ {x | ∀ j, x j ∈ convexHull ℝ (X j)}, f x = x := by
  have hP := fun j => proj_exists (convexHull ℝ (X j)) (conv_compact _ (hstd.1 j))
    (convex_convexHull ℝ _) ((hstd.2.1 j).mono (subset_convexHull ℝ _))
  choose P hPc hPC hPfix using hP
  have hK : IsCompact {x : Fin n → E d | ∀ j, x j ∈ convexHull ℝ (X j)} := by
    have e : {x : Fin n → E d | ∀ j, x j ∈ convexHull ℝ (X j)} =
        Set.univ.pi (fun j => convexHull ℝ (X j)) := by
      ext x; simp
    rw [e]
    exact isCompact_univ_pi fun j => conv_compact _ (hstd.1 j)
  exact brouwer_chart chart unchart chart_cont unchart_cont unchart_chart _ hK
    (fun x j => P j (x j)) (continuous_pi fun j => (hPc j).comp (continuous_apply j))
    (fun x j => hPC j (x j)) (fun x hx => funext fun j => hPfix j _ (hx j)) f hf hfK

/-- The convexified game has a pure Nash equilibrium. -/
theorem pne_exists {n d q : ℕ} {X : Fin n → Set (E d)} {A : Fin n → (E d →L[ℝ] E q)}
    {θ : Fin n → E d → E q → ℝ} {Ω : Set (E q)} {Δ M H γ : ℝ}
    (hstd : StandingHyp X A Ω Δ M) (hA1 : Assumption1 X Ω θ H γ) :
    ∃ xt : Fin n → E d, IsEpsPNE (fun i => convexHull ℝ (X i)) (convCost X θ A) 0 xt := by
  have hex := fun (x : Fin n → E d) (hx : ∀ j, x j ∈ convexHull ℝ (X j)) (i : Fin n) =>
    prox_exists hstd hA1 x hx i
  choose! Φ hΦC hΦm using hex
  have hcont := prox_cont hstd hA1 Φ (fun x hx i => ⟨hΦC x hx i, hΦm x hx i⟩)
  obtain ⟨x, hx, hfix⟩ := brouwer_K hstd Φ hcont (fun x hx i => hΦC x hx i)
  refine ⟨x, fixed_pne hstd hA1 x hx fun i w hw => ?_⟩
  have := hΦm x hx i w hw
  rwa [hfix] at this
end AggNashP

open AggNash.Existence in
theorem solution
    {n d q : ℕ} (X : Fin n → Set (E d)) (A : Fin n → (E d →L[ℝ] E q))
    (θ : Fin n → E d → E q → ℝ) (Ω : Set (E q)) (Δ M H γ : ℝ)
    (hstd : StandingHyp X A Ω Δ M) (hA1 : Assumption1 X Ω θ H γ) :
    (∃ x : Fin n → E d, IsEpsPNE X (cost θ A)
      (2 * H * (((Real.sqrt (q : ℝ) + 1) * M * Δ) / (n : ℝ)) ^ γ) x) ∧
    ∀ xt : Fin n → E d, IsEpsPNE (fun i => convexHull ℝ (X i)) (convCost X θ A) 0 xt →
      ∀ Z : Fin n → Set (E d), (∀ i, IsGenerator X θ A i xt (Z i)) →
      ∀ xs : Fin n → E d, (∀ i, xs i ∈ Z i) →
      (∀ x' : Fin n → E d, (∀ i, x' i ∈ Z i) →
        ‖∑ i, A i (xt i) - ∑ i, A i (xs i)‖ ^ 2 ≤ ‖∑ i, A i (xt i) - ∑ i, A i (x' i)‖ ^ 2) →
      IsEpsPNE X (cost θ A)
        (2 * H * (((Real.sqrt (q : ℝ) + 1) * M * Δ) / (n : ℝ)) ^ γ) xs := by
  exact AggNashP.prop24_of X A θ Ω Δ M H γ hstd hA1 (AggNashP.pne_exists hstd hA1)
    (fun xt h i => AggNashP.gen_exists hstd hA1 xt h i)
