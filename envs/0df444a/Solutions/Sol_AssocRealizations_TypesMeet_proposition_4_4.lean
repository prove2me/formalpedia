-- Prove2me | solution 1 for AssocRealizations.TypesMeet.proposition_4_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-31T13:23:22.281891+00:00
-- url     : https://prove2.me/submissions/81b771a6-f5fd-49df-af43-a10ec793273f

import Mathlib
import Definitions.Def_AssocRealizations_TypesMeet_Setting

set_option autoImplicit false
set_option linter.all false

open ChvatalArtGallery.FanPartition

namespace Phl

open AssocRealizations.TypesMeet

/-! ## Part A: cdist and dihedral basics (from the corollary_5_7 development) -/
lemma cdist_eq_sub {N : ℕ} [NeZero N] (a c : Fin N) : cdist a c = (c - a).val := by
  unfold cdist
  rw [Fin.sub_def]
  simp only
  congr 1
  have := a.isLt
  omega

lemma cdist_lt {N : ℕ} [NeZero N] (a c : Fin N) : cdist a c < N := by
  rw [cdist_eq_sub]; exact (c - a).isLt

lemma cdist_eq_zero {N : ℕ} [NeZero N] (a c : Fin N) : cdist a c = 0 ↔ a = c := by
  rw [cdist_eq_sub, Fin.val_eq_zero_iff, sub_eq_zero, eq_comm]

lemma cdist_swap {N : ℕ} [NeZero N] (a c : Fin N) (h : a ≠ c) :
    cdist c a = N - cdist a c := by
  rw [cdist_eq_sub, cdist_eq_sub]
  have h1 : a - c = -(c - a) := by abel
  rw [h1, Fin.coe_neg]
  have h2 : (c - a).val ≠ 0 := by
    intro h0
    rw [Fin.val_eq_zero_iff, sub_eq_zero] at h0
    exact h h0.symm
  have h3 := (c - a).isLt
  rw [Nat.mod_eq_of_lt (by omega)]

lemma cdist_rot {N : ℕ} [NeZero N] (r a c : Fin N) : cdist (r + a) (r + c) = cdist a c := by
  rw [cdist_eq_sub, cdist_eq_sub]; congr 1; abel

lemma cdist_refl {N : ℕ} [NeZero N] (r a c : Fin N) : cdist (r - a) (r - c) = cdist c a := by
  rw [cdist_eq_sub, cdist_eq_sub]; congr 1; abel

/-! ## dihedral maps -/

lemma dihedral_injective {N : ℕ} [NeZero N] (r : Fin N) (refl : Bool) :
    Function.Injective (dihedral r refl) := by
  intro x y h
  cases refl
  · simpa [dihedral] using h
  · simpa [dihedral] using h

/-- inverse of a dihedral map -/
def dihInv {N : ℕ} [NeZero N] (r : Fin N) (refl : Bool) : Fin N → Fin N :=
  if refl then dihedral r true else dihedral (-r) false

lemma dihInv_left {N : ℕ} [NeZero N] (r : Fin N) (refl : Bool) (x : Fin N) :
    dihInv r refl (dihedral r refl x) = x := by
  cases refl <;> simp [dihInv, dihedral]

lemma dihInv_right {N : ℕ} [NeZero N] (r : Fin N) (refl : Bool) (x : Fin N) :
    dihedral r refl (dihInv r refl x) = x := by
  cases refl <;> simp [dihInv, dihedral]

lemma crosses_dihedral {N : ℕ} [NeZero N] (r : Fin N) (refl : Bool) (e f : Sym2 (Fin N))
    (h : Crosses e f) : Crosses (Sym2.map (dihedral r refl) e) (Sym2.map (dihedral r refl) f) := by
  obtain ⟨a, b, c, d, rfl, rfl, h1, h2, h3⟩ := h
  cases refl
  · refine ⟨r + a, r + b, r + c, r + d, by simp [dihedral], by simp [dihedral], ?_⟩
    simp only [cdist_rot]; exact ⟨h1, h2, h3⟩
  · have h0 : cdist a a = 0 := (cdist_eq_zero a a).2 rfl
    have hac : a ≠ c := by intro h; subst h; omega
    have hab : a ≠ b := by intro h; subst h; omega
    have had : a ≠ d := by intro h; subst h; omega
    have hd := cdist_lt a d
    refine ⟨r - a, r - b, r - d, r - c, by simp [dihedral], by simp [dihedral, Sym2.eq_swap], ?_⟩
    simp only [cdist_refl]
    rw [cdist_swap a c hac, cdist_swap a b hab, cdist_swap a d had]
    omega

lemma dihInv_eq {N : ℕ} [NeZero N] (r : Fin N) (refl : Bool) :
    ∃ r' refl', dihInv r refl = dihedral r' refl' := by
  cases refl
  · exact ⟨-r, false, rfl⟩
  · exact ⟨r, true, rfl⟩

lemma map_dihInv_map {N : ℕ} [NeZero N] (r : Fin N) (refl : Bool) (e : Sym2 (Fin N)) :
    Sym2.map (dihInv r refl) (Sym2.map (dihedral r refl) e) = e := by
  rw [Sym2.map_map]
  have : (dihInv r refl ∘ dihedral r refl) = id := funext (dihInv_left r refl)
  rw [this, Sym2.map_id, id]

lemma map_dihedral_map_inv {N : ℕ} [NeZero N] (r : Fin N) (refl : Bool) (e : Sym2 (Fin N)) :
    Sym2.map (dihedral r refl) (Sym2.map (dihInv r refl) e) = e := by
  rw [Sym2.map_map]
  have : (dihedral r refl ∘ dihInv r refl) = id := funext (dihInv_right r refl)
  rw [this, Sym2.map_id, id]

lemma crosses_dihedral_iff {N : ℕ} [NeZero N] (r : Fin N) (refl : Bool) (e f : Sym2 (Fin N)) :
    Crosses (Sym2.map (dihedral r refl) e) (Sym2.map (dihedral r refl) f) ↔ Crosses e f := by
  refine ⟨fun h => ?_, crosses_dihedral r refl e f⟩
  obtain ⟨r', refl', hr⟩ := dihInv_eq r refl
  have := crosses_dihedral r' refl' _ _ h
  rwa [← hr, map_dihInv_map, map_dihInv_map] at this

lemma diagonal_dihedral {N : ℕ} [NeZero N] (r : Fin N) (refl : Bool) (e : Sym2 (Fin N))
    (h : IsDiagonal e) : IsDiagonal (Sym2.map (dihedral r refl) e) := by
  induction e using Sym2.ind with
  | _ x y =>
  have hxy := h x y rfl
  intro a b hab
  simp only [Sym2.map_pair_eq, Sym2.eq_iff] at hab
  have hne : dihedral r refl x ≠ dihedral r refl y :=
    fun h' => hxy.1 (dihedral_injective r refl h')
  have key : cdist (dihedral r refl x) (dihedral r refl y) ≠ 1 ∧
      cdist (dihedral r refl y) (dihedral r refl x) ≠ 1 := by
    cases refl
    · show cdist (r + x) (r + y) ≠ 1 ∧ cdist (r + y) (r + x) ≠ 1
      rw [cdist_rot, cdist_rot]; exact ⟨hxy.2.1, hxy.2.2⟩
    · show cdist (r - x) (r - y) ≠ 1 ∧ cdist (r - y) (r - x) ≠ 1
      rw [cdist_refl, cdist_refl]; exact ⟨hxy.2.2, hxy.2.1⟩
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨hne, key.1, key.2⟩
  · exact ⟨fun h' => hne h'.symm, key.2, key.1⟩

/-! ## the easy direction -/

lemma cdist_of_le {N : ℕ} [NeZero N] (x y : Fin N) (h : x.val ≤ y.val) :
    cdist x y = y.val - x.val := by
  unfold cdist
  have := y.isLt
  rw [show y.val + N - x.val = (y.val - x.val) + N by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]

lemma cdist_of_gt {N : ℕ} [NeZero N] (x y : Fin N) (h : y.val < x.val) :
    cdist x y = y.val + N - x.val := by
  unfold cdist
  have := x.isLt
  rw [Nat.mod_eq_of_lt (by omega)]

lemma cdist_add_self {N : ℕ} [NeZero N] (a x : Fin N) : cdist a (a + x) = x.val := by
  rw [cdist_eq_sub, add_sub_cancel_left]

lemma cdist_tri {N : ℕ} [NeZero N] (a b c : Fin N) (h : cdist a c ≤ cdist a b) :
    cdist c b = cdist a b - cdist a c := by
  rw [cdist_eq_sub, cdist_eq_sub, cdist_eq_sub] at *
  have h1 : b - c = (b - a) - (c - a) := by abel
  rw [h1]
  exact Fin.coe_sub_iff_le.2 (Fin.le_iff_val_le_val.2 h)

lemma crosses_symm {N : ℕ} [NeZero N] (e f : Sym2 (Fin N)) (h : Crosses e f) : Crosses f e := by
  obtain ⟨a, b, c, d, rfl, rfl, h1, h2, h3⟩ := h
  have h0 : cdist a a = 0 := (cdist_eq_zero a a).2 rfl
  have hac : a ≠ c := by intro h; subst h; omega
  have hd := cdist_lt a d
  refine ⟨c, d, b, a, rfl, Sym2.eq_swap, ?_⟩
  rw [cdist_tri a b c (by omega), cdist_tri a d c (by omega), cdist_swap a c hac]
  omega


lemma cdist_inj {N : ℕ} [NeZero N] (a x y : Fin N) (h : cdist a x = cdist a y) : x = y := by
  rw [cdist_eq_sub, cdist_eq_sub] at h
  exact sub_left_injective (Fin.ext h)

lemma crosses_disjoint {N : ℕ} [NeZero N] (e f : Sym2 (Fin N)) (h : Crosses e f) (x : Fin N)
    (hx : x ∈ e) (hy : x ∈ f) : False := by
  obtain ⟨a, b, c, d, rfl, rfl, h1, h2, h3⟩ := h
  have h0 : cdist a a = 0 := (cdist_eq_zero a a).2 rfl
  rw [Sym2.mem_iff] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> omega


lemma cdist_via {N : ℕ} [NeZero N] (o a x : Fin N) :
    cdist a x = if cdist o a ≤ cdist o x then cdist o x - cdist o a
      else cdist o x + N - cdist o a := by
  rw [cdist_eq_sub, cdist_eq_sub, cdist_eq_sub]
  have h1 : x - a = (x - o) - (a - o) := by abel
  rw [h1]
  split_ifs with h
  · exact Fin.coe_sub_iff_le.2 (Fin.le_iff_val_le_val.2 h)
  · have hlt : x - o < a - o := Fin.lt_iff_val_lt_val.2 (by omega)
    rw [Fin.coe_sub_iff_lt.2 hlt]
    omega

/-- exactly one of `w, z` lies strictly between `u` and `v`, the other is not an endpoint -/
def Inter (u v w z : ℕ) : Prop :=
  ((u < w ∧ w < v ∨ v < w ∧ w < u) ∧ ¬(u < z ∧ z < v ∨ v < z ∧ z < u) ∧ z ≠ u ∧ z ≠ v) ∨
  ((u < z ∧ z < v ∨ v < z ∧ z < u) ∧ ¬(u < w ∧ w < v ∨ v < w ∧ w < u) ∧ w ≠ u ∧ w ≠ v)

lemma crosses_pos {N : ℕ} [NeZero N] (o u v w z : Fin N) :
    Crosses s(u, v) s(w, z) ↔ Inter (cdist o u) (cdist o v) (cdist o w) (cdist o z) := by
  constructor
  · rintro ⟨a, b, c, d, h1, h2, i1, i2, i3⟩
    have la := cdist_lt o a
    have lb := cdist_lt o b
    have lc := cdist_lt o c
    have ld := cdist_lt o d
    have E : Inter (cdist o a) (cdist o b) (cdist o c) (cdist o d) := by
      simp only [cdist_via o a c, cdist_via o a b, cdist_via o a d] at i1 i2 i3
      unfold Inter
      split_ifs at i1 i2 i3 <;> omega
    have sym1 : ∀ p q r t, Inter p q r t → Inter q p r t := by unfold Inter; intros; omega
    have sym2 : ∀ p q r t, Inter p q r t → Inter p q t r := by unfold Inter; intros; omega
    rcases Sym2.eq_iff.1 h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases Sym2.eq_iff.1 h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact E
    · exact sym2 _ _ _ _ E
    · exact sym1 _ _ _ _ E
    · exact sym1 _ _ _ _ (sym2 _ _ _ _ E)
  · have key : ∀ a b c d : Fin N, cdist o a < cdist o c → cdist o c < cdist o b →
        (cdist o b < cdist o d ∨ cdist o d < cdist o a) → Crosses s(a, b) s(c, d) := by
      intro a b c d h1 h2 h3
      refine ⟨a, b, c, d, rfl, rfl, ?_⟩
      have := cdist_lt o d
      have := cdist_lt o b
      rw [cdist_via o a c, cdist_via o a b, cdist_via o a d]
      split_ifs <;> omega
    intro h
    unfold Inter at h
    rcases h with ⟨hw, hz, hzu, hzv⟩ | ⟨hz, hw, hwu, hwv⟩
    · rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact key u v w z h1 h2 (by omega)
      · rw [Sym2.eq_swap]; exact key v u w z h1 h2 (by omega)
    · rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [Sym2.eq_swap (a := w)]; exact key u v z w h1 h2 (by omega)
      · rw [Sym2.eq_swap, Sym2.eq_swap (a := w)]; exact key v u z w h1 h2 (by omega)

/-! ## step A: injectivity of Santos vectors -/

lemma crosses_irrefl {N : ℕ} [NeZero N] (e : Sym2 (Fin N)) : ¬ Crosses e e := by
  intro h
  induction e using Sym2.ind with
  | _ a b => exact crosses_disjoint _ _ h a (Sym2.mem_mk_left _ _) (Sym2.mem_mk_left _ _)


/-! ## Part B: triangulations under dihedral maps, apexes and flips -/

lemma inter_swap {u v w z : ℕ} (h : Inter u v w z) : Inter u v z w := by
  unfold Inter at *; omega

section HL
variable {n : ℕ} (σ : Fin (n - 1) → Bool)

def L1 : List (Fin (n + 3)) := (List.finRange (n + 3)).filter (fun k => !hlSign σ k)
def L2 : List (Fin (n + 3)) := (List.finRange (n + 3)).filter (fun k => hlSign σ k)

lemma hlOrder_eq : hlOrder σ = L1 σ ++ (L2 σ).reverse := rfl

lemma len12 : (L1 σ).length + (L2 σ).length = n + 3 := by
  have h := List.length_eq_length_filter_add (l := List.finRange (n + 3)) (fun k => !hlSign σ k)
  simp only [Bool.not_not, List.length_finRange] at h
  unfold L1 L2; omega

lemma mem_L1 (k : Fin (n + 3)) : k ∈ L1 σ ↔ hlSign σ k = false := by simp [L1]

lemma mem_L2 (k : Fin (n + 3)) : k ∈ L2 σ ↔ hlSign σ k = true := by simp [L2]

lemma L1_sorted : (L1 σ).Pairwise (· < ·) := (List.pairwise_lt_finRange _).filter _

lemma L2_sorted : (L2 σ).Pairwise (· < ·) := (List.pairwise_lt_finRange _).filter _

lemma label_lo (p : Fin (n + 3)) (hp : p.val < (L1 σ).length) :
    hlLabel σ p = (L1 σ)[p.val] := by
  have hl : p.val < (L1 σ ++ (L2 σ).reverse).length := by
    rw [List.length_append, List.length_reverse, len12]; exact p.isLt
  unfold hlLabel
  rw [hlOrder_eq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some,
    List.getElem_append_left hp]

lemma label_hi (p : Fin (n + 3)) (hp : (L1 σ).length ≤ p.val) :
    ∃ i, ∃ hi : i < (L2 σ).length, i = (L2 σ).length - 1 - (p.val - (L1 σ).length) ∧
      hlLabel σ p = (L2 σ)[i] := by
  have h12 := len12 σ
  have hp' := p.isLt
  have hl : p.val < (L1 σ ++ (L2 σ).reverse).length := by
    rw [List.length_append, List.length_reverse, len12]; exact p.isLt
  refine ⟨(L2 σ).length - 1 - (p.val - (L1 σ).length), by omega, rfl, ?_⟩
  unfold hlLabel
  rw [hlOrder_eq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some,
    List.getElem_append_right hp, List.getElem_reverse]

lemma lo_mem (p : Fin (n + 3)) (hp : p.val < (L1 σ).length) : hlLabel σ p ∈ L1 σ := by
  rw [label_lo σ p hp]; simp

lemma hi_mem (p : Fin (n + 3)) (hp : (L1 σ).length ≤ p.val) : hlLabel σ p ∈ L2 σ := by
  obtain ⟨i, hi, -, h⟩ := label_hi σ p hp
  rw [h]; simp

lemma lo_mono (p q : Fin (n + 3)) (hpq : p.val < q.val) (hq : q.val < (L1 σ).length) :
    hlLabel σ p < hlLabel σ q := by
  rw [label_lo σ p (by omega), label_lo σ q hq]
  exact List.pairwise_iff_getElem.1 (L1_sorted σ) _ _ _ _ hpq

lemma hi_anti (p q : Fin (n + 3)) (hp : (L1 σ).length ≤ p.val) (hpq : p.val < q.val) :
    hlLabel σ q < hlLabel σ p := by
  obtain ⟨i, hi, hi', h1⟩ := label_hi σ p hp
  obtain ⟨j, hj, hj', h2⟩ := label_hi σ q (by omega)
  rw [h1, h2]
  have := q.isLt
  have := len12 σ
  exact List.pairwise_iff_getElem.1 (L2_sorted σ) _ _ _ _ (by omega)

lemma signpos_lo (p : Fin (n + 3)) (hp : p.val < (L1 σ).length) : hlSignPos σ p = false :=
  (mem_L1 σ _).1 (lo_mem σ p hp)

lemma signpos_hi (p : Fin (n + 3)) (hp : (L1 σ).length ≤ p.val) : hlSignPos σ p = true :=
  (mem_L2 σ _).1 (hi_mem σ p hp)

lemma exists_pos_lo (k : Fin (n + 3)) (hk : hlSign σ k = false) :
    ∃ p : Fin (n + 3), p.val < (L1 σ).length ∧ hlLabel σ p = k := by
  obtain ⟨i, hi, hik⟩ := List.getElem_of_mem ((mem_L1 σ k).2 hk)
  have := len12 σ
  exact ⟨⟨i, by omega⟩, hi, by rw [label_lo σ _ hi]; exact hik⟩

lemma sign_false_ne (k : Fin (n + 3)) (h : hlSign σ k = false) :
    k.val ≠ 0 ∧ k.val ≠ n + 2 := by
  unfold hlSign at h
  constructor <;> intro hk <;> simp [hk] at h

lemma sign_one : hlSign σ (⟨1, by omega⟩ : Fin (n + 3)) = false := by
  have h1 : ¬ (1 = 0 ∨ 1 = n + 2) := by omega
  have h2 : 1 = 1 ∨ 1 = n + 1 := Or.inl rfl
  unfold hlSign
  exact (if_neg h1).trans (if_pos h2)

lemma sign_n1 : hlSign σ (⟨n + 1, by omega⟩ : Fin (n + 3)) = false := by
  have h1 : ¬ (n + 1 = 0 ∨ n + 1 = n + 2) := by omega
  have h2 : n + 1 = 1 ∨ n + 1 = n + 1 := Or.inr rfl
  unfold hlSign
  exact (if_neg h1).trans (if_pos h2)

lemma lower_S (a b : Fin (n + 3)) (hab : a.val < b.val) (hb : b.val < (L1 σ).length)
    (k : Fin (n + 3)) (hk : k ∈ hlS σ s(a, b)) :
    hlLabel σ a < k ∧ k < hlLabel σ b := by
  have hmono := lo_mono σ a b hab hb
  have Rlow : ∀ k', k' ∈ hlR σ s(a, b) →
      ∃ p : Fin (n + 3), hlLabel σ p = k' ∧ a.val < p.val ∧ p.val < b.val := by
    intro k' hk'
    simp only [hlR, Finset.mem_filter, Finset.mem_univ, true_and] at hk'
    obtain ⟨a', b', he, hl, p, hp, h1, h2⟩ := hk'
    rcases Sym2.eq_iff.1 he with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · rw [← h3] at h1
      rw [← h3, ← h4] at h2
      refine ⟨p, hp, ?_⟩
      rw [cdist_of_le _ _ hab.le] at h2
      by_cases hpa : a.val ≤ p.val
      · rw [cdist_of_le _ _ hpa] at h1 h2; omega
      · rw [cdist_of_gt _ _ (by omega)] at h2; have := b.isLt; omega
    · rw [← h3, ← h4] at hl; exact absurd hl (not_lt.2 hmono.le)
  have hpos : ∀ p : Fin (n + 3), a.val < p.val → p.val < b.val →
      hlLabel σ a < hlLabel σ p ∧ hlLabel σ p < hlLabel σ b ∧ hlSign σ (hlLabel σ p) = false :=
    fun p h1 h2 => ⟨lo_mono σ a p h1 (by omega), lo_mono σ p b h2 hb, signpos_lo σ p (by omega)⟩
  simp only [hlS, Finset.mem_filter, Finset.mem_univ, true_and] at hk
  obtain ⟨a', b', he, hl, H⟩ := hk
  rcases Sym2.eq_iff.1 he with ⟨h3, h4⟩ | ⟨h3, h4⟩
  swap
  · rw [← h3, ← h4] at hl; exact absurd hl (not_lt.2 hmono.le)
  rw [← h3, ← h4] at H
  rcases H with ⟨hkR, -, -⟩ | ⟨-, h0R⟩ | ⟨-, h0R⟩
  · obtain ⟨p, hp, h1, h2⟩ := Rlow k hkR
    rw [← hp]
    exact ⟨(hpos p h1 h2).1, (hpos p h1 h2).2.1⟩
  · obtain ⟨p, hp, h1, h2⟩ := Rlow _ h0R
    have := (hpos p h1 h2).2.2
    rw [hp] at this
    exact absurd rfl (sign_false_ne σ _ this).1
  · obtain ⟨p, hp, h1, h2⟩ := Rlow _ h0R
    have := (hpos p h1 h2).2.2
    rw [hp] at this
    exact absurd rfl (sign_false_ne σ _ this).2

lemma upper_S (a b : Fin (n + 3)) (hab : a.val < b.val) (ha : (L1 σ).length ≤ a.val)
    (k : Fin (n + 3)) (hk : hlSign σ k = false) (hk0 : k.val ≠ 0) (hk2 : k.val ≠ n + 2) :
    k ∈ hlS σ s(a, b) := by
  obtain ⟨p, hp, rfl⟩ := exists_pos_lo σ k hk
  have hanti := hi_anti σ a b ha hab
  have hR : hlLabel σ p ∈ hlR σ s(a, b) := by
    simp only [hlR, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨b, a, Sym2.eq_swap, hanti, p, rfl, ?_, ?_⟩
    · rw [cdist_of_gt _ _ (by omega)]; have := b.isLt; omega
    · rw [cdist_of_gt _ _ (by omega), cdist_of_gt _ _ hab]; omega
  simp only [hlS, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨b, a, Sym2.eq_swap, hanti, Or.inl ⟨hR, hk0, hk2⟩⟩

lemma S_same_lt (a b : Fin (n + 3)) (hab : a.val < b.val)
    (hs : hlSignPos σ a = hlSignPos σ b) :
    (⟨1, by omega⟩ : Fin (n + 3)) ∈ hlS σ s(a, b) ↔
      (⟨n + 1, by omega⟩ : Fin (n + 3)) ∈ hlS σ s(a, b) := by
  by_cases hb : b.val < (L1 σ).length
  · constructor <;> intro h <;> exfalso
    · obtain ⟨h1, -⟩ := lower_S σ a b hab hb _ h
      have h1' : (hlLabel σ a).val < 1 := h1
      have := (sign_false_ne σ _ (signpos_lo σ a (by omega))).1
      omega
    · obtain ⟨-, h2⟩ := lower_S σ a b hab hb _ h
      have h2' : n + 1 < (hlLabel σ b).val := h2
      have := (sign_false_ne σ _ (signpos_lo σ b hb)).2
      have := (hlLabel σ b).isLt
      omega
  · push_neg at hb
    have hsb := signpos_hi σ b hb
    have ha : (L1 σ).length ≤ a.val := by
      by_contra h
      push_neg at h
      have := signpos_lo σ a h
      simp [hs, hsb] at this
    exact ⟨fun _ => upper_S σ a b hab ha _ (sign_n1 σ) (by show n + 1 ≠ 0; omega)
        (by show n + 1 ≠ n + 2; omega),
      fun _ => upper_S σ a b hab ha _ (sign_one σ) (by show 1 ≠ 0; omega)
        (by show 1 ≠ n + 2; omega)⟩

lemma S_same (a b : Fin (n + 3)) (hab : a ≠ b) (hs : hlSignPos σ a = hlSignPos σ b) :
    (⟨1, by omega⟩ : Fin (n + 3)) ∈ hlS σ s(a, b) ↔
      (⟨n + 1, by omega⟩ : Fin (n + 3)) ∈ hlS σ s(a, b) := by
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with h | h
  · exact S_same_lt σ a b h hs
  · rw [Sym2.eq_swap]; exact S_same_lt σ b a h hs.symm

lemma sign_of_S (e : Sym2 (Fin (n + 3))) (j : Fin n)
    (hS : hlS σ e = Finset.univ.filter (fun k : Fin (n + 3) => 1 ≤ k.val ∧ k.val ≤ j.val + 1) ∨
      hlS σ e = Finset.univ.filter (fun k : Fin (n + 3) => j.val + 2 ≤ k.val ∧ k.val ≤ n + 1))
    (a b : Fin (n + 3)) (he : e = s(a, b)) (hab : a ≠ b) :
    hlSignPos σ a ≠ hlSignPos σ b := by
  intro hs
  have key := S_same σ a b hab hs
  have hj := j.isLt
  rcases hS with h | h
  · have h1 : (⟨1, by omega⟩ : Fin (n + 3)) ∈ hlS σ s(a, b) := by
      rw [← he, h]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
    have h2 := key.1 h1
    rw [← he, h] at h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h2
    omega
  · have h1 : (⟨n + 1, by omega⟩ : Fin (n + 3)) ∈ hlS σ s(a, b) := by
      rw [← he, h]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
    have h2 := key.2 h1
    rw [← he, h] at h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h2
    omega


/-! ## HL label / position calculus (new, 78e7c82b) -/

lemma exists_pos_hi (k : Fin (n + 3)) (hk : hlSign σ k = true) :
    ∃ p : Fin (n + 3), (L1 σ).length ≤ p.val ∧ hlLabel σ p = k := by
  obtain ⟨i, hi, hik⟩ := List.getElem_of_mem ((mem_L2 σ k).2 hk)
  have h12 := len12 σ
  obtain ⟨i', hi', hi'', h⟩ := label_hi σ ⟨(L1 σ).length + ((L2 σ).length - 1 - i), by omega⟩
    (by dsimp only; omega)
  refine ⟨⟨(L1 σ).length + ((L2 σ).length - 1 - i), by omega⟩, by dsimp only; omega, ?_⟩
  rw [h, ← hik]
  have : i' = i := by dsimp only at hi''; omega
  subst this; rfl

lemma exists_pos (k : Fin (n + 3)) : ∃ p : Fin (n + 3), hlLabel σ p = k := by
  cases hk : hlSign σ k
  · obtain ⟨p, -, hp⟩ := exists_pos_lo σ k hk; exact ⟨p, hp⟩
  · obtain ⟨p, -, hp⟩ := exists_pos_hi σ k hk; exact ⟨p, hp⟩

lemma pos_lt_iff (p q : Fin (n + 3)) : p.val < q.val ↔
    (hlSignPos σ p = false ∧ hlSignPos σ q = true) ∨
    (hlSignPos σ p = false ∧ hlSignPos σ q = false ∧ hlLabel σ p < hlLabel σ q) ∨
    (hlSignPos σ p = true ∧ hlSignPos σ q = true ∧ hlLabel σ q < hlLabel σ p) := by
  by_cases hp : p.val < (L1 σ).length <;> by_cases hq : q.val < (L1 σ).length
  · rw [signpos_lo σ p hp, signpos_lo σ q hq]
    simp only [Bool.false_eq_true, and_false, false_and, true_and, false_or, or_false]
    constructor
    · intro h; exact lo_mono σ p q h hq
    · intro h
      by_contra h'; push_neg at h'
      rcases h'.lt_or_eq with h'' | h''
      · exact absurd (lo_mono σ q p h'' hp) (not_lt.2 h.le)
      · have : q = p := Fin.ext h''
        subst this; exact absurd h (lt_irrefl _)
  · push_neg at hq
    rw [signpos_lo σ p hp, signpos_hi σ q hq]
    constructor
    · intro _; exact Or.inl ⟨rfl, rfl⟩
    · intro _; omega
  · push_neg at hp
    rw [signpos_hi σ p hp, signpos_lo σ q hq]
    constructor
    · intro h; omega
    · rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h, -⟩) <;> exact absurd h (by simp)
  · push_neg at hp hq
    rw [signpos_hi σ p hp, signpos_hi σ q hq]
    simp only [Bool.true_eq_false, false_and, and_false, true_and, false_or]
    constructor
    · intro h; exact hi_anti σ p q hp h
    · intro h
      by_contra h'; push_neg at h'
      rcases h'.lt_or_eq with h'' | h''
      · exact absurd (hi_anti σ q p hq h'') (not_lt.2 h.le)
      · have : q = p := Fin.ext h''
        subst this; exact absurd h (lt_irrefl _)

lemma label_inj (p q : Fin (n + 3)) (h : hlLabel σ p = hlLabel σ q) : p = q := by
  by_contra hne
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h' | h'
  · have := (pos_lt_iff σ p q).1 h'
    unfold hlSignPos at this; rw [h] at this
    rcases this with ⟨h1, h2⟩ | ⟨-, -, h3⟩ | ⟨-, -, h3⟩
    · rw [h1] at h2; exact absurd h2 (by simp)
    · exact lt_irrefl _ h3
    · exact lt_irrefl _ h3
  · have := (pos_lt_iff σ q p).1 h'
    unfold hlSignPos at this; rw [h] at this
    rcases this with ⟨h1, h2⟩ | ⟨-, -, h3⟩ | ⟨-, -, h3⟩
    · rw [h1] at h2; exact absurd h2 (by simp)
    · exact lt_irrefl _ h3
    · exact lt_irrefl _ h3

/-- membership of a position's label in hlR, as a position arc -/
lemma R_arc (a b p : Fin (n + 3)) (hab : hlLabel σ a < hlLabel σ b) :
    hlLabel σ p ∈ hlR σ s(a, b) ↔ 0 < cdist a p ∧ cdist a p < cdist a b := by
  simp only [hlR, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a', b', he, hl, p', hp', h1, h2⟩
    have := label_inj σ _ _ hp'
    subst this
    rcases Sym2.eq_iff.1 he with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · subst h3; subst h4; exact ⟨h1, h2⟩
    · subst h3; subst h4; exact absurd hab (not_lt.2 hl.le)
  · intro h
    exact ⟨a, b, rfl, hab, p, rfl, h.1, h.2⟩

/-- the R set in label/sign terms -/
lemma R_lab (a b p : Fin (n + 3)) (hab : hlLabel σ a < hlLabel σ b) :
    hlLabel σ p ∈ hlR σ s(a, b) ↔ p ≠ a ∧ p ≠ b ∧
      ((hlSignPos σ p = false ∧ (hlSignPos σ a = true ∨ hlLabel σ a < hlLabel σ p) ∧
          (hlSignPos σ b = true ∨ hlLabel σ p < hlLabel σ b)) ∨
        (hlSignPos σ p = true ∧ ((hlSignPos σ a = true ∧ hlLabel σ p < hlLabel σ a) ∨
          (hlSignPos σ b = true ∧ hlLabel σ b < hlLabel σ p)))) := by
  rw [R_arc σ a b p hab]
  have e1 := pos_lt_iff σ a b
  have e2 := pos_lt_iff σ b a
  have e3 := pos_lt_iff σ a p
  have e4 := pos_lt_iff σ p a
  have e5 := pos_lt_iff σ b p
  have e6 := pos_lt_iff σ p b
  have hab' : a ≠ b := fun h => by rw [h] at hab; exact lt_irrefl _ hab
  have hab'' : a.val ≠ b.val := Fin.val_ne_of_ne hab'
  have hb := b.isLt
  have hp := p.isLt
  have arc : (0 < cdist a p ∧ cdist a p < cdist a b) ↔
      ((a.val < b.val ∧ a.val < p.val ∧ p.val < b.val) ∨
        (b.val < a.val ∧ (a.val < p.val ∨ p.val < b.val))) := by
    by_cases h1 : a.val ≤ p.val <;> by_cases h2 : a.val ≤ b.val
    · rw [cdist_of_le _ _ h1, cdist_of_le _ _ h2]; omega
    · rw [cdist_of_le _ _ h1, cdist_of_gt _ _ (by omega)]; omega
    · rw [cdist_of_gt _ _ (by omega), cdist_of_le _ _ h2]; omega
    · rw [cdist_of_gt _ _ (by omega), cdist_of_gt _ _ (by omega)]; omega
  by_cases hpa : p = a
  · subst hpa; simp only [ne_eq, not_true_eq_false, false_and, iff_false, arc]; omega
  by_cases hpb : p = b
  · subst hpb; simp only [ne_eq, not_true_eq_false, false_and, and_false, iff_false, arc]; omega
  have la : (hlLabel σ p).val ≠ (hlLabel σ a).val := fun h => hpa (label_inj σ _ _ (Fin.ext h))
  have lb : (hlLabel σ p).val ≠ (hlLabel σ b).val := fun h => hpb (label_inj σ _ _ (Fin.ext h))
  have hpa' : p.val ≠ a.val := Fin.val_ne_of_ne hpa
  have hpb' : p.val ≠ b.val := Fin.val_ne_of_ne hpb
  simp only [ne_eq, hpa, hpb, not_false_eq_true, true_and, arc]
  simp only [Fin.lt_iff_val_lt_val] at e1 e2 e3 e4 e5 e6 hab ⊢
  rcases hA : hlSignPos σ a with _ | _ <;> rcases hB : hlSignPos σ b with _ | _ <;>
    rcases hP : hlSignPos σ p with _ | _ <;>
    simp only [hA, hB, hP, Bool.false_eq_true, Bool.true_eq_false, eq_self_iff_true, true_and, and_true,
      false_and, and_false, or_false, false_or, true_or, or_true, not_true_eq_false,
      not_false_eq_true, iff_true, true_iff, iff_false, false_iff] at e1 e2 e3 e4 e5 e6 ⊢ <;> omega

/-- the R set in pure label terms -/
lemma R_lab' (a b k : Fin (n + 3)) (hab : hlLabel σ a < hlLabel σ b) :
    k ∈ hlR σ s(a, b) ↔ k ≠ hlLabel σ a ∧ k ≠ hlLabel σ b ∧
      ((hlSign σ k = false ∧ (hlSign σ (hlLabel σ a) = true ∨ hlLabel σ a < k) ∧
          (hlSign σ (hlLabel σ b) = true ∨ k < hlLabel σ b)) ∨
        (hlSign σ k = true ∧ ((hlSign σ (hlLabel σ a) = true ∧ k < hlLabel σ a) ∨
          (hlSign σ (hlLabel σ b) = true ∧ hlLabel σ b < k)))) := by
  obtain ⟨p, rfl⟩ := exists_pos σ k
  rw [R_lab σ a b p hab]
  unfold hlSignPos
  have e1 : p ≠ a ↔ hlLabel σ p ≠ hlLabel σ a :=
    ⟨fun h h' => h (label_inj σ _ _ h'), fun h h' => h (by rw [h'])⟩
  have e2 : p ≠ b ↔ hlLabel σ p ≠ hlLabel σ b :=
    ⟨fun h h' => h (label_inj σ _ _ h'), fun h h' => h (by rw [h'])⟩
  rw [e1, e2]

lemma hlS_orient (a b k : Fin (n + 3)) (hab : hlLabel σ a < hlLabel σ b) :
    k ∈ hlS σ s(a, b) ↔ ((k ∈ hlR σ s(a, b) ∧ k.val ≠ 0 ∧ k.val ≠ n + 2) ∨
      (k = hlLabel σ a ∧ (⟨0, by omega⟩ : Fin (n + 3)) ∈ hlR σ s(a, b)) ∨
      (k = hlLabel σ b ∧ (⟨n + 2, by omega⟩ : Fin (n + 3)) ∈ hlR σ s(a, b))) := by
  simp only [hlS, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a', b', he, hl, H⟩
    rcases Sym2.eq_iff.1 he with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · subst h3; subst h4; exact H
    · subst h3; subst h4; exact absurd hab (not_lt.2 hl.le)
  · intro H; exact ⟨a, b, rfl, hab, H⟩

lemma sign_zero : hlSign σ (⟨0, by omega⟩ : Fin (n + 3)) = true := by
  unfold hlSign; simp

lemma sign_top : hlSign σ (⟨n + 2, by omega⟩ : Fin (n + 3)) = true := by
  unfold hlSign; simp

/-- Definition 4.1 in closed form: for labels x < y of the endpoints and 1 ≤ k ≤ n+1,
k ∈ S iff (k ≤ x and x upper) or (x < k < y and k lower) or (y ≤ k and y upper). -/
lemma S_mem (a b k : Fin (n + 3)) (hab : hlLabel σ a < hlLabel σ b) :
    k ∈ hlS σ s(a, b) ↔ 1 ≤ k.val ∧ k.val ≤ n + 1 ∧
      ((k.val ≤ (hlLabel σ a).val ∧ hlSign σ (hlLabel σ a) = true) ∨
        ((hlLabel σ a).val < k.val ∧ k.val < (hlLabel σ b).val ∧ hlSign σ k = false) ∨
        ((hlLabel σ b).val ≤ k.val ∧ hlSign σ (hlLabel σ b) = true)) := by
  rw [hlS_orient σ a b k hab, R_lab' σ a b k hab, R_lab' σ a b _ hab, R_lab' σ a b _ hab,
    sign_zero, sign_top]
  have fx : ∀ j : Fin (n + 3), j.val = 0 → hlSign σ j = true := fun j h => by
    have : j = ⟨0, by omega⟩ := Fin.ext h
    rw [this]; exact sign_zero σ
  have ft : ∀ j : Fin (n + 3), j.val = n + 2 → hlSign σ j = true := fun j h => by
    have : j = ⟨n + 2, by omega⟩ := Fin.ext h
    rw [this]; exact sign_top σ
  have x0 := fx (hlLabel σ a)
  have x2 := ft (hlLabel σ a)
  have y0 := fx (hlLabel σ b)
  have y2 := ft (hlLabel σ b)
  have k0 := fx k
  have k2 := ft k
  have kx : k.val = (hlLabel σ a).val → hlSign σ k = hlSign σ (hlLabel σ a) :=
    fun h => by rw [Fin.ext h]
  have ky : k.val = (hlLabel σ b).val → hlSign σ k = hlSign σ (hlLabel σ b) :=
    fun h => by rw [Fin.ext h]
  have hx := (hlLabel σ a).isLt
  have hy := (hlLabel σ b).isLt
  have hk := k.isLt
  simp only [Fin.ext_iff, Fin.lt_def, ne_eq] at hab ⊢
  rcases hX : hlSign σ (hlLabel σ a) with _ | _ <;>
    rcases hY : hlSign σ (hlLabel σ b) with _ | _ <;>
    rcases hK : hlSign σ k with _ | _ <;>
    simp only [hX, hY, hK, Bool.false_eq_true, Bool.true_eq_false, eq_self_iff_true, true_and,
      and_true, false_and, and_false, or_false, false_or, true_or, or_true, not_true_eq_false,
      not_false_eq_true, imp_false, implies_true] at x0 x2 y0 y2 k0 k2 kx ky ⊢ <;> omega

end HL

/-! ## Part B: pure-Nat core for the alternating word -/

/-- label of position `p` for the alternating sign word -/
def LAB (n p : ℕ) : ℕ :=
  if p < (n + 3) / 2 then (if n + 1 ≤ 2 * p + 1 then n + 1 else 2 * p + 1)
  else (if n + 1 ≤ 2 * (n + 2 - p) then n + 2 else 2 * (n + 2 - p))

/-- position of snake vertex `m` (before the rotation by one) -/
def PP (n m : ℕ) : ℕ := if m % 2 = 0 then m / 2 else n + 2 - (m + 1) / 2

def UP (n p : ℕ) : Prop := (n + 3) / 2 ≤ p

def LOW (n k : ℕ) : Prop := ¬ (k = 0 ∨ k = n + 2 ∨ (2 ≤ k ∧ k ≤ n ∧ k % 2 = 0))

def INS (n a b k : ℕ) : Prop :=
  1 ≤ k ∧ k ≤ n + 1 ∧ ((k ≤ LAB n a ∧ UP n a) ∨ (LAB n a < k ∧ k < LAB n b ∧ LOW n k) ∨
    (LAB n b ≤ k ∧ UP n b))

lemma lab_cases (n p : ℕ) :
    (p < (n + 3) / 2 ∧ n + 1 ≤ 2 * p + 1 ∧ LAB n p = n + 1) ∨
    (p < (n + 3) / 2 ∧ 2 * p + 1 < n + 1 ∧ LAB n p = 2 * p + 1) ∨
    ((n + 3) / 2 ≤ p ∧ n + 1 ≤ 2 * (n + 2 - p) ∧ LAB n p = n + 2) ∨
    ((n + 3) / 2 ≤ p ∧ 2 * (n + 2 - p) < n + 1 ∧ LAB n p = 2 * (n + 2 - p)) := by
  unfold LAB; split_ifs <;> omega

lemma pp_cases (n m : ℕ) :
    (m % 2 = 0 ∧ PP n m = m / 2 ∧ PP n (m + 1) = n + 2 - (m + 2) / 2) ∨
    (m % 2 = 1 ∧ PP n m = n + 2 - (m + 1) / 2 ∧ PP n (m + 1) = (m + 1) / 2) := by
  unfold PP; split_ifs <;> omega

lemma lab_cases' (n p : ℕ) (hp : p < n + 3) :
    ((UP n p ↔ False) ∧ n + 1 ≤ 2 * p + 1 ∧ p < (n + 3) / 2 ∧ LAB n p = n + 1) ∨
    ((UP n p ↔ False) ∧ 2 * p + 1 < n + 1 ∧ p < (n + 3) / 2 ∧ LAB n p = 2 * p + 1) ∨
    ((UP n p ↔ True) ∧ (n + 3) / 2 ≤ p ∧ n + 1 ≤ 2 * (n + 2 - p) ∧ LAB n p = n + 2) ∨
    ((UP n p ↔ True) ∧ (n + 3) / 2 ≤ p ∧ 2 * (n + 2 - p) < n + 1 ∧ LAB n p = 2 * (n + 2 - p)) := by
  unfold UP
  rcases lab_cases n p with h | h | h | h
  · exact Or.inl ⟨iff_false_intro (by omega), h.2.1, h.1, h.2.2⟩
  · exact Or.inr (Or.inl ⟨iff_false_intro (by omega), h.2.1, h.1, h.2.2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨iff_true_intro h.1, h.1, h.2.1, h.2.2⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨iff_true_intro h.1, h.1, h.2.1, h.2.2⟩))

lemma pp_cases' (n m : ℕ) (hm : m < n) :
    (m % 2 = 0 ∧ (LOW n (m + 1) ↔ True) ∧ (LOW n (m + 2) ↔ m + 2 = n + 1) ∧
      PP n m = m / 2 ∧ PP n (m + 1) = n + 2 - (m + 2) / 2) ∨
    (m % 2 = 1 ∧ (LOW n (m + 1) ↔ False) ∧ (LOW n (m + 2) ↔ True) ∧
      PP n m = n + 2 - (m + 1) / 2 ∧ PP n (m + 1) = (m + 1) / 2) := by
  rcases pp_cases n m with ⟨h, e1, e2⟩ | ⟨h, e1, e2⟩
  · left
    exact ⟨h, iff_true_intro (by unfold LOW; omega),
      ⟨fun hl => by unfold LOW at hl; omega, fun he => by unfold LOW; omega⟩, e1, e2⟩
  · right
    exact ⟨h, iff_false_intro (by unfold LOW; omega), iff_true_intro (by unfold LOW; omega), e1, e2⟩

def Xc (n a b t u : ℕ) : Prop :=
  (¬ UP n a ∧ ¬ UP n b ∧ a < t ∧ t < b) ∨ (UP n a ∧ UP n b ∧ b < u ∧ u < a) ∨
  (¬ UP n a ∧ UP n b ∧ ((a < t ∧ b < u) ∨ (u < b ∧ t < a))) ∨
  (UP n a ∧ ¬ UP n b ∧ ((b < t ∧ a < u) ∨ (u < a ∧ t < b)))

lemma orient (n a b : ℕ) (ha : a < n + 3) (hb : b < n + 3) (hxy : LAB n a < LAB n b) :
    (UP n a → UP n b → b < a) ∧ (¬ UP n a → ¬ UP n b → a < b) := by
  unfold UP
  rcases lab_cases n a with h1 | h1 | h1 | h1 <;> rcases lab_cases n b with h2 | h2 | h2 | h2 <;> omega

lemma X_all (n a b t u : ℕ) (ha : a < n + 3) (hb : b < n + 3) (hab : a ≠ b)
    (ho : (UP n a → UP n b → b < a) ∧ (¬ UP n a → ¬ UP n b → a < b))
    (ht : t < (n + 3) / 2) (hu : (n + 3) / 2 ≤ u) (hu' : u < n + 3) :
    Inter a b t u ↔ Xc n a b t u := by
  unfold Inter Xc
  unfold UP at ho ⊢
  constructor
  · rintro (⟨hw, hz, h3, h4⟩ | ⟨hz, hw, h3, h4⟩)
    · rcases Nat.lt_or_ge a ((n + 3) / 2) with h1 | h1 <;>
        rcases Nat.lt_or_ge b ((n + 3) / 2) with h2 | h2 <;> omega
    · rcases Nat.lt_or_ge a ((n + 3) / 2) with h1 | h1 <;>
        rcases Nat.lt_or_ge b ((n + 3) / 2) with h2 | h2 <;> omega
  · rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, (⟨h3, h4⟩ | ⟨h3, h4⟩)⟩ |
      ⟨h1, h2, (⟨h3, h4⟩ | ⟨h3, h4⟩)⟩)
    · left; omega
    · right; omega
    · left; omega
    · right; omega
    · left; omega
    · right; omega

lemma inter_comm (u v w z : ℕ) : Inter u v w z ↔ Inter u v z w := by
  unfold Inter; exact Or.comm

lemma ppE (n m : ℕ) (hm : m < n) (h : m % 2 = 0) :
    (LOW n (m + 1) ↔ True) ∧ (LOW n (m + 2) ↔ m + 2 = n + 1) ∧
      PP n m = m / 2 ∧ PP n (m + 1) = n + 2 - (m + 2) / 2 := by
  rcases pp_cases' n m hm with ⟨h0, h1, h2, h3, h4⟩ | ⟨h0, -⟩
  · exact ⟨h1, h2, h3, h4⟩
  · omega

lemma ppO (n m : ℕ) (hm : m < n) (h : m % 2 = 1) :
    (LOW n (m + 1) ↔ False) ∧ (LOW n (m + 2) ↔ True) ∧
      PP n m = n + 2 - (m + 1) / 2 ∧ PP n (m + 1) = (m + 1) / 2 := by
  rcases pp_cases' n m hm with ⟨h0, -⟩ | ⟨h0, h1, h2, h3, h4⟩
  · omega
  · exact ⟨h1, h2, h3, h4⟩

lemma XE (n a b m : ℕ) (ha : a < n + 3) (hb : b < n + 3) (hab : a ≠ b)
    (hxy : LAB n a < LAB n b) (hm : m < n) (h : m % 2 = 0) :
    Inter a b (PP n m) (PP n (m + 1)) ↔ Xc n a b (PP n m) (PP n (m + 1)) := by
  obtain ⟨-, -, e1, e2⟩ := ppE n m hm h
  exact X_all n a b _ _ ha hb hab (orient n a b ha hb hxy) (by omega) (by omega) (by omega)

lemma XO (n a b m : ℕ) (ha : a < n + 3) (hb : b < n + 3) (hab : a ≠ b)
    (hxy : LAB n a < LAB n b) (hm : m < n) (h : m % 2 = 1) :
    Inter a b (PP n m) (PP n (m + 1)) ↔ Xc n a b (PP n (m + 1)) (PP n m) := by
  obtain ⟨-, -, e1, e2⟩ := ppO n m hm h
  rw [inter_comm]
  exact X_all n a b _ _ ha hb hab (orient n a b ha hb hxy) (by omega) (by omega) (by omega)

lemma E1 (n a b m : ℕ) (ha : a < n + 3) (hb : b < n + 3) (hab : a ≠ b)
    (d1 : a + 1 ≠ b) (d2 : b + 1 ≠ a) (d3 : ¬ (a = 0 ∧ b = n + 2)) (d4 : ¬ (b = 0 ∧ a = n + 2))
    (hxy : LAB n a < LAB n b) (hm : m < n) (hpar : m % 2 = 0)
    (hI : Inter a b (PP n m) (PP n (m + 1))) :
    INS n a b (m + 1) := by
  rw [XE n a b m ha hb hab hxy hm hpar] at hI
  obtain ⟨l1, l2, p1, p2⟩ := ppE n m hm hpar
  rcases lab_cases' n a ha with ⟨u1, f1, g1, e1⟩ | ⟨u1, f1, g1, e1⟩ | ⟨u1, f1, g1, e1⟩ | ⟨u1, f1, g1, e1⟩ <;>
  rcases lab_cases' n b hb with ⟨u2, f2, g2, e2⟩ | ⟨u2, f2, g2, e2⟩ | ⟨u2, f2, g2, e2⟩ | ⟨u2, f2, g2, e2⟩ <;>
  (try simp only [INS, Xc, u1, u2, l1, l2, and_true, and_false, true_and, false_and, false_or, or_false, true_or, or_true, not_true, not_false_eq_true] at hI ⊢) <;>
  omega

lemma E2 (n a b m : ℕ) (ha : a < n + 3) (hb : b < n + 3) (hab : a ≠ b)
    (d1 : a + 1 ≠ b) (d2 : b + 1 ≠ a) (d3 : ¬ (a = 0 ∧ b = n + 2)) (d4 : ¬ (b = 0 ∧ a = n + 2))
    (hxy : LAB n a < LAB n b) (hm : m < n) (hpar : m % 2 = 0)
    (hI : Inter a b (PP n m) (PP n (m + 1))) :
    ¬ INS n a b (m + 2) := by
  rw [XE n a b m ha hb hab hxy hm hpar] at hI
  obtain ⟨l1, l2, p1, p2⟩ := ppE n m hm hpar
  rcases lab_cases' n a ha with ⟨u1, f1, g1, e1⟩ | ⟨u1, f1, g1, e1⟩ | ⟨u1, f1, g1, e1⟩ | ⟨u1, f1, g1, e1⟩ <;>
  rcases lab_cases' n b hb with ⟨u2, f2, g2, e2⟩ | ⟨u2, f2, g2, e2⟩ | ⟨u2, f2, g2, e2⟩ | ⟨u2, f2, g2, e2⟩ <;>
  (try simp only [INS, Xc, u1, u2, l1, l2, and_true, and_false, true_and, false_and, false_or, or_false, true_or, or_true, not_true, not_false_eq_true] at hI ⊢) <;>
  omega

lemma E3 (n a b m : ℕ) (ha : a < n + 3) (hb : b < n + 3) (hab : a ≠ b)
    (d1 : a + 1 ≠ b) (d2 : b + 1 ≠ a) (d3 : ¬ (a = 0 ∧ b = n + 2)) (d4 : ¬ (b = 0 ∧ a = n + 2))
    (hxy : LAB n a < LAB n b) (hm : m < n) (hpar : m % 2 = 0)
    (hne : ¬ ((a = PP n m ∧ b = PP n (m + 1)) ∨ (a = PP n (m + 1) ∧ b = PP n m))) (h1 : INS n a b (m + 1)) (h2 : ¬ INS n a b (m + 2)) :
    Inter a b (PP n m) (PP n (m + 1)) := by
  rw [XE n a b m ha hb hab hxy hm hpar] at ⊢
  obtain ⟨l1, l2, p1, p2⟩ := ppE n m hm hpar
  rcases lab_cases' n a ha with ⟨u1, f1, g1, e1⟩ | ⟨u1, f1, g1, e1⟩ | ⟨u1, f1, g1, e1⟩ | ⟨u1, f1, g1, e1⟩ <;>
  rcases lab_cases' n b hb with ⟨u2, f2, g2, e2⟩ | ⟨u2, f2, g2, e2⟩ | ⟨u2, f2, g2, e2⟩ | ⟨u2, f2, g2, e2⟩ <;>
  (try simp only [INS, Xc, u1, u2, l1, l2, and_true, and_false, true_and, false_and, false_or, or_false, true_or, or_true, not_true, not_false_eq_true] at h1 h2 ⊢) <;>
  omega

lemma E4 (n a b m : ℕ) (ha : a < n + 3) (hb : b < n + 3) (hab : a ≠ b)
    (d1 : a + 1 ≠ b) (d2 : b + 1 ≠ a) (d3 : ¬ (a = 0 ∧ b = n + 2)) (d4 : ¬ (b = 0 ∧ a = n + 2))
    (hxy : LAB n a < LAB n b) (hm : m < n) (hpar : m % 2 = 0)
    (hne : ¬ ((a = PP n m ∧ b = PP n (m + 1)) ∨ (a = PP n (m + 1) ∧ b = PP n m))) (h2 : INS n a b (m + 2)) :
    INS n a b (m + 1) := by
  obtain ⟨l1, l2, p1, p2⟩ := ppE n m hm hpar
  rcases lab_cases' n a ha with ⟨u1, f1, g1, e1⟩ | ⟨u1, f1, g1, e1⟩ | ⟨u1, f1, g1, e1⟩ | ⟨u1, f1, g1, e1⟩ <;>
  rcases lab_cases' n b hb with ⟨u2, f2, g2, e2⟩ | ⟨u2, f2, g2, e2⟩ | ⟨u2, f2, g2, e2⟩ | ⟨u2, f2, g2, e2⟩ <;>
  (try simp only [INS, Xc, u1, u2, l1, l2, and_true, and_false, true_and, false_and, false_or, or_false, true_or, or_true, not_true, not_false_eq_true] at h2 ⊢) <;>
  omega

lemma O1 (n a b m : ℕ) (ha : a < n + 3) (hb : b < n + 3) (hab : a ≠ b)
    (d1 : a + 1 ≠ b) (d2 : b + 1 ≠ a) (d3 : ¬ (a = 0 ∧ b = n + 2)) (d4 : ¬ (b = 0 ∧ a = n + 2))
    (hxy : LAB n a < LAB n b) (hm : m < n) (hpar : m % 2 = 1)
    (hI : Inter a b (PP n m) (PP n (m + 1))) :
    INS n a b (m + 2) := by
  rw [XO n a b m ha hb hab hxy hm hpar] at hI
  obtain ⟨l1, l2, p1, p2⟩ := ppO n m hm hpar
  rcases lab_cases' n a ha with ⟨u1, f1, g1, e1⟩ | ⟨u1, f1, g1, e1⟩ | ⟨u1, f1, g1, e1⟩ | ⟨u1, f1, g1, e1⟩ <;>
  rcases lab_cases' n b hb with ⟨u2, f2, g2, e2⟩ | ⟨u2, f2, g2, e2⟩ | ⟨u2, f2, g2, e2⟩ | ⟨u2, f2, g2, e2⟩ <;>
  (try simp only [INS, Xc, u1, u2, l1, l2, and_true, and_false, true_and, false_and, false_or, or_false, true_or, or_true, not_true, not_false_eq_true] at hI ⊢) <;>
  omega

lemma O2 (n a b m : ℕ) (ha : a < n + 3) (hb : b < n + 3) (hab : a ≠ b)
    (d1 : a + 1 ≠ b) (d2 : b + 1 ≠ a) (d3 : ¬ (a = 0 ∧ b = n + 2)) (d4 : ¬ (b = 0 ∧ a = n + 2))
    (hxy : LAB n a < LAB n b) (hm : m < n) (hpar : m % 2 = 1)
    (hI : Inter a b (PP n m) (PP n (m + 1))) :
    ¬ INS n a b (m + 1) := by
  rw [XO n a b m ha hb hab hxy hm hpar] at hI
  obtain ⟨l1, l2, p1, p2⟩ := ppO n m hm hpar
  rcases lab_cases' n a ha with ⟨u1, f1, g1, e1⟩ | ⟨u1, f1, g1, e1⟩ | ⟨u1, f1, g1, e1⟩ | ⟨u1, f1, g1, e1⟩ <;>
  rcases lab_cases' n b hb with ⟨u2, f2, g2, e2⟩ | ⟨u2, f2, g2, e2⟩ | ⟨u2, f2, g2, e2⟩ | ⟨u2, f2, g2, e2⟩ <;>
  (try simp only [INS, Xc, u1, u2, l1, l2, and_true, and_false, true_and, false_and, false_or, or_false, true_or, or_true, not_true, not_false_eq_true] at hI ⊢) <;>
  omega

lemma O3 (n a b m : ℕ) (ha : a < n + 3) (hb : b < n + 3) (hab : a ≠ b)
    (d1 : a + 1 ≠ b) (d2 : b + 1 ≠ a) (d3 : ¬ (a = 0 ∧ b = n + 2)) (d4 : ¬ (b = 0 ∧ a = n + 2))
    (hxy : LAB n a < LAB n b) (hm : m < n) (hpar : m % 2 = 1)
    (hne : ¬ ((a = PP n m ∧ b = PP n (m + 1)) ∨ (a = PP n (m + 1) ∧ b = PP n m))) (h1 : INS n a b (m + 2)) (h2 : ¬ INS n a b (m + 1)) :
    Inter a b (PP n m) (PP n (m + 1)) := by
  rw [XO n a b m ha hb hab hxy hm hpar] at ⊢
  obtain ⟨l1, l2, p1, p2⟩ := ppO n m hm hpar
  rcases lab_cases' n a ha with ⟨u1, f1, g1, e1⟩ | ⟨u1, f1, g1, e1⟩ | ⟨u1, f1, g1, e1⟩ | ⟨u1, f1, g1, e1⟩ <;>
  rcases lab_cases' n b hb with ⟨u2, f2, g2, e2⟩ | ⟨u2, f2, g2, e2⟩ | ⟨u2, f2, g2, e2⟩ | ⟨u2, f2, g2, e2⟩ <;>
  (try simp only [INS, Xc, u1, u2, l1, l2, and_true, and_false, true_and, false_and, false_or, or_false, true_or, or_true, not_true, not_false_eq_true] at h1 h2 ⊢) <;>
  omega

lemma O4 (n a b m : ℕ) (ha : a < n + 3) (hb : b < n + 3) (hab : a ≠ b)
    (d1 : a + 1 ≠ b) (d2 : b + 1 ≠ a) (d3 : ¬ (a = 0 ∧ b = n + 2)) (d4 : ¬ (b = 0 ∧ a = n + 2))
    (hxy : LAB n a < LAB n b) (hm : m < n) (hpar : m % 2 = 1)
    (hne : ¬ ((a = PP n m ∧ b = PP n (m + 1)) ∨ (a = PP n (m + 1) ∧ b = PP n m))) (h2 : INS n a b (m + 1)) :
    INS n a b (m + 2) := by
  obtain ⟨l1, l2, p1, p2⟩ := ppO n m hm hpar
  rcases lab_cases' n a ha with ⟨u1, f1, g1, e1⟩ | ⟨u1, f1, g1, e1⟩ | ⟨u1, f1, g1, e1⟩ | ⟨u1, f1, g1, e1⟩ <;>
  rcases lab_cases' n b hb with ⟨u2, f2, g2, e2⟩ | ⟨u2, f2, g2, e2⟩ | ⟨u2, f2, g2, e2⟩ | ⟨u2, f2, g2, e2⟩ <;>
  (try simp only [INS, Xc, u1, u2, l1, l2, and_true, and_false, true_and, false_and, false_or, or_false, true_or, or_true, not_true, not_false_eq_true] at h2 ⊢) <;>
  omega

lemma CE1 (n a b m : ℕ) (ha : a < n + 3) (hb : b < n + 3) (hab : a ≠ b)
    (d1 : a + 1 ≠ b) (d2 : b + 1 ≠ a) (d3 : ¬ (a = 0 ∧ b = n + 2)) (d4 : ¬ (b = 0 ∧ a = n + 2))
    (hxy : LAB n a < LAB n b) (hm : m < n) (hpar : m % 2 = 0)
    (hc : (a = PP n m ∧ b = PP n (m + 1)) ∨ (a = PP n (m + 1) ∧ b = PP n m)) :
    ¬ INS n a b (m + 1) := by
  obtain ⟨l1, l2, p1, p2⟩ := ppE n m hm hpar
  rcases lab_cases' n a ha with ⟨u1, f1, g1, e1⟩ | ⟨u1, f1, g1, e1⟩ | ⟨u1, f1, g1, e1⟩ | ⟨u1, f1, g1, e1⟩ <;>
  rcases lab_cases' n b hb with ⟨u2, f2, g2, e2⟩ | ⟨u2, f2, g2, e2⟩ | ⟨u2, f2, g2, e2⟩ | ⟨u2, f2, g2, e2⟩ <;>
  (try simp only [INS, Xc, u1, u2, l1, l2, and_true, and_false, true_and, false_and, false_or, or_false, true_or, or_true, not_true, not_false_eq_true] at ⊢) <;>
  omega

lemma CE2 (n a b m : ℕ) (ha : a < n + 3) (hb : b < n + 3) (hab : a ≠ b)
    (d1 : a + 1 ≠ b) (d2 : b + 1 ≠ a) (d3 : ¬ (a = 0 ∧ b = n + 2)) (d4 : ¬ (b = 0 ∧ a = n + 2))
    (hxy : LAB n a < LAB n b) (hm : m < n) (hpar : m % 2 = 0)
    (hc : (a = PP n m ∧ b = PP n (m + 1)) ∨ (a = PP n (m + 1) ∧ b = PP n m)) :
    INS n a b (m + 2) := by
  obtain ⟨l1, l2, p1, p2⟩ := ppE n m hm hpar
  rcases lab_cases' n a ha with ⟨u1, f1, g1, e1⟩ | ⟨u1, f1, g1, e1⟩ | ⟨u1, f1, g1, e1⟩ | ⟨u1, f1, g1, e1⟩ <;>
  rcases lab_cases' n b hb with ⟨u2, f2, g2, e2⟩ | ⟨u2, f2, g2, e2⟩ | ⟨u2, f2, g2, e2⟩ | ⟨u2, f2, g2, e2⟩ <;>
  (try simp only [INS, Xc, u1, u2, l1, l2, and_true, and_false, true_and, false_and, false_or, or_false, true_or, or_true, not_true, not_false_eq_true] at ⊢) <;>
  omega

lemma CO1 (n a b m : ℕ) (ha : a < n + 3) (hb : b < n + 3) (hab : a ≠ b)
    (d1 : a + 1 ≠ b) (d2 : b + 1 ≠ a) (d3 : ¬ (a = 0 ∧ b = n + 2)) (d4 : ¬ (b = 0 ∧ a = n + 2))
    (hxy : LAB n a < LAB n b) (hm : m < n) (hpar : m % 2 = 1)
    (hc : (a = PP n m ∧ b = PP n (m + 1)) ∨ (a = PP n (m + 1) ∧ b = PP n m)) :
    INS n a b (m + 1) := by
  obtain ⟨l1, l2, p1, p2⟩ := ppO n m hm hpar
  rcases lab_cases' n a ha with ⟨u1, f1, g1, e1⟩ | ⟨u1, f1, g1, e1⟩ | ⟨u1, f1, g1, e1⟩ | ⟨u1, f1, g1, e1⟩ <;>
  rcases lab_cases' n b hb with ⟨u2, f2, g2, e2⟩ | ⟨u2, f2, g2, e2⟩ | ⟨u2, f2, g2, e2⟩ | ⟨u2, f2, g2, e2⟩ <;>
  (try simp only [INS, Xc, u1, u2, l1, l2, and_true, and_false, true_and, false_and, false_or, or_false, true_or, or_true, not_true, not_false_eq_true] at ⊢) <;>
  omega

lemma CO2 (n a b m : ℕ) (ha : a < n + 3) (hb : b < n + 3) (hab : a ≠ b)
    (d1 : a + 1 ≠ b) (d2 : b + 1 ≠ a) (d3 : ¬ (a = 0 ∧ b = n + 2)) (d4 : ¬ (b = 0 ∧ a = n + 2))
    (hxy : LAB n a < LAB n b) (hm : m < n) (hpar : m % 2 = 1)
    (hc : (a = PP n m ∧ b = PP n (m + 1)) ∨ (a = PP n (m + 1) ∧ b = PP n m)) :
    ¬ INS n a b (m + 2) := by
  obtain ⟨l1, l2, p1, p2⟩ := ppO n m hm hpar
  rcases lab_cases' n a ha with ⟨u1, f1, g1, e1⟩ | ⟨u1, f1, g1, e1⟩ | ⟨u1, f1, g1, e1⟩ | ⟨u1, f1, g1, e1⟩ <;>
  rcases lab_cases' n b hb with ⟨u2, f2, g2, e2⟩ | ⟨u2, f2, g2, e2⟩ | ⟨u2, f2, g2, e2⟩ | ⟨u2, f2, g2, e2⟩ <;>
  (try simp only [INS, Xc, u1, u2, l1, l2, and_true, and_false, true_and, false_and, false_or, or_false, true_or, or_true, not_true, not_false_eq_true] at ⊢) <;>
  omega

lemma pp_lt (n m : ℕ) (hm : m ≤ n) : PP n m < n + 3 := by
  unfold PP; split_ifs <;> omega

lemma nc (n a b m m' : ℕ) (hm : m < n) (hm' : m' < n) (h : m ≠ m')
    (hab : (a = PP n m' ∧ b = PP n (m' + 1)) ∨ (a = PP n (m' + 1) ∧ b = PP n m')) :
    ¬ Inter a b (PP n m) (PP n (m + 1)) := by
  unfold Inter
  rcases pp_cases n m with h3 | h3 <;> rcases pp_cases n m' with h4 | h4 <;> omega

lemma pinj (n m m' : ℕ) (hm : m < n) (hm' : m' < n)
    (h : (PP n m = PP n m' ∧ PP n (m + 1) = PP n (m' + 1)) ∨
      (PP n m = PP n (m' + 1) ∧ PP n (m + 1) = PP n m')) : m = m' := by
  rcases pp_cases n m with h3 | h3 <;> rcases pp_cases n m' with h4 | h4 <;> omega


/-! ## Part C: the alternating sign word, explicit labels -/

section Alt
variable {n : ℕ}

lemma sgn_alt (k : Fin (n + 3)) : hlSign (altSigma n) k = false ↔ LOW n k.val := by
  unfold hlSign LOW
  by_cases h1 : k.val = 0 ∨ k.val = n + 2
  · rw [if_pos h1]; simp only [Bool.true_eq_false, false_iff, not_not]; omega
  · rw [if_neg h1]
    by_cases h2 : k.val = 1 ∨ k.val = n + 1
    · rw [if_pos h2]; simp only [true_iff]; omega
    · rw [if_neg h2]
      by_cases h3 : k.val - 2 < n - 1
      · rw [dif_pos h3]; simp only [altSigma, decide_eq_false_iff_not]; omega
      · rw [dif_neg h3]; simp only [true_iff]; omega

lemma lenL1 : (L1 (altSigma n)).length ≤ n + 3 := by
  have := len12 (altSigma n); omega

lemma low_lo (p : Fin (n + 3)) (hp : p.val < (L1 (altSigma n)).length) :
    LOW n (hlLabel (altSigma n) p).val :=
  (sgn_alt _).1 (signpos_lo (altSigma n) p hp)

lemma up_hi (p : Fin (n + 3)) (hp : (L1 (altSigma n)).length ≤ p.val) :
    ¬ LOW n (hlLabel (altSigma n) p).val := by
  rw [← sgn_alt]
  have := signpos_hi (altSigma n) p hp
  unfold hlSignPos at this
  rw [this]; decide

def fLo (n p : ℕ) : ℕ := if n + 1 ≤ 2 * p + 1 then n + 1 else 2 * p + 1

def gUp (n i : ℕ) : ℕ := if n + 1 ≤ 2 * i then n + 2 else 2 * i

lemma lower_step (p : ℕ) (hp : p < (L1 (altSigma n)).length) :
    (hlLabel (altSigma n) ⟨p, by have := lenL1 (n := n); omega⟩).val = fLo n p ∧
      2 * p ≤ n + 1 := by
  have hA := lenL1 (n := n)
  induction p with
  | zero =>
    obtain ⟨r, hr, hlr⟩ := exists_pos_lo (altSigma n) ⟨1, by omega⟩ (sign_one _)
    have h0 := low_lo (n := n) ⟨0, by omega⟩ hp
    rcases Nat.eq_zero_or_pos r.val with hr0 | hr0
    · have : r = ⟨0, by omega⟩ := Fin.ext hr0
      rw [this] at hlr
      rw [hlr]; unfold fLo; split_ifs <;> simp <;> omega
    · exfalso
      have := lo_mono (altSigma n) ⟨0, by omega⟩ r hr0 hr
      rw [hlr, Fin.lt_def] at this
      unfold LOW at h0; simp only at this; omega
  | succ p ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hlt := lo_mono (altSigma n) ⟨p, by omega⟩ ⟨p + 1, by omega⟩ (by simp) hp
    rw [Fin.lt_def] at hlt
    have hlow := low_lo (n := n) ⟨p + 1, by omega⟩ hp
    have hb := (hlLabel (altSigma n) ⟨p + 1, by omega⟩).isLt
    unfold LOW at hlow
    have hmax : 2 * p + 1 < n + 1 := by
      by_contra hc
      unfold fLo at ih1; rw [if_pos (by omega)] at ih1
      omega
    have ef : fLo n p = 2 * p + 1 := by unfold fLo; rw [if_neg (by omega)]
    rw [ef] at ih1
    have hk : fLo n (p + 1) < n + 3 := by unfold fLo; split_ifs <;> omega
    have hlow' : LOW n (fLo n (p + 1)) := by
      unfold fLo; split_ifs with hh
      · unfold LOW; omega
      · unfold LOW; omega
    have hks := (sgn_alt (n := n) ⟨fLo n (p + 1), hk⟩).2 hlow'
    obtain ⟨r, hr, hlr⟩ := exists_pos_lo (altSigma n) _ hks
    refine ⟨?_, by omega⟩
    rcases lt_trichotomy r.val (p + 1) with h | h | h
    · exfalso
      rcases Nat.lt_or_ge r.val p with h' | h'
      · have := lo_mono (altSigma n) r ⟨p, by omega⟩ h' (by simp only; omega)
        rw [hlr, Fin.lt_def] at this
        simp only at this
        unfold fLo at this; split_ifs at this <;> omega
      · have : r = ⟨p, by omega⟩ := Fin.ext (by simp only; omega)
        rw [this] at hlr
        rw [hlr] at ih1; simp only at ih1
        unfold fLo at ih1; split_ifs at ih1 <;> omega
    · have : r = ⟨p + 1, by omega⟩ := Fin.ext h
      rw [this] at hlr; rw [hlr]
    · exfalso
      have := lo_mono (altSigma n) ⟨p + 1, by omega⟩ r h hr
      rw [hlr, Fin.lt_def] at this
      simp only at this
      unfold fLo at this; split_ifs at this <;> omega

lemma lower_fin (p : Fin (n + 3)) (hp : p.val < (L1 (altSigma n)).length) :
    (hlLabel (altSigma n) p).val = fLo n p.val ∧ 2 * p.val ≤ n + 1 :=
  lower_step p.val hp

lemma upper_step (i : ℕ) (hi : i ≤ n + 2) (hA : (L1 (altSigma n)).length ≤ n + 2 - i) :
    (hlLabel (altSigma n) ⟨n + 2 - i, by omega⟩).val = gUp n i ∧ 2 * i ≤ n + 3 := by
  induction i with
  | zero =>
    obtain ⟨r, hr, hlr⟩ := exists_pos_hi (altSigma n) ⟨0, by omega⟩ (sign_zero _)
    have hrl := r.isLt
    rcases Nat.lt_or_ge r.val (n + 2) with h | h
    · exfalso
      have := hi_anti (altSigma n) r ⟨n + 2, by omega⟩ hr (by simp only; omega)
      rw [hlr, Fin.lt_def] at this; simp at this
    · have : r = ⟨n + 2 - 0, by omega⟩ := Fin.ext (by simp only; omega)
      rw [this] at hlr; rw [hlr]; unfold gUp; simp
  | succ i ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega) (by omega)
    have hlt := hi_anti (altSigma n) ⟨n + 2 - (i + 1), by omega⟩ ⟨n + 2 - i, by omega⟩ hA
      (by simp only; omega)
    rw [Fin.lt_def] at hlt
    have hup := up_hi (n := n) ⟨n + 2 - (i + 1), by omega⟩ hA
    have hb := (hlLabel (altSigma n) ⟨n + 2 - (i + 1), by omega⟩).isLt
    unfold LOW at hup
    have hmax : 2 * i < n + 1 := by
      by_contra hc
      unfold gUp at ih1; rw [if_pos (by omega)] at ih1
      omega
    have eg : gUp n i = 2 * i := by unfold gUp; rw [if_neg (by omega)]
    rw [eg] at ih1
    have hk : gUp n (i + 1) < n + 3 := by unfold gUp; split_ifs <;> omega
    have hks : hlSign (altSigma n) ⟨gUp n (i + 1), hk⟩ = true := by
      cases h : hlSign (altSigma n) ⟨gUp n (i + 1), hk⟩
      · exfalso; rw [sgn_alt] at h; unfold LOW gUp at h; simp only at h
        split_ifs at h <;> omega
      · rfl
    obtain ⟨r, hr, hlr⟩ := exists_pos_hi (altSigma n) _ hks
    refine ⟨?_, by omega⟩
    have hrl := r.isLt
    rcases lt_trichotomy r.val (n + 2 - (i + 1)) with h | h | h
    · exfalso
      have := hi_anti (altSigma n) r ⟨n + 2 - (i + 1), by omega⟩ hr h
      rw [hlr, Fin.lt_def] at this; simp only at this
      unfold gUp at this; split_ifs at this <;> omega
    · have : r = ⟨n + 2 - (i + 1), by omega⟩ := Fin.ext h
      rw [this] at hlr; rw [hlr]
    · exfalso
      rcases Nat.lt_or_ge (n + 2 - i) r.val with h' | h'
      · have := hi_anti (altSigma n) ⟨n + 2 - i, by omega⟩ r (by simp only; omega) h'
        rw [hlr, Fin.lt_def] at this; simp only at this
        unfold gUp at this; split_ifs at this <;> omega
      · have : r = ⟨n + 2 - i, by omega⟩ := Fin.ext (by simp only; omega)
        rw [this] at hlr; rw [hlr] at ih1; simp only at ih1
        unfold gUp at ih1; split_ifs at ih1 <;> omega

lemma A_eq : (L1 (altSigma n)).length = (n + 3) / 2 := by
  have hA := lenL1 (n := n)
  obtain ⟨r, hr, hlr⟩ := exists_pos_lo (altSigma n) ⟨n + 1, by omega⟩ (sign_n1 _)
  obtain ⟨h1a, h1b⟩ := lower_fin r hr
  rw [hlr] at h1a; simp only at h1a
  have h2 := (lower_step (n := n) ((L1 (altSigma n)).length - 1) (by omega)).2
  unfold fLo at h1a; split_ifs at h1a <;> omega

lemma upper_fin (p : Fin (n + 3)) (hp : (L1 (altSigma n)).length ≤ p.val) :
    (hlLabel (altSigma n) p).val = gUp n (n + 2 - p.val) := by
  have hpl := p.isLt
  have := (upper_step (n := n) (n + 2 - p.val) (by omega) (by omega)).1
  have e : (⟨n + 2 - (n + 2 - p.val), by omega⟩ : Fin (n + 3)) = p := Fin.ext (by simp only; omega)
  rw [e] at this; exact this

lemma lab_eq (p : Fin (n + 3)) : (hlLabel (altSigma n) p).val = LAB n p.val := by
  have hA := A_eq (n := n)
  unfold LAB
  by_cases hp : p.val < (n + 3) / 2
  · rw [if_pos hp, (lower_fin p (by omega)).1]; rfl
  · rw [if_neg hp, upper_fin p (by omega)]; rfl

lemma up_iff (p : Fin (n + 3)) :
    hlSign (altSigma n) (hlLabel (altSigma n) p) = true ↔ UP n p.val := by
  have hA := A_eq (n := n)
  unfold UP
  by_cases hp : p.val < (L1 (altSigma n)).length
  · have := signpos_lo (altSigma n) p hp; unfold hlSignPos at this; rw [this]; simp; omega
  · have := signpos_hi (altSigma n) p (by omega); unfold hlSignPos at this; rw [this]; simp; omega

lemma S_iff (a b k : Fin (n + 3)) (hab : hlLabel (altSigma n) a < hlLabel (altSigma n) b) :
    k ∈ hlS (altSigma n) s(a, b) ↔ INS n a.val b.val k.val := by
  rw [S_mem (altSigma n) a b k hab, up_iff, up_iff, sgn_alt, lab_eq, lab_eq]
  exact Iff.rfl

end Alt

/-! ## Part D: the linear map -/

noncomputable def ext0 {n : ℕ} (x : Fin n → ℝ) (j : ℕ) : ℝ := if h : j < n then x ⟨j, h⟩ else 0

noncomputable def Mlin (n : ℕ) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun x := fun m => (if m.val % 2 = 0 then (1 : ℝ) else -1) * (x m - ext0 x (m.val + 1))
  map_add' x y := by
    funext m; simp only [ext0, Pi.add_apply]; split_ifs <;> ring
  map_smul' c x := by
    funext m; simp only [ext0, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

lemma Mlin_inj (n : ℕ) : Function.Injective (Mlin n) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have key : ∀ d j, n - j = d → ext0 x j = 0 := by
    intro d
    induction d with
    | zero => intro j hj; unfold ext0; rw [dif_neg (by omega)]
    | succ d ih =>
      intro j hj
      have hjn : j < n := by omega
      have h1 := congrFun hx ⟨j, hjn⟩
      have h2 := ih (j + 1) (by omega)
      simp only [Mlin, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at h1
      rw [h2] at h1
      unfold ext0
      rw [dif_pos hjn]
      split_ifs at h1 <;> linarith
  funext m
  have := key (n - m.val) m.val rfl
  unfold ext0 at this; rw [dif_pos m.isLt] at this; exact this

noncomputable def Meq (n : ℕ) : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
  LinearEquiv.ofInjectiveEndo (Mlin n) (Mlin_inj n)

lemma Mlin_apply_of {n : ℕ} (F : ℕ → ℝ) (x : Fin n → ℝ)
    (hx : ∀ k : Fin n, x k = F (k.val + 1) - F (n + 1)) (m : Fin n) :
    Mlin n x m = (if m.val % 2 = 0 then (1 : ℝ) else -1) * (F (m.val + 1) - F (m.val + 2)) := by
  simp only [Mlin, LinearMap.coe_mk, AddHom.coe_mk, ext0]
  congr 1
  split_ifs with h
  · rw [hx, hx]; simp only [Fin.val_mk]; ring_nf
  · rw [hx]; have : m.val + 2 = n + 1 := by omega
    rw [this]; ring

lemma ite_iff (p q : Prop) [Decidable p] [Decidable q] (h : p ↔ q) :
    (if p then (1 : ℝ) else 0) = (if q then 1 else 0) := by
  by_cases hp : p
  · rw [if_pos hp, if_pos (h.1 hp)]
  · rw [if_neg hp, if_neg (fun hq => hp (h.2 hq))]

open Classical in
lemma Mvec {n : ℕ} (a b : Fin (n + 3)) (hab : hlLabel (altSigma n) a < hlLabel (altSigma n) b)
    (m : Fin n) :
    Mlin n (hlVec (altSigma n) s(a, b)) m = (if m.val % 2 = 0 then (1 : ℝ) else -1) *
      ((if INS n a.val b.val (m.val + 1) then 1 else 0) -
        (if INS n a.val b.val (m.val + 2) then 1 else 0)) := by
  refine Mlin_apply_of (fun j => if INS n a.val b.val j then 1 else 0) _ ?_ m
  intro k
  unfold hlVec
  rw [ite_iff _ _ (S_iff a b ⟨k.val + 1, by omega⟩ hab), ite_iff _ _ (S_iff a b ⟨n + 1, by omega⟩ hab)]

/-! ## Part E: the snake as a rotated chain -/

def cc (n : ℕ) (m : Fin n) : Sym2 (Fin (n + 3)) :=
  s(⟨PP n m.val, pp_lt n m.val (by omega)⟩, ⟨PP n (m.val + 1), pp_lt n (m.val + 1) (by omega)⟩)

def rot (n : ℕ) : Sym2 (Fin (n + 3)) → Sym2 (Fin (n + 3)) := Sym2.map (dihedral 1 false)

lemma dih1_val {n : ℕ} (x : Fin (n + 3)) : (dihedral 1 false x).val = (1 + x.val) % (n + 3) := by
  simp [dihedral, Fin.val_add]

lemma snakePt_eq {n : ℕ} (m : ℕ) (hm : m ≤ n) :
    snakePt n m = dihedral 1 false ⟨PP n m, pp_lt n m hm⟩ := by
  apply Fin.ext
  rw [dih1_val]
  unfold snakePt PP
  rcases Nat.mod_two_eq_zero_or_one m with h | h
  · simp only [h, if_true]
  · simp only [h, if_false, one_ne_zero]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

lemma rot_inj {n : ℕ} : Function.Injective (rot n) :=
  Sym2.map.injective (dihedral_injective 1 false)

lemma chord_eq {n : ℕ} (m : Fin n) :
    s(snakePt n m.val, snakePt n (m.val + 1)) = rot n (cc n m) := by
  rw [snakePt_eq m.val (by omega), snakePt_eq (m.val + 1) (by omega)]
  rfl

lemma cc_mem {n : ℕ} (m : Fin n) : rot n (cc n m) ∈ snake n := by
  unfold snake; rw [Finset.mem_image]
  exact ⟨m.val, Finset.mem_range.2 m.isLt, chord_eq m⟩

lemma cc_inj {n : ℕ} : Function.Injective (cc n) := by
  intro m m' h
  unfold cc at h
  rw [Sym2.eq_iff] at h
  apply Fin.ext
  apply pinj n m.val m'.val m.isLt m'.isLt
  simp only [Fin.ext_iff] at h
  exact h

noncomputable def iota (n : ℕ) : Fin n ≃ {d // d ∈ snake n} :=
  Equiv.ofBijective (fun m => ⟨rot n (cc n m), cc_mem m⟩)
    ⟨fun x y h => cc_inj (rot_inj (congrArg Subtype.val h)), fun d => by
      obtain ⟨m, hm, hd⟩ := Finset.mem_image.1 d.2
      refine ⟨⟨m, Finset.mem_range.1 hm⟩, Subtype.ext ?_⟩
      rw [← hd]
      exact (chord_eq ⟨m, Finset.mem_range.1 hm⟩).symm⟩

lemma cdist0 {n : ℕ} (x : Fin (n + 3)) : cdist 0 x = x.val := by
  rw [cdist_of_le 0 x (by simp)]; simp

lemma cross_nat {n : ℕ} (a b c d : Fin (n + 3)) :
    Crosses s(a, b) s(c, d) ↔ Inter a.val b.val c.val d.val := by
  rw [crosses_pos 0 a b c d]; simp only [cdist0]

lemma diag_nat {n : ℕ} (a b : Fin (n + 3)) (he : IsDiagonal s(a, b)) :
    a.val ≠ b.val ∧ a.val + 1 ≠ b.val ∧ b.val + 1 ≠ a.val ∧ ¬ (a.val = 0 ∧ b.val = n + 2) ∧
      ¬ (b.val = 0 ∧ a.val = n + 2) := by
  obtain ⟨h1, h2, h3⟩ := he a b rfl
  have ha := a.isLt
  have hb := b.isLt
  have h1' : a.val ≠ b.val := fun h => h1 (Fin.ext h)
  rcases lt_or_gt_of_ne h1' with h | h
  · rw [cdist_of_le a b h.le] at h2; rw [cdist_of_gt b a h] at h3; omega
  · rw [cdist_of_gt a b h] at h2; rw [cdist_of_le b a h.le] at h3; omega

open Classical in
lemma key {n : ℕ} (a b : Fin (n + 3)) (he : IsDiagonal s(a, b))
    (hab : hlLabel (altSigma n) a < hlLabel (altSigma n) b) (m : Fin n) :
    santosVec (snake n) (rot n s(a, b)) (iota n m) = Mlin n (hlVec (altSigma n) s(a, b)) m := by
  rw [Mvec a b hab m]
  obtain ⟨d0, d1, d2, d3, d4⟩ := diag_nat a b he
  have ha := a.isLt
  have hb := b.isLt
  have hm := m.isLt
  have hxy : LAB n a.val < LAB n b.val := by
    rw [← lab_eq, ← lab_eq]; exact hab
  have hiota : (iota n m).1 = rot n (cc n m) := rfl
  unfold santosVec
  rw [hiota]
  by_cases hc : s(a, b) = cc n m
  · have hcn : (a.val = PP n m.val ∧ b.val = PP n (m.val + 1)) ∨
        (a.val = PP n (m.val + 1) ∧ b.val = PP n m.val) := by
      unfold cc at hc; rw [Sym2.eq_iff] at hc; simp only [Fin.ext_iff] at hc; exact hc
    rw [if_pos (by rw [hc]; exact cc_mem m), if_pos (by rw [hc])]
    rcases Nat.mod_two_eq_zero_or_one m.val with hp | hp
    · rw [if_pos hp, if_neg (CE1 n a.val b.val m.val ha hb d0 d1 d2 d3 d4 hxy hm hp hcn),
        if_pos (CE2 n a.val b.val m.val ha hb d0 d1 d2 d3 d4 hxy hm hp hcn)]
      norm_num
    · rw [if_neg (by omega), if_pos (CO1 n a.val b.val m.val ha hb d0 d1 d2 d3 d4 hxy hm hp hcn),
        if_neg (CO2 n a.val b.val m.val ha hb d0 d1 d2 d3 d4 hxy hm hp hcn)]
      norm_num
  · have hne : ¬ ((a.val = PP n m.val ∧ b.val = PP n (m.val + 1)) ∨
        (a.val = PP n (m.val + 1) ∧ b.val = PP n m.val)) := by
      intro h; apply hc; unfold cc; rw [Sym2.eq_iff]; simp only [Fin.ext_iff]; exact h
    have hrhs : (if m.val % 2 = 0 then (1 : ℝ) else -1) *
        ((if INS n a.val b.val (m.val + 1) then 1 else 0) -
          (if INS n a.val b.val (m.val + 2) then 1 else 0)) =
        if Inter a.val b.val (PP n m.val) (PP n (m.val + 1)) then 1 else 0 := by
      rcases Nat.mod_two_eq_zero_or_one m.val with hp | hp
      · rw [if_pos hp]
        by_cases hI : Inter a.val b.val (PP n m.val) (PP n (m.val + 1))
        · rw [if_pos hI, if_pos (E1 n a.val b.val m.val ha hb d0 d1 d2 d3 d4 hxy hm hp hI),
            if_neg (E2 n a.val b.val m.val ha hb d0 d1 d2 d3 d4 hxy hm hp hI)]
          norm_num
        · rw [if_neg hI]
          by_cases h1 : INS n a.val b.val (m.val + 1)
          · have h2 : INS n a.val b.val (m.val + 2) := by
              by_contra h2
              exact hI (E3 n a.val b.val m.val ha hb d0 d1 d2 d3 d4 hxy hm hp hne h1 h2)
            rw [if_pos h1, if_pos h2]; norm_num
          · have h2 : ¬ INS n a.val b.val (m.val + 2) := fun h2 =>
              h1 (E4 n a.val b.val m.val ha hb d0 d1 d2 d3 d4 hxy hm hp hne h2)
            rw [if_neg h1, if_neg h2]; norm_num
      · rw [if_neg (by omega)]
        by_cases hI : Inter a.val b.val (PP n m.val) (PP n (m.val + 1))
        · rw [if_pos hI, if_pos (O1 n a.val b.val m.val ha hb d0 d1 d2 d3 d4 hxy hm hp hI),
            if_neg (O2 n a.val b.val m.val ha hb d0 d1 d2 d3 d4 hxy hm hp hI)]
          norm_num
        · rw [if_neg hI]
          by_cases h1 : INS n a.val b.val (m.val + 2)
          · have h2 : INS n a.val b.val (m.val + 1) := by
              by_contra h2
              exact hI (O3 n a.val b.val m.val ha hb d0 d1 d2 d3 d4 hxy hm hp hne h1 h2)
            rw [if_pos h1, if_pos h2]; norm_num
          · have h2 : ¬ INS n a.val b.val (m.val + 1) := fun h2 =>
              h1 (O4 n a.val b.val m.val ha hb d0 d1 d2 d3 d4 hxy hm hp hne h2)
            rw [if_neg h1, if_neg h2]; norm_num
    rw [hrhs]
    have hcr : Crosses (rot n s(a, b)) (rot n (cc n m)) ↔
        Inter a.val b.val (PP n m.val) (PP n (m.val + 1)) := by
      unfold rot; rw [crosses_dihedral_iff]; unfold cc; exact cross_nat _ _ _ _
    by_cases hs : rot n s(a, b) ∈ snake n
    · rw [if_pos hs, if_neg (fun h => hc (rot_inj h))]
      obtain ⟨m', hm'⟩ := (iota n).surjective ⟨_, hs⟩
      have hm'2 : cc n m' = s(a, b) := rot_inj (congrArg Subtype.val hm')
      have hmm : m.val ≠ m'.val := by
        intro h; apply hc; rw [← hm'2]; congr 1; exact Fin.ext h.symm
      have hcn : (a.val = PP n m'.val ∧ b.val = PP n (m'.val + 1)) ∨
          (a.val = PP n (m'.val + 1) ∧ b.val = PP n m'.val) := by
        unfold cc at hm'2; rw [Sym2.eq_iff] at hm'2; simp only [Fin.ext_iff] at hm'2
        rcases hm'2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1.symm, h2.symm⟩
        · exact Or.inr ⟨h2.symm, h1.symm⟩
      rw [if_neg (nc n a.val b.val m.val m'.val hm m'.isLt hmm hcn)]
    · rw [if_neg hs]
      exact ite_iff _ _ hcr

lemma hLe {n : ℕ} (e : Sym2 (Fin (n + 3))) (he : IsDiagonal e) :
    (LinearEquiv.funCongrLeft ℝ ℝ (iota n).symm) (Meq n (hlVec (altSigma n) e)) =
      santosVec (snake n) (rot n e) := by
  funext d
  obtain ⟨m, rfl⟩ := (iota n).surjective d
  simp only [LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, Equiv.symm_apply_apply,
    Meq, LinearEquiv.coe_ofInjectiveEndo]
  revert he
  refine Sym2.ind (fun a b he => ?_) e
  have hne : a ≠ b := (he a b rfl).1
  have hl : hlLabel (altSigma n) a ≠ hlLabel (altSigma n) b :=
    fun h => hne (label_inj (altSigma n) a b h)
  rcases lt_or_gt_of_ne hl with h | h
  · exact (key a b he h m).symm
  · have he' : IsDiagonal s(b, a) := by rw [Sym2.eq_swap]; exact he
    have := (key b a he' h m).symm
    rw [Sym2.eq_swap] at this
    exact this

end Phl

open AssocRealizations.TypesMeet ChvatalArtGallery.FanPartition in
theorem solution (n : ℕ) :
    NormallyIsomorphic (hlFan (altSigma n)) (santosFan (snake n)) := by
  refine ⟨(Phl.Meq n).trans (LinearEquiv.funCongrLeft ℝ ℝ (Phl.iota n).symm), ?_⟩
  rintro C ⟨D, hD1, hD2, rfl⟩
  refine ⟨D.image (Phl.rot n), ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.1 he
    exact Phl.diagonal_dihedral 1 false e' (hD1 e' he')
  · intro e he f hf
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.1 he
    obtain ⟨f', hf', rfl⟩ := Finset.mem_image.1 hf
    unfold Phl.rot
    rw [Phl.crosses_dihedral_iff]
    exact hD2 e' he' f' hf'
  · have : (((Phl.Meq n).trans (LinearEquiv.funCongrLeft ℝ ℝ (Phl.iota n).symm)).toLinearMap.restrictScalars
        {c : ℝ // 0 ≤ c}) '' (hlVec (altSigma n) '' (↑D : Set _)) =
        santosVec (snake n) '' (↑(D.image (Phl.rot n)) : Set _) := by
      rw [Finset.coe_image, Set.image_image, Set.image_image]
      apply Set.image_congr
      intro e he
      exact Phl.hLe e (hD1 e he)
    rw [PointedCone.hull, PointedCone.hull, ← this,
      Submodule.span_image (((Phl.Meq n).trans
        (LinearEquiv.funCongrLeft ℝ ℝ (Phl.iota n).symm)).toLinearMap.restrictScalars
          {c : ℝ // 0 ≤ c}), Submodule.map_coe]
    rfl
