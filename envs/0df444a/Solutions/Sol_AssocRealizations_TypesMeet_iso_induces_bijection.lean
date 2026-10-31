-- Prove2me | solution 1 for AssocRealizations.TypesMeet.iso_induces_bijection
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-30T12:02:35.018779+00:00
-- url     : https://prove2.me/submissions/810f4ba0-7f1d-45d6-babd-49c6f22d7467

import Mathlib
import Definitions.Def_AssocRealizations_TypesMeet_Setting

set_option autoImplicit false

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


/-! ## copied from 0e6c5404 (santos side, cones, counting) -/
lemma cdist_succ {N : ℕ} [NeZero N] (hN : 2 ≤ N) (a x : Fin N) :
    cdist a (x + 1) = if cdist a x + 1 = N then 0 else cdist a x + 1 := by
  rw [cdist_eq_sub, cdist_eq_sub, show x + 1 - a = (x - a) + 1 by abel, Fin.val_add,
    Fin.val_one', Nat.mod_eq_of_lt (show 1 < N by omega)]
  have := (x - a).isLt
  split_ifs with h
  · rw [h, Nat.mod_self]
  · rw [Nat.mod_eq_of_lt (by omega)]

lemma cdist_pred {N : ℕ} [NeZero N] (hN : 2 ≤ N) (a x : Fin N) :
    cdist a (x - 1) = if cdist a x = 0 then N - 1 else cdist a x - 1 := by
  have h := cdist_succ hN a (x - 1)
  rw [sub_add_cancel] at h
  have := cdist_lt a (x - 1)
  split_ifs at h ⊢ <;> omega


lemma santos_entries {N : ℕ} (T : Finset (Sym2 (Fin N))) (e : Sym2 (Fin N)) (x : {d // d ∈ T}) :
    santosVec T e x = -1 ∨ santosVec T e x = 0 ∨ santosVec T e x = 1 := by
  unfold santosVec
  split_ifs <;> simp

lemma santos_ne_zero {N : ℕ} (T : Finset (Sym2 (Fin N))) (hT : IsTriangulation N T)
    (e : Sym2 (Fin N)) (he : IsDiagonal e) : santosVec T e ≠ 0 := by
  intro h0
  by_cases heT : e ∈ T
  · have := congrFun h0 ⟨e, heT⟩
    simp [santosVec, heT] at this
  · obtain ⟨d, hd, hcr⟩ : ∃ d ∈ T, Crosses e d := by
      by_contra hno
      push_neg at hno
      exact heT (hT.2.2.2 e he hno)
    have := congrFun h0 ⟨d, hd⟩
    simp [santosVec, heT, hcr] at this

lemma posparallel_eq {ι : Type*} (v w : ι → ℝ)
    (hv : ∀ i, v i = -1 ∨ v i = 0 ∨ v i = 1) (hw : ∀ i, w i = -1 ∨ w i = 0 ∨ w i = 1)
    (hw0 : w ≠ 0) (c : ℝ) (hc : 0 < c) (h : v = c • w) : v = w := by
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra hno
    push_neg at hno
    exact hw0 (funext hno)
  have hvi : v i = c * w i := by rw [h]; rfl
  have hc1 : c = 1 := by
    rcases hw i with h1 | h1 | h1
    · rw [h1] at hvi; rcases hv i with h2 | h2 | h2 <;> rw [h2] at hvi <;> linarith
    · exact absurd h1 hi
    · rw [h1] at hvi; rcases hv i with h2 | h2 | h2 <;> rw [h2] at hvi <;> linarith
  rw [h, hc1, one_smul]

/-! ## crossing in positions relative to any base point -/

lemma tri_at {N : ℕ} [NeZero N] (hN : 5 ≤ N) (T : Finset (Sym2 (Fin N)))
    (hT : IsTriangulation N T) (a b : Fin N) (he : IsDiagonal s(a, b)) (heT : s(a, b) ∉ T) :
    ∃ p q : Fin N, 0 < cdist a p ∧ cdist a p < cdist a b ∧ cdist a b < cdist a q ∧
      s(p, q) ∈ T ∧ (cdist a p = 1 ∨ s(a, p) ∈ T) ∧ (cdist a q = N - 1 ∨ s(a, q) ∈ T) := by
  have hab := he a b rfl
  have hk := cdist_lt a b
  have hk0 : cdist a b ≠ 0 := fun h => hab.1 ((cdist_eq_zero a b).1 h)
  have hk2 : cdist b a = N - cdist a b := cdist_swap a b hab.1
  have hk1 := hab.2.1
  have hk3 := hab.2.2
  have h00 : cdist a a = 0 := (cdist_eq_zero a a).2 rfl
  have c1 : cdist a (a + 1) = 1 := by
    rw [cdist_add_self, Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  have cm : cdist a (a - 1) = N - 1 := by
    rw [cdist_pred (by omega), h00]; simp
  let Sp := Finset.univ.filter (fun x : Fin N =>
    0 < cdist a x ∧ cdist a x < cdist a b ∧ (cdist a x = 1 ∨ s(a, x) ∈ T))
  let Sq := Finset.univ.filter (fun x : Fin N =>
    cdist a b < cdist a x ∧ (cdist a x = N - 1 ∨ s(a, x) ∈ T))
  have hp1 : a + 1 ∈ Sp := by
    simp only [Sp, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [c1]; exact ⟨by omega, by omega, Or.inl rfl⟩
  have hq1 : a - 1 ∈ Sq := by
    simp only [Sq, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [cm]; exact ⟨by omega, Or.inl rfl⟩
  obtain ⟨p, hp, hpmax⟩ := Finset.exists_max_image Sp (cdist a) ⟨_, hp1⟩
  obtain ⟨q, hq, hqmin⟩ := Finset.exists_min_image Sq (cdist a) ⟨_, hq1⟩
  simp only [Sp, Sq, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq hpmax hqmin
  have hpl := cdist_lt a p
  have hql := cdist_lt a q
  have hpq_diag : IsDiagonal s(p, q) := by
    intro u v huv
    have e1 : cdist p q = cdist a q - cdist a p := by
      rw [cdist_via a p q]; split_ifs <;> omega
    have e2 : cdist q p = cdist a p + N - cdist a q := by
      rw [cdist_via a q p]; split_ifs <;> omega
    have hne : p ≠ q := by rintro rfl; omega
    rcases Sym2.eq_iff.1 huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hne, by omega, by omega⟩
    · exact ⟨fun h => hne h.symm, by omega, by omega⟩
  refine ⟨p, q, hp.1, hp.2.1, hq.1, ?_, hp.2.2, hq.2⟩
  apply hT.2.2.2 _ hpq_diag
  intro d hd hcr
  induction d using Sym2.ind with
  | _ u w =>
  rw [crosses_pos a] at hcr
  have hul := cdist_lt a u
  have hwl := cdist_lt a w
  have key : ∀ x : Fin N, s(a, x) ∈ T → cdist a p < cdist a x → cdist a x < cdist a q → False := by
    intro x hx h1 h2
    rcases lt_trichotomy (cdist a x) (cdist a b) with h3 | h3 | h3
    · have := hpmax x ⟨by omega, h3, Or.inr hx⟩; omega
    · have := cdist_inj a x b h3; rw [this] at hx; exact heT hx
    · have := hqmin x ⟨h3, Or.inr hx⟩; omega
  have nc : ∀ x : Fin N, s(a, x) ∈ T → ¬ Crosses s(a, x) s(u, w) :=
    fun x hx h => hT.2.2.1 _ hx _ hd h
  have ncp : ¬ Inter 0 (cdist a p) (cdist a u) (cdist a w) := by
    intro hI
    rcases hp.2.2 with h | h
    · unfold Inter at hI; omega
    · apply nc p h; rw [crosses_pos a, h00]; exact hI
  have ncq : ¬ Inter 0 (cdist a q) (cdist a u) (cdist a w) := by
    intro hI
    rcases hq.2 with h | h
    · unfold Inter at hI; omega
    · apply nc q h; rw [crosses_pos a, h00]; exact hI
  by_cases hu0 : cdist a u = 0
  · have hua : u = a := ((cdist_eq_zero a u).1 hu0).symm
    rw [hua] at hd
    unfold Inter at hcr
    exact key w hd (by omega) (by omega)
  by_cases hw0 : cdist a w = 0
  · have hwa : w = a := ((cdist_eq_zero a w).1 hw0).symm
    rw [hwa, Sym2.eq_swap] at hd
    unfold Inter at hcr
    exact key u hd (by omega) (by omega)
  unfold Inter at hcr ncp ncq
  omega

lemma santos_inj_aux {N : ℕ} [NeZero N] (hN : 5 ≤ N) (T : Finset (Sym2 (Fin N)))
    (hT : IsTriangulation N T) (a b : Fin N) (he : IsDiagonal s(a, b)) (heT : s(a, b) ∉ T)
    (f : Sym2 (Fin N)) (hfT : f ∉ T) (ha : a ∉ f)
    (hv : santosVec T s(a, b) = santosVec T f) : False := by
  obtain ⟨p, q, h1, h2, h3, hpqT, hpT, hqT⟩ := tri_at hN T hT a b he heT
  have h00 : cdist a a = 0 := (cdist_eq_zero a a).2 rfl
  have hpl := cdist_lt a p
  have hql := cdist_lt a q
  have hbl := cdist_lt a b
  have hc : Crosses s(a, b) s(p, q) := by
    rw [crosses_pos a, h00]; unfold Inter; omega
  have hv1 := congrFun hv ⟨s(p, q), hpqT⟩
  simp only [santosVec, heT, hfT, hc, if_false, if_true] at hv1
  have hfc : Crosses f s(p, q) := by
    by_contra h; rw [if_neg h] at hv1; norm_num at hv1
  induction f using Sym2.ind with
  | _ u w =>
  have hua : u ≠ a := fun h => ha (h ▸ Sym2.mem_mk_left _ _)
  have hwa : w ≠ a := fun h => ha (h ▸ Sym2.mem_mk_right _ _)
  have hu0 : cdist a u ≠ 0 := fun h => hua ((cdist_eq_zero a u).1 h).symm
  have hw0 : cdist a w ≠ 0 := fun h => hwa ((cdist_eq_zero a w).1 h).symm
  rw [crosses_pos a] at hfc
  have hul := cdist_lt a u
  have hwl := cdist_lt a w
  have ne : ∀ x, s(a, x) ∈ T → Crosses s(u, w) s(a, x) → False := by
    intro x hx hcx
    have hv2 := congrFun hv ⟨s(a, x), hx⟩
    have : ¬ Crosses s(a, b) s(a, x) := fun h =>
      crosses_disjoint _ _ h a (Sym2.mem_mk_left _ _) (Sym2.mem_mk_left _ _)
    simp only [santosVec, heT, hfT, this, hcx, if_false, if_true] at hv2
    norm_num at hv2
  have np : ¬ Inter (cdist a u) (cdist a w) 0 (cdist a p) := by
    intro hI
    rcases hpT with h | h
    · unfold Inter at hI; omega
    · exact ne p h (by rw [crosses_pos a, h00]; exact hI)
  have nq : ¬ Inter (cdist a u) (cdist a w) 0 (cdist a q) := by
    intro hI
    rcases hqT with h | h
    · unfold Inter at hI; omega
    · exact ne q h (by rw [crosses_pos a, h00]; exact hI)
  unfold Inter at hfc np nq
  omega

lemma santos_inj {N : ℕ} [NeZero N] (hN : 5 ≤ N) (T : Finset (Sym2 (Fin N)))
    (hT : IsTriangulation N T) (e f : Sym2 (Fin N)) (he : IsDiagonal e) (hf : IsDiagonal f)
    (hv : santosVec T e = santosVec T f) : e = f := by
  by_contra hne
  by_cases heT : e ∈ T <;> by_cases hfT : f ∈ T
  · have := congrFun hv ⟨e, heT⟩
    simp [santosVec, heT, hfT, Ne.symm hne] at this
  · have := congrFun hv ⟨e, heT⟩
    simp [santosVec, heT, hfT] at this <;> split_ifs at this <;> norm_num at this
  · have := congrFun hv ⟨f, hfT⟩
    simp [santosVec, heT, hfT] at this <;> split_ifs at this <;> norm_num at this
  · induction e using Sym2.ind with
    | _ a b =>
    by_cases ha : a ∈ f
    · by_cases hb : b ∈ f
      · exact hne ((Sym2.mem_and_mem_iff (he a b rfl).1).1 ⟨ha, hb⟩).symm
      · exact santos_inj_aux hN T hT b a (by rw [Sym2.eq_swap]; exact he)
          (by rw [Sym2.eq_swap]; exact heT) f hfT hb (by rw [Sym2.eq_swap]; exact hv)
    · exact santos_inj_aux hN T hT a b he heT f hfT ha hv


lemma ray_pick {α W : Type*} [AddCommGroup W] [Module ℝ W] (g : α → W) (D : Set α) (w : W)
    (hw : w ≠ 0) (hg : ∀ d ∈ D, g d ≠ 0)
    (h : (PointedCone.hull ℝ {w} : Set W) = PointedCone.hull ℝ (g '' D)) :
    ∃ d ∈ D, ∃ t : ℝ, 0 < t ∧ w = t • g d := by
  have hwm : w ∈ PointedCone.hull ℝ (g '' D) := by
    rw [← SetLike.mem_coe, ← h]; exact PointedCone.subset_hull (Set.mem_singleton w)
  obtain ⟨d, hd⟩ : D.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    subst hne
    simp at hwm
    exact hw hwm
  have hgd : g d ∈ PointedCone.hull ℝ {w} := by
    rw [← SetLike.mem_coe, h]; exact PointedCone.subset_hull (Set.mem_image_of_mem g hd)
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hgd
  have ha' : (a : ℝ) • w = g d := ha
  have hapos : 0 < (a : ℝ) := by
    rcases (a.2).lt_or_eq with h' | h'
    · exact h'
    · exfalso; apply hg d hd; rw [← ha', ← h', zero_smul]
  refine ⟨d, hd, (a : ℝ)⁻¹, inv_pos.2 hapos, ?_⟩
  rw [← ha', smul_smul, inv_mul_cancel₀ hapos.ne', one_smul]

lemma cone2_pick {α W : Type*} [AddCommGroup W] [Module ℝ W] (g : α → W) (D : Set α)
    (x y : W) (hx : x ≠ 0) (hind : ∀ l : ℝ, y ≠ l • x)
    (h : (PointedCone.hull ℝ {x, y} : Set W) = PointedCone.hull ℝ (g '' D)) :
    ∃ d ∈ D, ∃ t : ℝ, 0 < t ∧ g d = t • x := by
  have hxm : x ∈ PointedCone.hull ℝ (g '' D) := by
    rw [← SetLike.mem_coe, ← h]; exact PointedCone.subset_hull (Set.mem_insert x _)
  have hgen : ∀ d ∈ D, ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ g d = a • x + b • y := by
    intro d hd
    have : g d ∈ PointedCone.hull ℝ {x, y} := by
      rw [← SetLike.mem_coe, h]; exact PointedCone.subset_hull (Set.mem_image_of_mem g hd)
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.1 this
    exact ⟨a, b, a.2, b.2, hab.symm⟩
  choose! a b ha hb hab using hgen
  obtain ⟨t, ht, c, hc⟩ := (Submodule.mem_span_image_iff_exists_fun _).1 hxm
  have hsum : (∑ i : t, (c i : ℝ) * a i) • x + (∑ i : t, (c i : ℝ) * b i) • y = x := by
    conv_rhs => rw [← hc]
    rw [Finset.sum_smul, Finset.sum_smul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hab i (ht i.2), ← Nonneg.coe_smul, smul_add, smul_smul, smul_smul]
  set A := ∑ i : t, (c i : ℝ) * a i with hAdef
  set B := ∑ i : t, (c i : ℝ) * b i with hBdef
  have hB : B = 0 := by
    by_contra hB
    apply hind ((1 - A) / B)
    have h1 : B • y = (1 - A) • x := by
      rw [sub_smul, one_smul, eq_sub_iff_add_eq, add_comm]; exact hsum
    rw [div_eq_mul_inv, mul_comm, ← smul_smul, ← h1, smul_smul, inv_mul_cancel₀ hB, one_smul]
  have hA : A = 1 := by
    have h1 : (1 - A) • x = 0 := by
      rw [sub_smul, one_smul]; nth_rewrite 1 [← hsum]; rw [hB, zero_smul, add_zero, sub_self]
    rcases smul_eq_zero.1 h1 with h2 | h2
    · linarith
    · exact absurd h2 hx
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (show A ≠ 0 by rw [hA]; norm_num)
  have hbi : (c i : ℝ) * b i = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (c j).2 (hb j (ht j.2)))).1 hB i
      (Finset.mem_univ _)
  have hci : (c i : ℝ) ≠ 0 := left_ne_zero_of_mul hi
  have hai : a i ≠ 0 := right_ne_zero_of_mul hi
  have hbi' : b i = 0 := (mul_eq_zero.1 hbi).resolve_left hci
  refine ⟨i.1, ht i.2, a i, lt_of_le_of_ne (ha i (ht i.2)) (Ne.symm hai), ?_⟩
  rw [hab i (ht i.2), hbi', zero_smul, add_zero]

/-! ## step A: the ray map -/


lemma fin_surj {α : Type*} [Fintype α] (P : α → Prop) (φ : α → α)
    (hP : ∀ x, P x → P (φ x)) (hinj : ∀ x y, P x → P y → φ x = φ y → x = y) :
    ∀ y, P y → ∃ x, P x ∧ φ x = y := by
  classical
  let s := Finset.univ.filter P
  have hsub : s.image φ ⊆ s := by
    intro y hy
    simp only [s, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    obtain ⟨x, hx, rfl⟩ := hy
    exact hP x hx
  have hcard : (s.image φ).card = s.card :=
    Finset.card_image_of_injOn (fun x hx y hy hxy =>
      hinj x y (by simpa [s] using hx) (by simpa [s] using hy) hxy)
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard])
  intro y hy
  have : y ∈ s.image φ := by rw [heq]; simpa [s] using hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 this
  exact ⟨x, by simpa [s] using hx, rfl⟩


/-! ## abstract label combinatorics (78e7c82b session 2) -/

def Sm (N1 : ℕ) (g : ℕ → Prop) (x y k : ℕ) : Prop :=
  1 ≤ k ∧ k ≤ N1 ∧ ((k ≤ x ∧ g x) ∨ (x < k ∧ k < y ∧ ¬ g k) ∨ (y ≤ k ∧ g y))

def LD (N1 : ℕ) (g : ℕ → Prop) (x y : ℕ) : Prop :=
  x < y ∧ y ≤ N1 + 1 ∧
  ((¬ g x ∨ x = 0) → (¬ g y ∨ y = N1 + 1) → ∃ k, x < k ∧ k < y ∧ ¬ g k) ∧
  (g x → g y → ∃ k, x < k ∧ k < y ∧ g k)

section Abs
variable {N1 : ℕ} {g : ℕ → Prop}

lemma Sm_ne {x y : ℕ} (h : LD N1 g x y) : ∃ k, Sm N1 g x y k := by
  obtain ⟨hxy, hy, hl, -⟩ := h
  by_cases A : g x ∧ 1 ≤ x
  · exact ⟨x, A.2, by omega, Or.inl ⟨le_rfl, A.1⟩⟩
  by_cases B : g y ∧ y ≤ N1
  · exact ⟨y, by omega, B.2, Or.inr (Or.inr ⟨le_rfl, B.1⟩)⟩
  have hx : ¬ g x ∨ x = 0 := by
    by_cases h : g x
    · right; by_contra h'; exact A ⟨h, by omega⟩
    · left; exact h
  have hy' : ¬ g y ∨ y = N1 + 1 := by
    by_cases h : g y
    · right; by_contra h'; exact B ⟨h, by omega⟩
    · left; exact h
  obtain ⟨k, h1, h2, h3⟩ := hl hx hy'
  exact ⟨k, by omega, by omega, Or.inr (Or.inl ⟨h1, h2, h3⟩)⟩

lemma Sm_nf (g0 : g 0) (gt : g (N1 + 1)) {x y : ℕ} (h : LD N1 g x y) :
    ∃ k, 1 ≤ k ∧ k ≤ N1 ∧ ¬ Sm N1 g x y k := by
  obtain ⟨hxy, hy, -, hu⟩ := h
  by_cases A : g x
  · by_cases B : g y
    · obtain ⟨k, h1, h2, h3⟩ := hu A B
      refine ⟨k, by omega, by omega, ?_⟩
      rintro ⟨-, -, ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨h, -⟩⟩
      · omega
      · exact h h3
      · omega
    · have hy0 : y ≠ N1 + 1 := fun h => B (h ▸ gt)
      refine ⟨y, by omega, by omega, ?_⟩
      rintro ⟨-, -, ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, h⟩⟩
      · omega
      · omega
      · exact B h
  · have hx0 : x ≠ 0 := fun h => A (h ▸ g0)
    refine ⟨x, by omega, by omega, ?_⟩
    rintro ⟨-, -, ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩⟩
    · exact A h
    · omega
    · omega

lemma Sm_one (g0 : g 0) (g1 : ¬ g 1) (hN1 : 1 ≤ N1) {x y : ℕ} (h : LD N1 g x y) :
    Sm N1 g x y 1 ↔ g x := by
  obtain ⟨hxy, hy, hl, -⟩ := h
  constructor
  · rintro ⟨-, -, ⟨-, h⟩ | ⟨h1, -, -⟩ | ⟨h1, h2⟩⟩
    · exact h
    · have : x = 0 := by omega
      exact this ▸ g0
    · have : y = 1 := by omega
      exact absurd (this ▸ h2) g1
  · intro hx
    by_cases hx1 : 1 ≤ x
    · exact ⟨le_rfl, hN1, Or.inl ⟨hx1, hx⟩⟩
    · have hx0 : x = 0 := by omega
      have hy1 : y ≠ 1 := by
        intro hy1
        obtain ⟨k, h1, h2, -⟩ := hl (Or.inr hx0) (Or.inl (hy1 ▸ g1))
        omega
      exact ⟨le_rfl, hN1, Or.inr (Or.inl ⟨by omega, by omega, g1⟩)⟩

lemma Sm_top (gt : g (N1 + 1)) (gN : ¬ g N1) (hN1 : 1 ≤ N1) {x y : ℕ} (h : LD N1 g x y) :
    Sm N1 g x y N1 ↔ g y := by
  obtain ⟨hxy, hy, hl, -⟩ := h
  constructor
  · rintro ⟨-, -, ⟨h1, h2⟩ | ⟨-, h1, -⟩ | ⟨-, h⟩⟩
    · have : x = N1 := by omega
      exact absurd (this ▸ h2) gN
    · have : y = N1 + 1 := by omega
      exact this ▸ gt
    · exact h
  · intro hgy
    by_cases hyN : y ≤ N1
    · exact ⟨hN1, le_rfl, Or.inr (Or.inr ⟨hyN, hgy⟩)⟩
    · have hyt : y = N1 + 1 := by omega
      have hxN : x ≠ N1 := by
        intro hx
        obtain ⟨k, h1, h2, -⟩ := hl (Or.inl (hx ▸ gN)) (Or.inr hyt)
        omega
      exact ⟨hN1, le_rfl, Or.inr (Or.inl ⟨by omega, by omega, gN⟩)⟩

lemma inj_x (g0 : g 0) {x y x' y' : ℕ} (hL : LD N1 g x y) (hL' : LD N1 g x' y')
    (hS : ∀ k, Sm N1 g x y k ↔ Sm N1 g x' y' k) (hgx : g x ↔ g x') (hgy : g y ↔ g y') :
    ¬ x < x' := by
  intro hlt
  obtain ⟨hxy, hy, hl, hu⟩ := hL
  obtain ⟨hxy', hy', hl', hu'⟩ := hL'
  by_cases hx' : g x'
  · have m1 : Sm N1 g x' y' x' := ⟨by omega, by omega, Or.inl ⟨le_rfl, hx'⟩⟩
    rcases (hS x').2 m1 with ⟨-, -, ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨hyx, hgy'⟩⟩
    · omega
    · exact h hx'
    · obtain ⟨u, hu1, hu2, hu3⟩ := hu (hgx.2 hx') hgy'
      have : Sm N1 g x' y' u := ⟨by omega, by omega, Or.inl ⟨by omega, hx'⟩⟩
      rcases (hS u).2 this with ⟨-, -, ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨h, -⟩⟩
      · omega
      · exact h hu3
      · omega
  · have hx0 : x' ≠ 0 := fun h => hx' (h ▸ g0)
    have n1 : ¬ Sm N1 g x' y' x' := by
      rintro ⟨-, -, ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩⟩
      · exact hx' h
      · omega
      · omega
    by_cases hyx : x' < y
    · exact n1 ((hS x').1 ⟨by omega, by omega, Or.inr (Or.inl ⟨hlt, hyx, hx'⟩)⟩)
    · by_cases hgy' : g y
      · exact n1 ((hS x').1 ⟨by omega, by omega, Or.inr (Or.inr ⟨by omega, hgy'⟩)⟩)
      · obtain ⟨w, hw1, hw2, hw3⟩ := hl' (Or.inl hx') (Or.inl (fun h => hgy' (hgy.2 h)))
        have : Sm N1 g x' y' w := ⟨by omega, by omega, Or.inr (Or.inl ⟨hw1, hw2, hw3⟩)⟩
        rcases (hS w).2 this with ⟨-, -, ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, h⟩⟩
        · omega
        · omega
        · exact hgy' h

lemma inj_y (gt : g (N1 + 1)) {x y y' : ℕ} (hL : LD N1 g x y) (hL' : LD N1 g x y')
    (hS : ∀ k, Sm N1 g x y k ↔ Sm N1 g x y' k) (hgy : g y ↔ g y') : ¬ y < y' := by
  intro hlt
  obtain ⟨hxy, hy, -, -⟩ := hL
  obtain ⟨hxy', hy', -, -⟩ := hL'
  by_cases hgy1 : g y
  · have m1 : Sm N1 g x y y := ⟨by omega, by omega, Or.inr (Or.inr ⟨le_rfl, hgy1⟩)⟩
    rcases (hS y).1 m1 with ⟨-, -, ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨h, -⟩⟩
    · omega
    · exact h hgy1
    · omega
  · have hyt : y ≠ N1 + 1 := fun h => hgy1 (h ▸ gt)
    have m1 : Sm N1 g x y' y := ⟨by omega, by omega, Or.inr (Or.inl ⟨hxy, hlt, hgy1⟩)⟩
    rcases (hS y).2 m1 with ⟨-, -, ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, h⟩⟩
    · omega
    · omega
    · exact hgy1 h

lemma Sm_inj (g0 : g 0) (gt : g (N1 + 1)) (g1 : ¬ g 1) (gN : ¬ g N1) (hN1 : 1 ≤ N1)
    {x y x' y' : ℕ} (hL : LD N1 g x y) (hL' : LD N1 g x' y')
    (hS : ∀ k, Sm N1 g x y k ↔ Sm N1 g x' y' k) : x = x' ∧ y = y' := by
  have hgx : g x ↔ g x' := by
    rw [← Sm_one g0 g1 hN1 hL, ← Sm_one g0 g1 hN1 hL']; exact hS 1
  have hgy : g y ↔ g y' := by
    rw [← Sm_top gt gN hN1 hL, ← Sm_top gt gN hN1 hL']; exact hS N1
  have hx : x = x' := by
    rcases lt_trichotomy x x' with h | h | h
    · exact absurd h (inj_x g0 hL hL' hS hgx hgy)
    · exact h
    · exact absurd h (inj_x g0 hL' hL (fun k => (hS k).symm) hgx.symm hgy.symm)
  subst hx
  refine ⟨rfl, ?_⟩
  rcases lt_trichotomy y y' with h | h | h
  · exact absurd h (inj_y gt hL hL' hS hgy)
  · exact h
  · exact absurd h (inj_y gt hL' hL (fun k => (hS k).symm) hgy.symm)

lemma comp_UU {x y x' y' : ℕ} (hL' : LD N1 g x' y')
    (hC : ∀ k, 1 ≤ k → k ≤ N1 → (Sm N1 g x y k ↔ ¬ Sm N1 g x' y' k))
    (hx : g x) (hy : g y) (hx' : ¬ g x') (hy' : ¬ g y') : False := by
  obtain ⟨hxy', hyb', hl', -⟩ := hL'
  obtain ⟨w, hw1, hw2, hw3⟩ := hl' (Or.inl hx') (Or.inl hy')
  have m : Sm N1 g x' y' w := ⟨by omega, by omega, Or.inr (Or.inl ⟨hw1, hw2, hw3⟩)⟩
  apply (hC w (by omega) (by omega)).1 _ m
  by_cases h1 : w ≤ x
  · exact ⟨by omega, by omega, Or.inl ⟨h1, hx⟩⟩
  by_cases h2 : w < y
  · exact ⟨by omega, by omega, Or.inr (Or.inl ⟨by omega, h2, hw3⟩)⟩
  · exact ⟨by omega, by omega, Or.inr (Or.inr ⟨by omega, hy⟩)⟩

lemma comp_one (gt : g (N1 + 1)) {x y x' y' : ℕ} (hL : LD N1 g x y) (hL' : LD N1 g x' y')
    (hC : ∀ k, 1 ≤ k → k ≤ N1 → (Sm N1 g x y k ↔ ¬ Sm N1 g x' y' k))
    (hx : g x) (hy : ¬ g y) (hx' : ¬ g x') (hy' : g y') : x' < y ∧ x < y' := by
  obtain ⟨hxy, hyb, -, -⟩ := hL
  obtain ⟨hxy', hyb', -, -⟩ := hL'
  have hyt : y ≠ N1 + 1 := fun h => hy (h ▸ gt)
  have n1 : ¬ Sm N1 g x y y := by
    rintro ⟨-, -, ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, h⟩⟩
    · omega
    · omega
    · exact hy h
  have m1 : Sm N1 g x' y' y := by
    by_contra h
    exact n1 ((hC y (by omega) (by omega)).2 h)
  constructor
  · rcases m1 with ⟨-, -, ⟨-, h⟩ | ⟨h, -, -⟩ | ⟨h, -⟩⟩
    · exact absurd h hx'
    · exact h
    · omega
  · by_contra hc
    have m2 : Sm N1 g x' y' y' := ⟨by omega, by omega, Or.inr (Or.inr ⟨le_rfl, hy'⟩)⟩
    have m3 : Sm N1 g x y y' := ⟨by omega, by omega, Or.inl ⟨by omega, hx⟩⟩
    exact (hC y' (by omega) (by omega)).1 m3 m2

lemma Sm_comp (g0 : g 0) (gt : g (N1 + 1)) (g1 : ¬ g 1) (gN : ¬ g N1) (hN1 : 1 ≤ N1)
    {x y x' y' : ℕ} (hL : LD N1 g x y) (hL' : LD N1 g x' y')
    (hC : ∀ k, 1 ≤ k → k ≤ N1 → (Sm N1 g x y k ↔ ¬ Sm N1 g x' y' k)) :
    (g x ∧ ¬ g y ∧ ¬ g x' ∧ g y' ∧ x' < y ∧ x < y') ∨
    (g x' ∧ ¬ g y' ∧ ¬ g x ∧ g y ∧ x < y' ∧ x' < y) := by
  have hC' : ∀ k, 1 ≤ k → k ≤ N1 → (Sm N1 g x' y' k ↔ ¬ Sm N1 g x y k) := by
    intro k h1 h2; have := hC k h1 h2; tauto
  have hgx : g x ↔ ¬ g x' := by
    rw [← Sm_one g0 g1 hN1 hL, ← Sm_one g0 g1 hN1 hL']; exact hC 1 le_rfl hN1
  have hgy : g y ↔ ¬ g y' := by
    rw [← Sm_top gt gN hN1 hL, ← Sm_top gt gN hN1 hL']; exact hC N1 hN1 le_rfl
  by_cases hx : g x <;> by_cases hy : g y
  · exact (comp_UU hL' hC hx hy (hgx.1 hx) (hgy.1 hy)).elim
  · have hx' := hgx.1 hx
    have hy' : g y' := by by_contra h; exact hy (hgy.2 h)
    exact Or.inl ⟨hx, hy, hx', hy', comp_one gt hL hL' hC hx hy hx' hy'⟩
  · have hx' : g x' := by by_contra h; exact hx (hgx.2 h)
    have hy' := hgy.1 hy
    obtain ⟨h1, h2⟩ := comp_one gt hL' hL hC' hx' hy' hx hy
    exact Or.inr ⟨hx', hy', hx, hy, h1, h2⟩
  · have hx' : g x' := by by_contra h; exact hx (hgx.2 h)
    have hy' : g y' := by by_contra h; exact hy (hgy.2 h)
    exact (comp_UU hL hC' hx' hy' hx hy).elim

end Abs

/-! ## indicator vectors -/

open Classical in
lemma R2 {n : ℕ} (Q Q' : ℕ → Prop)
    (h : ∀ k : Fin n, ((if Q (k.val + 1) then (1 : ℝ) else 0) - (if Q (n + 1) then 1 else 0)) =
      (if Q' (k.val + 1) then 1 else 0) - (if Q' (n + 1) then 1 else 0)) :
    (∀ j, 1 ≤ j → j ≤ n + 1 → (Q j ↔ Q' j)) ∨ (∀ j, 1 ≤ j → j ≤ n + 1 → Q j) ∨
      (∀ j, 1 ≤ j → j ≤ n + 1 → Q' j) := by
  have key : ∀ j, 1 ≤ j → j ≤ n + 1 → ((if Q j then (1 : ℝ) else 0) - (if Q (n + 1) then 1 else 0)) =
      (if Q' j then 1 else 0) - (if Q' (n + 1) then 1 else 0) := by
    intro j h1 h2
    by_cases hj : j = n + 1
    · subst hj; simp
    · have := h ⟨j - 1, by omega⟩
      simp only at this
      rwa [show j - 1 + 1 = j by omega] at this
  by_cases hA : Q (n + 1) <;> by_cases hB : Q' (n + 1)
  · left; intro j h1 h2; have := key j h1 h2
    by_cases hq : Q j <;> by_cases hq' : Q' j <;> simp only [hA, hB, hq, hq', if_true, if_false] at this <;>
      first | tauto | (norm_num at this)
  · right; left; intro j h1 h2; have := key j h1 h2
    by_cases hq : Q j <;> by_cases hq' : Q' j <;> simp only [hA, hB, hq, hq', if_true, if_false] at this <;>
      first | tauto | (norm_num at this)
  · right; right; intro j h1 h2; have := key j h1 h2
    by_cases hq : Q j <;> by_cases hq' : Q' j <;> simp only [hA, hB, hq, hq', if_true, if_false] at this <;>
      first | tauto | (norm_num at this)
  · left; intro j h1 h2; have := key j h1 h2
    by_cases hq : Q j <;> by_cases hq' : Q' j <;> simp only [hA, hB, hq, hq', if_true, if_false] at this <;>
      first | tauto | (norm_num at this)

section HL2
variable {n : ℕ} (σ : Fin (n - 1) → Bool)

def gU (j : ℕ) : Prop := ∃ h : j < n + 3, hlSign σ ⟨j, h⟩ = true

lemma gU_iff (k : Fin (n + 3)) : gU σ k.val ↔ hlSign σ k = true :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨k.isLt, h⟩⟩

lemma gU0 : gU σ 0 := ⟨by omega, sign_zero σ⟩
lemma gUt : gU σ (n + 1 + 1) := ⟨by omega, sign_top σ⟩
lemma gU1 : ¬ gU σ 1 := fun ⟨_, h⟩ => by rw [sign_one σ] at h; exact Bool.false_ne_true h
lemma gUN : ¬ gU σ (n + 1) := fun ⟨_, h⟩ => by rw [sign_n1 σ] at h; exact Bool.false_ne_true h

lemma S_eq_Sm (a b k : Fin (n + 3)) (hab : hlLabel σ a < hlLabel σ b) :
    k ∈ hlS σ s(a, b) ↔ Sm (n + 1) (gU σ) (hlLabel σ a).val (hlLabel σ b).val k.val := by
  rw [S_mem σ a b k hab]
  simp only [Sm, gU_iff, Bool.not_eq_true]

lemma sp (p : Fin (n + 3)) : hlSignPos σ p = hlSign σ (hlLabel σ p) := rfl

lemma lo_of (p : Fin (n + 3)) (h : hlSign σ (hlLabel σ p) = false) : p.val < (L1 σ).length := by
  by_contra h'
  push_neg at h'
  have := signpos_hi σ p h'
  rw [sp, h] at this
  exact Bool.false_ne_true this

lemma hi_of (p : Fin (n + 3)) (h : hlSign σ (hlLabel σ p) = true) : (L1 σ).length ≤ p.val := by
  by_contra h'
  push_neg at h'
  have := signpos_lo σ p h'
  rw [sp, h] at this
  exact Bool.false_ne_true this.symm

lemma m_le : (L1 σ).length ≤ n + 1 := by
  obtain ⟨p, hp, hp'⟩ := exists_pos_hi σ _ (sign_zero σ)
  obtain ⟨q, hq, hq'⟩ := exists_pos_hi σ _ (sign_top σ)
  have hne : p ≠ q := by
    intro h; subst h; rw [hp'] at hq'; simp [Fin.ext_iff] at hq'
  have := Fin.val_ne_of_ne hne
  have := p.isLt
  have := q.isLt
  omega

lemma pos_zero (p : Fin (n + 3)) (hp : (hlLabel σ p).val = 0) : p.val = n + 2 := by
  have hs : hlSign σ (hlLabel σ p) = true := by
    rw [show hlLabel σ p = ⟨0, by omega⟩ from Fin.ext hp]; exact sign_zero σ
  have hpm := hi_of σ p hs
  by_contra hne
  have hlt : p.val < n + 2 := by have := p.isLt; omega
  have := hi_anti σ p ⟨n + 2, by omega⟩ hpm hlt
  rw [Fin.lt_def, hp] at this
  omega

lemma pos_top (p : Fin (n + 3)) (hp : (hlLabel σ p).val = n + 2) : p.val = (L1 σ).length := by
  have hs : hlSign σ (hlLabel σ p) = true := by
    rw [show hlLabel σ p = ⟨n + 2, by omega⟩ from Fin.ext hp]; exact sign_top σ
  have hpm := hi_of σ p hs
  have hm := m_le σ
  by_contra hne
  have := hi_anti σ ⟨(L1 σ).length, by omega⟩ p le_rfl (by show (L1 σ).length < p.val; omega)
  rw [Fin.lt_def, hp] at this
  have := (hlLabel σ ⟨(L1 σ).length, by omega⟩).isLt
  omega

lemma DL (a b : Fin (n + 3)) (he : IsDiagonal s(a, b)) (hab : hlLabel σ a < hlLabel σ b)
    (hx : hlSign σ (hlLabel σ a) = false ∨ (hlLabel σ a).val = 0)
    (hy : hlSign σ (hlLabel σ b) = false ∨ (hlLabel σ b).val = n + 2) :
    ∃ k : Fin (n + 3), hlLabel σ a < k ∧ k < hlLabel σ b ∧ hlSign σ k = false := by
  by_contra H
  simp only [not_exists, not_and, Bool.not_eq_false] at H
  obtain ⟨hne, h1, h2⟩ := he a b rfl
  have hm := m_le σ
  have lowne : ∀ q : Fin (n + 3), hlSign σ (hlLabel σ q) = false →
      (hlLabel σ q).val ≠ 0 ∧ (hlLabel σ q).val ≠ n + 2 := fun q hq => sign_false_ne σ _ hq
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · have ha := lo_of σ a hx
    have hb := lo_of σ b hy
    have hab' : a.val < b.val := (pos_lt_iff σ a b).2 (Or.inr (Or.inl ⟨hx, hy, hab⟩))
    by_cases hq : a.val + 1 < b.val
    · have hql := signpos_lo σ ⟨a.val + 1, by omega⟩ (by show a.val + 1 < _; omega)
      rw [sp] at hql
      have := H _ (lo_mono σ a ⟨a.val + 1, by omega⟩ (by show a.val < a.val + 1; omega)
        (by show a.val + 1 < _; omega)) (lo_mono σ ⟨a.val + 1, by omega⟩ b hq hb)
      rw [hql] at this; exact Bool.false_ne_true this
    · apply h1; rw [cdist_of_le _ _ hab'.le]; omega
  · have ha := lo_of σ a hx
    have hb := pos_top σ b hy
    by_cases hq : a.val + 1 < (L1 σ).length
    · have hql := signpos_lo σ ⟨a.val + 1, by omega⟩ hq
      rw [sp] at hql
      have hlt : hlLabel σ ⟨a.val + 1, by omega⟩ < hlLabel σ b := by
        rw [Fin.lt_def, hy]
        have := (lowne _ hql).2
        have := (hlLabel σ ⟨a.val + 1, by omega⟩).isLt
        omega
      have := H _ (lo_mono σ a ⟨a.val + 1, by omega⟩ (by show a.val < a.val + 1; omega) hq) hlt
      rw [hql] at this; exact Bool.false_ne_true this
    · apply h1; rw [cdist_of_le _ _ (by omega)]; omega
  · have ha := pos_zero σ a hx
    have hb := lo_of σ b hy
    by_cases hq : 0 < b.val
    · have hql := signpos_lo σ ⟨0, by omega⟩ (by show 0 < _; omega)
      rw [sp] at hql
      have hlt : hlLabel σ a < hlLabel σ ⟨0, by omega⟩ := by
        rw [Fin.lt_def, hx]
        have := (lowne _ hql).1
        omega
      have := H _ hlt (lo_mono σ ⟨0, by omega⟩ b hq hb)
      rw [hql] at this; exact Bool.false_ne_true this
    · apply h1; rw [cdist_of_gt _ _ (by omega)]; omega
  · have := H ⟨1, by omega⟩ (by rw [Fin.lt_def, hx]; show 0 < 1; omega)
      (by rw [Fin.lt_def, hy]; show 1 < n + 2; omega)
    rw [sign_one σ] at this; exact Bool.false_ne_true this

lemma DU (a b : Fin (n + 3)) (he : IsDiagonal s(a, b)) (hab : hlLabel σ a < hlLabel σ b)
    (hx : hlSign σ (hlLabel σ a) = true) (hy : hlSign σ (hlLabel σ b) = true) :
    ∃ k : Fin (n + 3), hlLabel σ a < k ∧ k < hlLabel σ b ∧ hlSign σ k = true := by
  by_contra H
  simp only [not_exists, not_and, Bool.not_eq_true] at H
  obtain ⟨hne, h1, h2⟩ := he a b rfl
  have ha := hi_of σ a hx
  have hb := hi_of σ b hy
  have hba : b.val < a.val := (pos_lt_iff σ b a).2 (Or.inr (Or.inr ⟨hy, hx, hab⟩))
  by_cases hq : b.val + 1 < a.val
  · have hqh := signpos_hi σ ⟨b.val + 1, by omega⟩ (by show _ ≤ b.val + 1; omega)
    rw [sp] at hqh
    have := H _ (hi_anti σ ⟨b.val + 1, by omega⟩ a (by show _ ≤ b.val + 1; omega) hq)
      (hi_anti σ b ⟨b.val + 1, by omega⟩ hb (by show b.val < b.val + 1; omega))
    rw [hqh] at this; exact Bool.false_ne_true this.symm
  · apply h2; rw [cdist_of_le _ _ hba.le]; omega

lemma LD_of (a b : Fin (n + 3)) (he : IsDiagonal s(a, b)) (hab : hlLabel σ a < hlLabel σ b) :
    LD (n + 1) (gU σ) (hlLabel σ a).val (hlLabel σ b).val := by
  refine ⟨Fin.lt_def.1 hab, by have := (hlLabel σ b).isLt; omega, ?_, ?_⟩
  · intro hx hy
    have hx' : hlSign σ (hlLabel σ a) = false ∨ (hlLabel σ a).val = 0 := by
      rcases hx with hx | hx
      · left; rw [gU_iff] at hx; simpa using hx
      · right; exact hx
    have hy' : hlSign σ (hlLabel σ b) = false ∨ (hlLabel σ b).val = n + 2 := by
      rcases hy with hy | hy
      · left; rw [gU_iff] at hy; simpa using hy
      · right; exact hy
    obtain ⟨k, h1, h2, h3⟩ := DL σ a b he hab hx' hy'
    refine ⟨k.val, Fin.lt_def.1 h1, Fin.lt_def.1 h2, ?_⟩
    rw [gU_iff]; simp [h3]
  · intro hx hy
    rw [gU_iff] at hx hy
    obtain ⟨k, h1, h2, h3⟩ := DU σ a b he hab hx hy
    exact ⟨k.val, Fin.lt_def.1 h1, Fin.lt_def.1 h2, (gU_iff σ k).2 h3⟩

lemma cross_lab (a b c d : Fin (n + 3)) (ha : hlSign σ (hlLabel σ a) = true)
    (hb : hlSign σ (hlLabel σ b) = false) (hc : hlSign σ (hlLabel σ c) = false)
    (hd : hlSign σ (hlLabel σ d) = true) (hcb : hlLabel σ c < hlLabel σ b)
    (had : hlLabel σ a < hlLabel σ d) : Crosses s(a, b) s(c, d) := by
  have h1 : c.val < b.val := (pos_lt_iff σ c b).2 (Or.inr (Or.inl ⟨hc, hb, hcb⟩))
  have h2 : b.val < d.val := (pos_lt_iff σ b d).2 (Or.inl ⟨hb, hd⟩)
  have h3 : d.val < a.val := (pos_lt_iff σ d a).2 (Or.inr (Or.inr ⟨hd, ha, had⟩))
  have e : ∀ p : Fin (n + 3), cdist 0 p = p.val := fun p => by
    rw [cdist_of_le _ _ (by simp)]; simp
  rw [crosses_pos 0 a b c d, e, e, e, e]
  unfold Inter
  omega

lemma diag_pos (e : Sym2 (Fin (n + 3))) (he : IsDiagonal e) :
    ∃ a b, e = s(a, b) ∧ hlLabel σ a < hlLabel σ b ∧ IsDiagonal s(a, b) := by
  induction e using Sym2.ind with
  | _ a b =>
  have hne := (he a b rfl).1
  have hl : hlLabel σ a ≠ hlLabel σ b := fun h => hne (label_inj σ _ _ h)
  rcases lt_or_gt_of_ne hl with h | h
  · exact ⟨a, b, rfl, h, he⟩
  · exact ⟨b, a, Sym2.eq_swap, h, by rw [Sym2.eq_swap]; exact he⟩

open Classical in
lemma vec_spec (a b : Fin (n + 3)) (hab : hlLabel σ a < hlLabel σ b) (k : Fin n) :
    hlVec σ s(a, b) k =
      (if Sm (n + 1) (gU σ) (hlLabel σ a).val (hlLabel σ b).val (k.val + 1) then (1 : ℝ) else 0) -
      (if Sm (n + 1) (gU σ) (hlLabel σ a).val (hlLabel σ b).val (n + 1) then 1 else 0) := by
  have e1 := S_eq_Sm σ a b ⟨k.val + 1, by omega⟩ hab
  have e2 := S_eq_Sm σ a b ⟨n + 1, by omega⟩ hab
  simp only at e1 e2
  unfold hlVec
  by_cases h1 : Sm (n + 1) (gU σ) (hlLabel σ a).val (hlLabel σ b).val (k.val + 1) <;>
    by_cases h2 : Sm (n + 1) (gU σ) (hlLabel σ a).val (hlLabel σ b).val (n + 1) <;>
    simp [e1, e2, h1, h2]

lemma hl_entries (e : Sym2 (Fin (n + 3))) (k : Fin n) :
    hlVec σ e k = -1 ∨ hlVec σ e k = 0 ∨ hlVec σ e k = 1 := by
  unfold hlVec
  split_ifs <;> norm_num

open Classical in
lemma hl_ne_zero (e : Sym2 (Fin (n + 3))) (he : IsDiagonal e) : hlVec σ e ≠ 0 := by
  intro h0
  obtain ⟨a, b, rfl, hab, hd⟩ := diag_pos σ e he
  have hL := LD_of σ a b hd hab
  have := R2 (n := n) (Sm (n + 1) (gU σ) (hlLabel σ a).val (hlLabel σ b).val) (fun _ => False)
    (fun k => by rw [← vec_spec σ a b hab k, h0]; simp)
  rcases this with h | h | h
  · obtain ⟨k, hk⟩ := Sm_ne hL
    exact (h k hk.1 hk.2.1).1 hk
  · obtain ⟨k, h1, h2, h3⟩ := Sm_nf (gU0 σ) (gUt σ) hL
    exact h3 (h k h1 h2)
  · exact h 1 le_rfl (by omega)

lemma Sm_out {N1 : ℕ} {g : ℕ → Prop} {x y k : ℕ} (h : Sm N1 g x y k) : 1 ≤ k ∧ k ≤ N1 := ⟨h.1, h.2.1⟩

open Classical in
lemma hl_inj (e f : Sym2 (Fin (n + 3))) (he : IsDiagonal e) (hf : IsDiagonal f)
    (hv : hlVec σ e = hlVec σ f) : e = f := by
  obtain ⟨a, b, rfl, hab, hd⟩ := diag_pos σ e he
  obtain ⟨c, d, rfl, hcd, hd'⟩ := diag_pos σ f hf
  have hL := LD_of σ a b hd hab
  have hL' := LD_of σ c d hd' hcd
  have := R2 (n := n) (Sm (n + 1) (gU σ) (hlLabel σ a).val (hlLabel σ b).val)
    (Sm (n + 1) (gU σ) (hlLabel σ c).val (hlLabel σ d).val)
    (fun k => by rw [← vec_spec σ a b hab k, ← vec_spec σ c d hcd k, hv])
  rcases this with h | h | h
  · have hS : ∀ k, Sm (n + 1) (gU σ) (hlLabel σ a).val (hlLabel σ b).val k ↔
        Sm (n + 1) (gU σ) (hlLabel σ c).val (hlLabel σ d).val k := by
      intro k
      by_cases hk : 1 ≤ k ∧ k ≤ n + 1
      · exact h k hk.1 hk.2
      · exact ⟨fun h' => absurd (Sm_out h') hk, fun h' => absurd (Sm_out h') hk⟩
    obtain ⟨h1, h2⟩ := Sm_inj (gU0 σ) (gUt σ) (gU1 σ) (gUN σ) (by omega) hL hL' hS
    have e1 := label_inj σ a c (Fin.ext h1)
    have e2 := label_inj σ b d (Fin.ext h2)
    rw [e1, e2]
  · obtain ⟨k, h1, h2, h3⟩ := Sm_nf (gU0 σ) (gUt σ) hL
    exact (h3 (h k h1 h2)).elim
  · obtain ⟨k, h1, h2, h3⟩ := Sm_nf (gU0 σ) (gUt σ) hL'
    exact (h3 (h k h1 h2)).elim

open Classical in
lemma hl_cross (e f : Sym2 (Fin (n + 3))) (he : IsDiagonal e) (hf : IsDiagonal f)
    (hv : hlVec σ f = -hlVec σ e) : Crosses e f := by
  obtain ⟨a, b, rfl, hab, hd⟩ := diag_pos σ e he
  obtain ⟨c, d, rfl, hcd, hd'⟩ := diag_pos σ f hf
  have hL := LD_of σ a b hd hab
  have hL' := LD_of σ c d hd' hcd
  have := R2 (n := n) (Sm (n + 1) (gU σ) (hlLabel σ a).val (hlLabel σ b).val)
    (fun j => ¬ Sm (n + 1) (gU σ) (hlLabel σ c).val (hlLabel σ d).val j)
    (fun k => by
      have h1 := congrFun hv k
      rw [Pi.neg_apply, vec_spec σ a b hab k, vec_spec σ c d hcd k] at h1
      by_cases q1 : Sm (n + 1) (gU σ) (hlLabel σ c).val (hlLabel σ d).val (k.val + 1) <;>
        by_cases q2 : Sm (n + 1) (gU σ) (hlLabel σ c).val (hlLabel σ d).val (n + 1) <;>
        simp only [q1, q2, if_true, if_false, not_true_eq_false, not_false_eq_true] at h1 ⊢ <;>
        linarith)
  rcases this with h | h | h
  · rcases Sm_comp (gU0 σ) (gUt σ) (gU1 σ) (gUN σ) (by omega) hL hL' h with
      ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩
    · rw [gU_iff] at h1 h4
      rw [gU_iff, Bool.not_eq_true] at h2 h3
      exact cross_lab σ a b c d h1 h2 h3 h4 (Fin.lt_def.2 h5) (Fin.lt_def.2 h6)
    · rw [gU_iff] at h1 h4
      rw [gU_iff, Bool.not_eq_true] at h2 h3
      exact crosses_symm _ _ (cross_lab σ c d a b h1 h2 h3 h4 (Fin.lt_def.2 h5) (Fin.lt_def.2 h6))
  · obtain ⟨k, h1, h2, h3⟩ := Sm_nf (gU0 σ) (gUt σ) hL
    exact (h3 (h k h1 h2)).elim
  · obtain ⟨k, hk⟩ := Sm_ne hL'
    exact (h k hk.1 hk.2.1 hk).elim

lemma hl_indep (e f : Sym2 (Fin (n + 3))) (he : IsDiagonal e) (hf : IsDiagonal f)
    (hne : e ≠ f) (hnc : ¬ Crosses e f) (l : ℝ) : hlVec σ f ≠ l • hlVec σ e := by
  intro hl
  obtain ⟨i, hi⟩ : ∃ i, hlVec σ e i ≠ 0 := by
    by_contra h; push_neg at h; exact hl_ne_zero σ e he (funext h)
  have hfi := congrFun hl i
  simp only [Pi.smul_apply, smul_eq_mul] at hfi
  have hl3 : l = 0 ∨ l = 1 ∨ l = -1 := by
    rcases hl_entries σ e i with h1 | h1 | h1 <;>
      rcases hl_entries σ f i with h2 | h2 | h2 <;> rw [h1, h2] at hfi <;>
      first | exact absurd h1 hi | (left; linarith) | (right; left; linarith) |
        (right; right; linarith)
  rcases hl3 with rfl | rfl | rfl
  · rw [zero_smul] at hl; exact hl_ne_zero σ f hf hl
  · rw [one_smul] at hl; exact hne (hl_inj σ e f he hf hl.symm)
  · rw [neg_one_smul] at hl; exact hnc (hl_cross σ e f he hf hl)

end HL2

/-! ## the ray map from the HL fan to the Santos fan -/

theorem ray_part {n : ℕ} (σ : Fin (n - 1) → Bool) (T : Finset (Sym2 (Fin (n + 3))))
    (hT : IsTriangulation (n + 3) T)
    (L : (Fin n → ℝ) ≃ₗ[ℝ] ({d // d ∈ T} → ℝ))
    (hL : ∀ C ∈ hlFan σ, L '' C ∈ santosFan T) :
    ∃ φ : Sym2 (Fin (n + 3)) → Sym2 (Fin (n + 3)), ∃ c : Sym2 (Fin (n + 3)) → ℝ,
      ∀ e, IsDiagonal e → IsDiagonal (φ e) ∧ 0 < c e ∧ L (hlVec σ e) = c e • santosVec T (φ e) := by
  have imh : ∀ S : Set (Fin n → ℝ),
      L '' (PointedCone.hull ℝ S : Set _) = (PointedCone.hull ℝ (L '' S) : Set _) := by
    intro S
    have : (L '' S) = (L.toLinearMap.restrictScalars {c : ℝ // 0 ≤ c}) '' S := rfl
    rw [this, PointedCone.hull, PointedCone.hull,
      Submodule.span_image (L.toLinearMap.restrictScalars {c : ℝ // 0 ≤ c}), Submodule.map_coe]
    rfl
  have Lne : ∀ e, IsDiagonal e → L (hlVec σ e) ≠ 0 := fun e he =>
    (L.map_ne_zero_iff).2 (hl_ne_zero σ e he)
  have hray : ∀ e, ∃ f, ∃ t : ℝ, IsDiagonal e →
      (IsDiagonal f ∧ 0 < t ∧ L (hlVec σ e) = t • santosVec T f) := by
    intro e
    by_cases he : IsDiagonal e
    · obtain ⟨D', hD1, _, hD3⟩ := hL _ ⟨{e}, by
          intro x hx; rw [Finset.mem_singleton] at hx; rw [hx]; exact he, by
          intro x hx y hy; rw [Finset.mem_singleton] at hx hy; rw [hx, hy]
          exact crosses_irrefl e, rfl⟩
      rw [Finset.coe_singleton, Set.image_singleton, imh, Set.image_singleton] at hD3
      obtain ⟨d, hd, t, ht, hw⟩ := ray_pick (santosVec T) (↑D') _ (Lne e he)
        (fun d hd => santos_ne_zero T hT d (hD1 d hd)) hD3
      exact ⟨d, t, fun _ => ⟨hD1 d hd, ht, hw⟩⟩
    · exact ⟨e, 1, fun h => absurd h he⟩
  choose φ c hφ using hray
  exact ⟨φ, c, hφ⟩

theorem nc_part {n : ℕ} (hN : 5 ≤ n + 3) (σ : Fin (n - 1) → Bool) (T : Finset (Sym2 (Fin (n + 3))))
    (hT : IsTriangulation (n + 3) T)
    (L : (Fin n → ℝ) ≃ₗ[ℝ] ({d // d ∈ T} → ℝ))
    (hL : ∀ C ∈ hlFan σ, L '' C ∈ santosFan T)
    (φ : Sym2 (Fin (n + 3)) → Sym2 (Fin (n + 3))) (c : Sym2 (Fin (n + 3)) → ℝ)
    (hφ : ∀ e, IsDiagonal e → IsDiagonal (φ e) ∧ 0 < c e ∧ L (hlVec σ e) = c e • santosVec T (φ e)) :
    ∀ e f, IsDiagonal e → IsDiagonal f → ¬ Crosses e f → ¬ Crosses (φ e) (φ f) := by
  have imh : ∀ S : Set (Fin n → ℝ),
      L '' (PointedCone.hull ℝ S : Set _) = (PointedCone.hull ℝ (L '' S) : Set _) := by
    intro S
    have : (L '' S) = (L.toLinearMap.restrictScalars {c : ℝ // 0 ≤ c}) '' S := rfl
    rw [this, PointedCone.hull, PointedCone.hull,
      Submodule.span_image (L.toLinearMap.restrictScalars {c : ℝ // 0 ≤ c}), Submodule.map_coe]
    rfl
  have Lne : ∀ e, IsDiagonal e → L (hlVec σ e) ≠ 0 := fun e he =>
    (L.map_ne_zero_iff).2 (hl_ne_zero σ e he)
  have pick : ∀ e f, IsDiagonal e → IsDiagonal f → e ≠ f → ¬ Crosses e f →
      ∀ D' : Finset (Sym2 (Fin (n + 3))), (∀ d ∈ D', IsDiagonal d) →
      (PointedCone.hull ℝ {L (hlVec σ e), L (hlVec σ f)} : Set ({d // d ∈ T} → ℝ)) =
        (PointedCone.hull ℝ (santosVec T '' ↑D') : Set ({d // d ∈ T} → ℝ)) → φ e ∈ D' := by
    intro e f he hf hne hnc D' hD1 hD3
    have hind : ∀ l : ℝ, L (hlVec σ f) ≠ l • L (hlVec σ e) := by
      intro l h
      rw [← map_smul] at h
      exact hl_indep σ e f he hf hne hnc l (L.injective h)
    obtain ⟨d, hd, t, ht, hdeq⟩ := cone2_pick (santosVec T) (↑D') _ _ (Lne e he) hind hD3
    obtain ⟨hφd, hc, hφL⟩ := hφ e he
    have hv : santosVec T d = santosVec T (φ e) :=
      posparallel_eq _ _ (santos_entries T d) (santos_entries T (φ e))
        (santos_ne_zero T hT _ hφd) (t * c e) (mul_pos ht hc)
        (by rw [hdeq, hφL, smul_smul])
    have := santos_inj hN T hT d (φ e) (hD1 d hd) hφd hv
    rw [← this]; exact hd
  intro e f he hf hnc
  by_cases hef : e = f
  · rw [hef]; exact crosses_irrefl _
  obtain ⟨D', hD1, hD2, hD3⟩ := hL _ ⟨{e, f}, by
      intro x hx; rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact he
      · exact hf, by
      intro x hx y hy; rw [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact crosses_irrefl _
      · exact hnc
      · exact fun h => hnc (crosses_symm _ _ h)
      · exact crosses_irrefl _, rfl⟩
  rw [Finset.coe_insert, Finset.coe_singleton, Set.image_pair, imh, Set.image_pair] at hD3
  have m1 := pick e f he hf hef hnc D' hD1 hD3
  have m2 := pick f e hf he (Ne.symm hef) (fun h => hnc (crosses_symm _ _ h)) D' hD1
    (by rw [Set.pair_comm]; exact hD3)
  exact hD2 _ m1 _ m2

open Classical in
theorem finish {n : ℕ} (σ : Fin (n - 1) → Bool) (T : Finset (Sym2 (Fin (n + 3))))
    (hT : IsTriangulation (n + 3) T)
    (L : (Fin n → ℝ) ≃ₗ[ℝ] ({d // d ∈ T} → ℝ))
    (φ : Sym2 (Fin (n + 3)) → Sym2 (Fin (n + 3))) (c : Sym2 (Fin (n + 3)) → ℝ)
    (hφ : ∀ e, IsDiagonal e → IsDiagonal (φ e) ∧ 0 < c e ∧ L (hlVec σ e) = c e • santosVec T (φ e))
    (hnc : ∀ e f, IsDiagonal e → IsDiagonal f → ¬ Crosses e f → ¬ Crosses (φ e) (φ f)) :
    ∃ π : Sym2 (Fin (n + 3)) ≃ Sym2 (Fin (n + 3)),
      (∀ e, IsDiagonal e ↔ IsDiagonal (π e)) ∧
      (∀ e f, IsDiagonal e → IsDiagonal f →
        (Crosses e f ↔ Crosses (π e) (π f))) ∧
      (∀ e f, IsDiagonal e → IsDiagonal f → e ≠ f →
        (Opposite (hlVec σ e) (hlVec σ f) ↔
          Opposite (santosVec T (π e)) (santosVec T (π f)))) := by
  have hinj : ∀ e f, IsDiagonal e → IsDiagonal f → φ e = φ f → e = f := by
    intro e f he hf hef
    obtain ⟨hφe, hce, hLe⟩ := hφ e he
    obtain ⟨hφf, hcf, hLf⟩ := hφ f hf
    have h1 : hlVec σ e = (c e / c f) • hlVec σ f := by
      apply L.injective
      rw [map_smul, hLe, hLf, hef, smul_smul, div_mul_cancel₀ _ hcf.ne']
    have h2 := posparallel_eq _ _ (hl_entries σ e) (hl_entries σ f)
      (hl_ne_zero σ f hf) (c e / c f) (div_pos hce hcf) h1
    exact hl_inj σ e f he hf h2
  have hcr : ∀ e f, IsDiagonal e → IsDiagonal f → (Crosses (φ e) (φ f) ↔ Crosses e f) := by
    intro e f he hf
    constructor
    · intro h; by_contra hc; exact hnc e f he hf hc h
    · intro h; by_contra hc
      obtain ⟨⟨e', f'⟩, ⟨he', hf', hnc'⟩, heq⟩ := fin_surj
        (fun p : Sym2 (Fin (n + 3)) × Sym2 (Fin (n + 3)) =>
          IsDiagonal p.1 ∧ IsDiagonal p.2 ∧ ¬ Crosses p.1 p.2)
        (fun p => (φ p.1, φ p.2))
        (fun p hp => ⟨(hφ _ hp.1).1, (hφ _ hp.2.1).1, hnc _ _ hp.1 hp.2.1 hp.2.2⟩)
        (fun p q hp hq hpq => by
          simp only [Prod.mk.injEq] at hpq
          exact Prod.ext (hinj _ _ hp.1 hq.1 hpq.1) (hinj _ _ hp.2.1 hq.2.1 hpq.2))
        (φ e, φ f) ⟨(hφ e he).1, (hφ f hf).1, hc⟩
      simp only [Prod.mk.injEq] at heq
      have e1 := hinj _ _ he' he heq.1
      have e2 := hinj _ _ hf' hf heq.2
      rw [e1, e2] at hnc'
      exact hnc' h
  let F : Sym2 (Fin (n + 3)) → Sym2 (Fin (n + 3)) := fun e => if IsDiagonal e then φ e else e
  have hFinj : Function.Injective F := by
    intro e f h
    simp only [F] at h
    split_ifs at h with he hf hf
    · exact hinj e f he hf h
    · exact absurd (h ▸ (hφ e he).1) hf
    · exact absurd (h.symm ▸ (hφ f hf).1) he
    · exact h
  let π := Equiv.ofBijective F (Finite.injective_iff_bijective.1 hFinj)
  have hπ : ∀ e, IsDiagonal e → π e = φ e := fun e he => by
    simp [π, F, he]
  have hπ' : ∀ e, ¬ IsDiagonal e → π e = e := fun e he => by
    simp [π, F, he]
  refine ⟨π, ?_, ?_, ?_⟩
  · intro e
    by_cases he : IsDiagonal e
    · rw [hπ e he]; exact ⟨fun _ => (hφ e he).1, fun _ => he⟩
    · rw [hπ' e he]
  · intro e f he hf
    rw [hπ e he, hπ f hf]; exact (hcr e f he hf).symm
  · intro e f he hf _
    rw [hπ e he, hπ f hf]
    obtain ⟨-, hce, hLe⟩ := hφ e he
    obtain ⟨-, hcf, hLf⟩ := hφ f hf
    constructor
    · rintro ⟨t, ht, h⟩
      refine ⟨t * c f / c e, by positivity, ?_⟩
      have h1 := congrArg L h
      rw [map_neg, map_smul, hLe, hLf] at h1
      have h2 := congrArg (fun v => (c e)⁻¹ • v) h1
      simp only [smul_smul, inv_mul_cancel₀ hce.ne', one_smul, smul_neg] at h2
      rw [h2]
      congr 2
      field_simp
    · rintro ⟨t, ht, h⟩
      refine ⟨t * c e / c f, by positivity, ?_⟩
      apply L.injective
      rw [map_neg, map_smul, hLe, hLf, h, smul_neg, smul_smul, smul_smul,
        div_mul_cancel₀ _ hcf.ne', mul_comm]

lemma fin4_nc (e f : Sym2 (Fin 4)) (he : IsDiagonal e) (hf : IsDiagonal f)
    (hnc : ¬ Crosses e f) : e = f := by
  have hd : ∀ e : Sym2 (Fin 4), IsDiagonal e → e = s(0, 2) ∨ e = s(1, 3) := by decide
  have hc : Crosses (s(0, 2) : Sym2 (Fin 4)) s(1, 3) := by decide
  rcases hd e he with rfl | rfl <;> rcases hd f hf with rfl | rfl
  · rfl
  · exact (hnc hc).elim
  · exact (hnc (crosses_symm _ _ hc)).elim
  · rfl

end Phl

open ChvatalArtGallery.FanPartition AssocRealizations.TypesMeet in
theorem solution (n : ℕ)
    (σ : Fin (n - 1) → Bool) (T : Finset (Sym2 (Fin (n + 3))))
    (hT : IsTriangulation (n + 3) T)
    (hiso : NormallyIsomorphic (hlFan σ) (santosFan T)) :
    ∃ π : Sym2 (Fin (n + 3)) ≃ Sym2 (Fin (n + 3)),
      (∀ e, IsDiagonal e ↔ IsDiagonal (π e)) ∧
      (∀ e f, IsDiagonal e → IsDiagonal f →
        (Crosses e f ↔ Crosses (π e) (π f))) ∧
      (∀ e f, IsDiagonal e → IsDiagonal f → e ≠ f →
        (Opposite (hlVec σ e) (hlVec σ f) ↔
          Opposite (santosVec T (π e)) (santosVec T (π f)))) := by
  obtain ⟨L, hL⟩ := hiso
  obtain ⟨φ, c, hφ⟩ := Phl.ray_part σ T hT L hL
  rcases n with _ | _ | n
  · have hnd : ∀ e : Sym2 (Fin (0 + 3)), ¬ IsDiagonal e := by decide
    exact ⟨Equiv.refl _, fun e => Iff.rfl, fun e f _ _ => Iff.rfl, fun e f he => absurd he (hnd e)⟩
  · exact Phl.finish σ T hT L φ c hφ (fun e f he hf h => by
      rw [Phl.fin4_nc e f he hf h]; exact Phl.crosses_irrefl _)
  · exact Phl.finish σ T hT L φ c hφ (Phl.nc_part (by omega) σ T hT L hL φ c hφ)
