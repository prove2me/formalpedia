-- Prove2me | solution 1 for AssocRealizations.TypesMeet.proposition_4_7
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-30T12:25:28.639382+00:00
-- url     : https://prove2.me/submissions/0027a20f-b504-4406-b91c-d17fb5f4223d

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

/-! ## Proposition 4.7 -/

lemma head_filter_range (N r0 : ℕ) (p : ℕ → Bool) (h0 : r0 < N) (hp : p r0 = true)
    (hlt : ∀ r, r < r0 → p r = false) : ((List.range N).filter p).headD 0 = r0 := by
  obtain ⟨k, rfl⟩ : ∃ k, N = r0 + 1 + k := ⟨N - r0 - 1, by omega⟩
  have e1 : (List.range r0).filter p = [] :=
    List.filter_eq_nil_iff.2 (fun a ha => by simp [hlt a (List.mem_range.1 ha)])
  rw [List.range_add, List.range_succ, List.filter_append, List.filter_append, e1]
  simp [hp]

lemma rev_filter_range (m r0 : ℕ) (p : ℕ → Bool) (h0 : r0 < m) (hp : p r0 = true)
    (hgt : ∀ r, r0 < r → r < m → p r = false) :
    (((List.range m).filter p).reverse).headD 0 = r0 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = r0 + 1 + k := ⟨m - r0 - 1, by omega⟩
  have e2 : ((List.range k).map (r0 + 1 + ·)).filter p = [] := by
    apply List.filter_eq_nil_iff.2
    intro a ha
    simp only [List.mem_map, List.mem_range] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    simp [hgt (r0 + 1 + i) (by omega) (by omega)]
  rw [List.range_add, List.range_succ, List.filter_append, List.filter_append, e2]
  simp [hp]

lemma vA {α : Type} (a1 b1 a2 b2 : α) : ∀ p : α, (p ∈ s(a1, b1) ∨ p ∈ s(a2, b2)) ↔
    (p = a1 ∨ p = a2 ∨ p = b1 ∨ p = b2) := fun p => by simp only [Sym2.mem_iff]; tauto

lemma vB {α : Type} (a1 b1 a2 b2 : α) : ∀ p : α, (p ∈ s(a1, b1) ∨ p ∈ s(a2, b2)) ↔
    (p = a1 ∨ p = a2 ∨ p = b2 ∨ p = b1) := fun p => by simp only [Sym2.mem_iff]; tauto

lemma vC {α : Type} (a1 b1 a2 b2 : α) : ∀ p : α, (p ∈ s(a1, b1) ∨ p ∈ s(a2, b2)) ↔
    (p = a2 ∨ p = a1 ∨ p = b1 ∨ p = b2) := fun p => by simp only [Sym2.mem_iff]; tauto

lemma vD {α : Type} (a1 b1 a2 b2 : α) : ∀ p : α, (p ∈ s(a1, b1) ∨ p ∈ s(a2, b2)) ↔
    (p = a2 ∨ p = a1 ∨ p = b2 ∨ p = b1) := fun p => by simp only [Sym2.mem_iff]; tauto

section P47
variable {n : ℕ} (σ : Fin (n - 1) → Bool)

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

lemma sg0 (j : Fin (n + 3)) (h : j.val = 0) : hlSign σ j = true := by
  rw [show j = ⟨0, by omega⟩ from Fin.ext h]; exact sign_zero σ

lemma sg1 (j : Fin (n + 3)) (h : j.val = 1) : hlSign σ j = false := by
  rw [show j = ⟨1, by omega⟩ from Fin.ext h]; exact sign_one σ

lemma sgN1 (j : Fin (n + 3)) (h : j.val = n + 1) : hlSign σ j = false := by
  rw [show j = ⟨n + 1, by omega⟩ from Fin.ext h]; exact sign_n1 σ

lemma sgN2 (j : Fin (n + 3)) (h : j.val = n + 2) : hlSign σ j = true := by
  rw [show j = ⟨n + 2, by omega⟩ from Fin.ext h]; exact sign_top σ

lemma mid_lower (a b : Fin (n + 3)) (hb : hlSign σ (hlLabel σ b) = false)
    (hab : a.val + 1 < b.val) :
    ∃ p : Fin (n + 3), hlLabel σ a < hlLabel σ p ∧ hlLabel σ p < hlLabel σ b ∧
      hlSign σ (hlLabel σ p) = false := by
  have hb' := lo_of σ b hb
  refine ⟨⟨a.val + 1, by omega⟩, lo_mono σ _ _ (by show a.val < a.val + 1; omega)
    (by show a.val + 1 < (L1 σ).length; omega),
    lo_mono σ _ _ (by show a.val + 1 < b.val; omega) hb', ?_⟩
  exact signpos_lo σ _ (by show a.val + 1 < (L1 σ).length; omega)

lemma mid_upper (a b : Fin (n + 3)) (ha : hlSign σ (hlLabel σ a) = true)
    (hab : a.val + 1 < b.val) :
    ∃ p : Fin (n + 3), hlLabel σ b < hlLabel σ p ∧ hlLabel σ p < hlLabel σ a ∧
      hlSign σ (hlLabel σ p) = true := by
  have ha' := hi_of σ a ha
  refine ⟨⟨a.val + 1, by omega⟩, hi_anti σ _ _ (by show (L1 σ).length ≤ a.val + 1; omega)
    (by show a.val + 1 < b.val; omega),
    hi_anti σ _ _ ha' (by show a.val < a.val + 1; omega), ?_⟩
  exact signpos_hi σ _ (by show (L1 σ).length ≤ a.val + 1; omega)

lemma one_mem (a b : Fin (n + 3)) (hd : IsDiagonal s(a, b)) (hab : hlLabel σ a < hlLabel σ b) :
    (⟨1, by omega⟩ : Fin (n + 3)) ∈ hlS σ s(a, b) ↔ hlSign σ (hlLabel σ a) = true := by
  rw [S_mem σ a b _ hab]
  obtain ⟨-, h2, -⟩ := hd a b rfl
  have hx0 := sg0 σ (hlLabel σ a)
  have hy1 := sg1 σ (hlLabel σ b)
  have hs1 := sg1 σ (⟨1, by omega⟩ : Fin (n + 3)) rfl
  have h01 : ¬ ((hlLabel σ a).val = 0 ∧ (hlLabel σ b).val = 1) := by
    rintro ⟨ha, hb⟩
    have pa := pos_zero σ a ha
    have pb := lo_of σ b (sg1 σ _ hb)
    have pb0 : b.val = 0 := by
      by_contra h
      have h3 := Fin.lt_def.1 (lo_mono σ ⟨0, by omega⟩ b (by show 0 < b.val; omega) pb)
      have hs0 := signpos_lo σ ⟨0, by omega⟩ (by show 0 < (L1 σ).length; omega)
      have h4 := (sign_false_ne σ _ hs0).1
      omega
    apply h2; rw [cdist_of_gt a b (by omega)]; omega
  have hab' := Fin.lt_def.1 hab
  simp only [Fin.val_mk, hs1]
  rcases hX : hlSign σ (hlLabel σ a) with _ | _ <;>
    rcases hY : hlSign σ (hlLabel σ b) with _ | _ <;>
    simp only [hX, hY, Bool.false_eq_true, Bool.true_eq_false, eq_self_iff_true, true_and,
      and_true, false_and, and_false, or_false, false_or, true_or, or_true, not_true_eq_false,
      not_false_eq_true, imp_false, implies_true, iff_true, iff_false] at hx0 hy1 ⊢ <;> omega

lemma top_mem (a b : Fin (n + 3)) (hd : IsDiagonal s(a, b)) (hab : hlLabel σ a < hlLabel σ b) :
    (⟨n + 1, by omega⟩ : Fin (n + 3)) ∈ hlS σ s(a, b) ↔ hlSign σ (hlLabel σ b) = true := by
  rw [S_mem σ a b _ hab]
  obtain ⟨-, h1, -⟩ := hd a b rfl
  have hxN := sgN1 σ (hlLabel σ a)
  have hyN := sgN1 σ (hlLabel σ b)
  have hyT := sgN2 σ (hlLabel σ b)
  have hs1 := sgN1 σ (⟨n + 1, by omega⟩ : Fin (n + 3)) rfl
  have hm := m_le σ
  have hNN : ¬ ((hlLabel σ a).val = n + 1 ∧ (hlLabel σ b).val = n + 2) := by
    rintro ⟨ha, hb⟩
    have pb := pos_top σ b hb
    have pa := lo_of σ a (sgN1 σ _ ha)
    have pa' : a.val + 1 = (L1 σ).length := by
      by_contra h
      have h3 := Fin.lt_def.1 (lo_mono σ a ⟨a.val + 1, by omega⟩ (by show a.val < a.val + 1; omega)
        (by show a.val + 1 < (L1 σ).length; omega))
      have hs1 := signpos_lo σ ⟨a.val + 1, by omega⟩ (by show a.val + 1 < (L1 σ).length; omega)
      have h4 := (sign_false_ne σ _ hs1).2
      have := (hlLabel σ ⟨a.val + 1, by omega⟩).isLt
      omega
    apply h1; rw [cdist_of_le a b (by omega)]; omega
  have hab' := Fin.lt_def.1 hab
  have hyl := (hlLabel σ b).isLt
  simp only [Fin.val_mk, hs1]
  rcases hX : hlSign σ (hlLabel σ a) with _ | _ <;>
    rcases hY : hlSign σ (hlLabel σ b) with _ | _ <;>
    simp only [hX, hY, Bool.false_eq_true, Bool.true_eq_false, eq_self_iff_true, true_and,
      and_true, false_and, and_false, or_false, false_or, true_or, or_true, not_true_eq_false,
      not_false_eq_true, imp_false, implies_true, iff_true, iff_false] at hxN hyN hyT ⊢ <;> omega

lemma in_out (a b : Fin (n + 3)) (hd : IsDiagonal s(a, b)) (hab : hlLabel σ a < hlLabel σ b) :
    (∃ t : Fin (n + 3), 1 ≤ t.val ∧ t.val ≤ n + 1 ∧ t ∈ hlS σ s(a, b)) ∧
    (∃ t : Fin (n + 3), 1 ≤ t.val ∧ t.val ≤ n + 1 ∧ t ∉ hlS σ s(a, b)) := by
  have o := one_mem σ a b hd hab
  have t := top_mem σ a b hd hab
  obtain ⟨-, h1, h2⟩ := hd a b rfl
  have hab' := Fin.lt_def.1 hab
  have hyb := (hlLabel σ b).isLt
  have P1 : 1 ≤ (⟨1, by omega⟩ : Fin (n + 3)).val ∧ (⟨1, by omega⟩ : Fin (n + 3)).val ≤ n + 1 :=
    ⟨le_rfl, by show 1 ≤ n + 1; omega⟩
  have PN : 1 ≤ (⟨n + 1, by omega⟩ : Fin (n + 3)).val ∧
      (⟨n + 1, by omega⟩ : Fin (n + 3)).val ≤ n + 1 := ⟨by show 1 ≤ n + 1; omega, le_rfl⟩
  rcases hX : hlSign σ (hlLabel σ a) with _ | _ <;> rcases hY : hlSign σ (hlLabel σ b) with _ | _
  · have hpos : a.val < b.val := (pos_lt_iff σ a b).2 (Or.inr (Or.inl ⟨hX, hY, hab⟩))
    have hgap : a.val + 1 < b.val := by
      by_contra h; apply h1; rw [cdist_of_le _ _ hpos.le]; omega
    obtain ⟨p, hp1, hp2, hp3⟩ := mid_lower σ a b hY hgap
    have hb := sign_false_ne σ _ hp3
    have hp1' := Fin.lt_def.1 hp1
    have hp2' := Fin.lt_def.1 hp2
    refine ⟨⟨hlLabel σ p, by omega, by omega, ?_⟩, ⟨⟨1, by omega⟩, P1.1, P1.2, ?_⟩⟩
    · rw [S_mem σ a b _ hab]
      exact ⟨by omega, by omega, Or.inr (Or.inl ⟨hp1', hp2', hp3⟩)⟩
    · rw [o, hX]; simp
  · exact ⟨⟨⟨n + 1, by omega⟩, PN.1, PN.2, by rw [t]; exact hY⟩,
      ⟨⟨1, by omega⟩, P1.1, P1.2, by rw [o, hX]; simp⟩⟩
  · exact ⟨⟨⟨1, by omega⟩, P1.1, P1.2, by rw [o]; exact hX⟩,
      ⟨⟨n + 1, by omega⟩, PN.1, PN.2, by rw [t, hY]; simp⟩⟩
  · have hpos : b.val < a.val := (pos_lt_iff σ b a).2 (Or.inr (Or.inr ⟨hY, hX, hab⟩))
    have hgap : b.val + 1 < a.val := by
      by_contra h; apply h2; rw [cdist_of_le _ _ hpos.le]; omega
    obtain ⟨p, hp1, hp2, hp3⟩ := mid_upper σ b a hY hgap
    have hp1' := Fin.lt_def.1 hp1
    have hp2' := Fin.lt_def.1 hp2
    refine ⟨⟨⟨1, by omega⟩, P1.1, P1.2, by rw [o]; exact hX⟩,
      ⟨hlLabel σ p, by omega, by omega, ?_⟩⟩
    rw [S_mem σ a b _ hab]
    rintro ⟨-, -, h | h | h⟩
    · omega
    · rw [hp3] at h; exact Bool.noConfusion h.2.2
    · omega

lemma comp_of_opp (a1 b1 a2 b2 : Fin (n + 3)) (hd1 : IsDiagonal s(a1, b1))
    (h1 : hlLabel σ a1 < hlLabel σ b1) (c : ℝ) (hc : 0 < c)
    (hv : hlVec σ s(a1, b1) = -(c • hlVec σ s(a2, b2))) (k : Fin (n + 3))
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ n + 1) :
    (k ∈ hlS σ s(a1, b1) ↔ k ∉ hlS σ s(a2, b2)) := by
  have H : ∀ k : Fin (n + 3), 1 ≤ k.val → k.val ≤ n + 1 →
      ((if k ∈ hlS σ s(a1, b1) then (1:ℝ) else 0) -
        (if (⟨n + 1, by omega⟩ : Fin (n + 3)) ∈ hlS σ s(a1, b1) then 1 else 0)) =
      -(c * ((if k ∈ hlS σ s(a2, b2) then (1:ℝ) else 0) -
        (if (⟨n + 1, by omega⟩ : Fin (n + 3)) ∈ hlS σ s(a2, b2) then 1 else 0))) := by
    intro k hk1 hk2
    by_cases hkt : k.val = n + 1
    · rw [show k = ⟨n + 1, by omega⟩ from Fin.ext hkt]; simp
    · obtain ⟨m, hm⟩ : ∃ m : Fin n, m.val + 1 = k.val := ⟨⟨k.val - 1, by omega⟩, by
        show k.val - 1 + 1 = k.val; omega⟩
      have := congrFun hv m
      have hkm : (⟨m.val + 1, by omega⟩ : Fin (n + 3)) = k := Fin.ext hm
      simp only [hlVec, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at this
      rw [hkm] at this
      exact this
  obtain ⟨⟨t1, t11, t12, ht1⟩, ⟨t0, t01, t02, ht0⟩⟩ := in_out σ a1 b1 hd1 h1
  have H1 := H t1 t11 t12
  have H0 := H t0 t01 t02
  have Hk := H k hk1 hk2
  rw [if_pos ht1] at H1
  rw [if_neg ht0] at H0
  have ind : ∀ (P : Prop) [Decidable P],
      (if P then (1:ℝ) else 0) = 0 ∨ (if P then (1:ℝ) else 0) = 1 := by
    intro P _; split_ifs <;> simp
  obtain ⟨hc1, hb1⟩ : c = 1 ∧ (if t1 ∈ hlS σ s(a2, b2) then (1:ℝ) else 0) = 0 := by
    rcases ind (t1 ∈ hlS σ s(a2, b2)) with h | h <;>
      rcases ind (t0 ∈ hlS σ s(a2, b2)) with h' | h' <;>
      rw [h] at H1 <;> rw [h'] at H0 <;> constructor <;> linarith
  subst hc1
  rw [hb1] at H1
  constructor
  · intro hA hB; rw [if_pos hA, if_pos hB] at Hk; linarith
  · intro hB; by_contra hA; rw [if_neg hA, if_neg hB] at Hk; linarith

lemma signNat_eq (r : ℕ) (h : r < n + 3) : hlSignNat σ r = hlSign σ ⟨r, h⟩ := by
  unfold hlSignNat; rw [dif_pos h]

lemma hlI_eq (m : ℕ) (r0 M : Fin (n + 3)) (hM : M.val = m) (h0 : r0.val < m)
    (hne : hlSign σ r0 ≠ hlSign σ M)
    (hmid : ∀ r : Fin (n + 3), r0.val < r.val → r.val < m → hlSign σ r = hlSign σ M) :
    hlI σ m = r0.val := by
  unfold hlI
  have hm : m < n + 3 := by have := M.isLt; omega
  have sm : hlSignNat σ m = hlSign σ M := by
    rw [signNat_eq σ m hm]; congr 1; exact Fin.ext hM.symm
  apply rev_filter_range
  · exact h0
  · simp only [decide_eq_true_eq, ne_eq]; rw [signNat_eq σ r0.val r0.isLt, sm]; exact hne
  · intro r hr1 hr2
    simp only [decide_eq_false_iff_not, ne_eq, not_not]
    rw [signNat_eq σ r (by omega), sm]
    exact hmid ⟨r, by omega⟩ hr1 hr2

lemma hlK_eq (m : ℕ) (r0 M : Fin (n + 3)) (hM : M.val = m + 1) (h0 : m + 1 < r0.val)
    (hne : hlSign σ r0 ≠ hlSign σ M)
    (hmid : ∀ r : Fin (n + 3), m + 1 < r.val → r.val < r0.val → hlSign σ r = hlSign σ M) :
    hlK σ m = r0.val := by
  unfold hlK
  have := M.isLt
  have sm : hlSignNat σ (m + 1) = hlSign σ M := by
    rw [signNat_eq σ (m + 1) (by omega)]; congr 1; exact Fin.ext hM.symm
  apply head_filter_range
  · exact r0.isLt
  · simp only [decide_eq_true_eq, ne_eq]; rw [signNat_eq σ r0.val r0.isLt, sm]; exact ⟨h0, hne⟩
  · intro r hr
    simp only [decide_eq_false_iff_not, not_and, ne_eq, not_not]
    intro hr1
    have := r0.isLt
    rw [signNat_eq σ r (by omega), sm]
    exact hmid ⟨r, by omega⟩ hr1 hr

lemma ordered (e : Sym2 (Fin (n + 3))) (he : IsDiagonal e) :
    ∃ a b : Fin (n + 3), e = s(a, b) ∧ hlLabel σ a < hlLabel σ b := by
  induction e using Sym2.ind with
  | _ x y =>
  have hxy := (he x y rfl).1
  have hl : hlLabel σ x ≠ hlLabel σ y := fun h => hxy (label_inj σ _ _ h)
  rcases lt_or_gt_of_ne hl with h | h
  · exact ⟨x, y, rfl, h⟩
  · exact ⟨y, x, Sym2.eq_swap, h⟩

set_option maxHeartbeats 1000000 in
lemma core (a1 b1 a2 b2 : Fin (n + 3)) (hd1 : IsDiagonal s(a1, b1)) (hd2 : IsDiagonal s(a2, b2))
    (h1 : hlLabel σ a1 < hlLabel σ b1) (h2 : hlLabel σ a2 < hlLabel σ b2)
    (comp : ∀ k : Fin (n + 3), 1 ≤ k.val → k.val ≤ n + 1 →
      (k ∈ hlS σ s(a1, b1) ↔ k ∉ hlS σ s(a2, b2)))
    (hs : hlSign σ (hlLabel σ a1) = true) :
    ∃ j : Fin n, ∃ a b c d : Fin (n + 3),
        (hlLabel σ a).val = hlI σ (j.val + 1) ∧
        (hlLabel σ b).val = j.val + 1 ∧
        (hlLabel σ c).val = j.val + 2 ∧
        (hlLabel σ d).val = hlK σ (j.val + 1) ∧
        Crosses s(a1, b1) s(a2, b2) ∧
        (∀ p : Fin (n + 3), (p ∈ s(a1, b1) ∨ p ∈ s(a2, b2)) ↔
          (p = a ∨ p = b ∨ p = c ∨ p = d)) ∧
        (hlS σ s(a1, b1) = Finset.univ.filter
              (fun k : Fin (n + 3) => 1 ≤ k.val ∧ k.val ≤ j.val + 1) ∧
            hlS σ s(a2, b2) = Finset.univ.filter
              (fun k : Fin (n + 3) => j.val + 2 ≤ k.val ∧ k.val ≤ n + 1)) := by
  have o1 := one_mem σ a1 b1 hd1 h1
  have o2 := one_mem σ a2 b2 hd2 h2
  have t1 := top_mem σ a1 b1 hd1 h1
  have t2 := top_mem σ a2 b2 hd2 h2
  have c1 := comp ⟨1, by omega⟩ le_rfl (by show 1 ≤ n + 1; omega)
  have cN := comp ⟨n + 1, by omega⟩ (by show 1 ≤ n + 1; omega) le_rfl
  have h1' := Fin.lt_def.1 h1
  have h2' := Fin.lt_def.1 h2
  have lx1 := (hlLabel σ a1).isLt
  have lx2 := (hlLabel σ a2).isLt
  have ly1 := (hlLabel σ b1).isLt
  have ly2 := (hlLabel σ b2).isLt
  have sx2 : hlSign σ (hlLabel σ a2) = false := by
    rw [o1, o2] at c1; simpa [hs] using c1
  have sy1 : hlSign σ (hlLabel σ b1) = false := by
    by_contra hy
    rw [Bool.not_eq_false] at hy
    have sy2 : hlSign σ (hlLabel σ b2) = false := by
      rw [t1, t2] at cN; simpa [hy] using cN
    obtain ⟨⟨t, ht1, ht2, ht⟩, -⟩ := in_out σ a2 b2 hd2 h2
    have ct := comp t ht1 ht2
    rw [S_mem σ a2 b2 t h2] at ht
    rw [S_mem σ a1 b1 t h1, S_mem σ a2 b2 t h2] at ct
    rcases hT : hlSign σ t with _ | _ <;>
      simp only [hT, hs, hy, sx2, sy2, Bool.false_eq_true, Bool.true_eq_false, eq_self_iff_true,
        true_and, and_true, false_and, and_false, or_false, false_or] at ht ct <;> omega
  have sy2 : hlSign σ (hlLabel σ b2) = true := by
    rw [t1, t2, sy1] at cN; simpa using cN
  have bx2 := sign_false_ne σ _ sx2
  have by1 := sign_false_ne σ _ sy1
  have F2 : ∀ k : Fin (n + 3), hlSign σ k = false →
      (k.val < (hlLabel σ b1).val ↔ k.val ≤ (hlLabel σ a2).val) := by
    intro k hk
    have hb := sign_false_ne σ k hk
    have := k.isLt
    have ck := comp k (by omega) (by omega)
    rw [S_mem σ a1 b1 k h1, S_mem σ a2 b2 k h2] at ck
    simp only [hk, hs, sy1, sx2, sy2, Bool.false_eq_true, Bool.true_eq_false, eq_self_iff_true,
      true_and, and_true, false_and, and_false, or_false, false_or] at ck
    omega
  have F3 : ∀ k : Fin (n + 3), hlSign σ k = true →
      (k.val ≤ (hlLabel σ a1).val ↔ k.val < (hlLabel σ b2).val) := by
    intro k hk
    have := k.isLt
    by_cases hk0 : k.val = 0
    · omega
    by_cases hkN : k.val = n + 2
    · omega
    have ck := comp k (by omega) (by omega)
    rw [S_mem σ a1 b1 k h1, S_mem σ a2 b2 k h2] at ck
    simp only [hk, hs, sy1, sx2, sy2, Bool.false_eq_true, Bool.true_eq_false, eq_self_iff_true,
      true_and, and_true, false_and, and_false, or_false, false_or] at ck
    omega
  have hx2y1 : (hlLabel σ a2).val < (hlLabel σ b1).val := by
    have := F2 _ sx2; omega
  have hx1y2 : (hlLabel σ a1).val < (hlLabel σ b2).val := by
    have := F3 _ hs; omega
  have nogap : ∀ r : ℕ, r < n + 3 → ¬ ((hlLabel σ a1).val < r ∧ (hlLabel σ a2).val < r ∧
      r < (hlLabel σ b1).val ∧ r < (hlLabel σ b2).val) := by
    rintro r hr ⟨k1, k2, k3, k4⟩
    rcases hk : hlSign σ ⟨r, hr⟩ with _ | _
    · have := F2 _ hk; dsimp only at this; omega
    · have := F3 _ hk; dsimp only at this; omega
  have Seq : ∀ j : Fin n, (hlLabel σ a1).val ≤ j.val + 1 → (hlLabel σ a2).val ≤ j.val + 1 →
      j.val + 2 ≤ (hlLabel σ b1).val → j.val + 2 ≤ (hlLabel σ b2).val →
      (hlS σ s(a1, b1) = Finset.univ.filter
              (fun k : Fin (n + 3) => 1 ≤ k.val ∧ k.val ≤ j.val + 1) ∧
            hlS σ s(a2, b2) = Finset.univ.filter
              (fun k : Fin (n + 3) => j.val + 2 ≤ k.val ∧ k.val ≤ n + 1)) := by
    intro j hj1 hj2 hj3 hj4
    have hj := j.isLt
    constructor
    · ext k
      rw [S_mem σ a1 b1 k h1]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hk : hlSign σ k with _ | _
      · have := F2 k hk
        simp only [hs, sy1, Bool.false_eq_true, Bool.true_eq_false, and_true, and_false,
          or_false, true_and] 
        omega
      · have := F3 k hk
        simp only [hs, sy1, Bool.false_eq_true, Bool.true_eq_false, and_true, and_false,
          or_false, true_and]
        omega
    · ext k
      rw [S_mem σ a2 b2 k h2]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hk : hlSign σ k with _ | _
      · have := F2 k hk
        simp only [sx2, sy2, Bool.false_eq_true, Bool.true_eq_false, and_true, and_false,
          false_or, true_and]
        omega
      · have := F3 k hk
        simp only [sx2, sy2, Bool.false_eq_true, Bool.true_eq_false, and_true, and_false,
          false_or, true_and]
        omega
  -- positions and crossing
  have pa2 := lo_of σ a2 sx2
  have pb1 := lo_of σ b1 sy1
  have pa1 := hi_of σ a1 hs
  have pb2 := hi_of σ b2 sy2
  have q1 : b1.val = a2.val + 1 := by
    have hlt : a2.val < b1.val :=
      (pos_lt_iff σ a2 b1).2 (Or.inr (Or.inl ⟨sx2, sy1, Fin.lt_def.2 hx2y1⟩))
    by_contra h
    obtain ⟨p, hp1, hp2, hp3⟩ := mid_lower σ a2 b1 sy1 (by omega)
    have := F2 _ hp3
    rw [Fin.lt_def] at hp1 hp2
    omega
  have q2 : a1.val = b2.val + 1 := by
    have hlt : b2.val < a1.val :=
      (pos_lt_iff σ b2 a1).2 (Or.inr (Or.inr ⟨sy2, hs, Fin.lt_def.2 hx1y2⟩))
    by_contra h
    obtain ⟨p, hp1, hp2, hp3⟩ := mid_upper σ b2 a1 sy2 (by omega)
    have := F3 _ hp3
    rw [Fin.lt_def] at hp1 hp2
    omega
  have hcross : Crosses s(a1, b1) s(a2, b2) := by
    refine ⟨b1, a1, b2, a2, Sym2.eq_swap, Sym2.eq_swap, ?_⟩
    have := a1.isLt
    rw [cdist_of_le b1 b2 (by omega), cdist_of_le b1 a1 (by omega), cdist_of_gt b1 a2 (by omega)]
    omega
  have hxx : (hlLabel σ a1).val ≠ (hlLabel σ a2).val := fun h => by
    have := congrArg (hlSign σ) (Fin.ext h); rw [hs, sx2] at this; simp at this
  have hyy : (hlLabel σ b1).val ≠ (hlLabel σ b2).val := fun h => by
    have := congrArg (hlSign σ) (Fin.ext h); rw [sy1, sy2] at this; simp at this
  -- I/K values
  have IlowA : ∀ m : ℕ, m = (hlLabel σ a2).val → (hlLabel σ a1).val < m →
      hlI σ m = (hlLabel σ a1).val := by
    intro m hm hlt
    refine hlI_eq σ m (hlLabel σ a1) (hlLabel σ a2) hm.symm hlt (by rw [hs, sx2]; simp) ?_
    intro r hr1 hr2
    rw [sx2]
    rcases hr : hlSign σ r with _ | _
    · rfl
    · have := F3 r hr; omega
  have IupA : ∀ m : ℕ, m = (hlLabel σ a1).val → (hlLabel σ a2).val < m →
      hlI σ m = (hlLabel σ a2).val := by
    intro m hm hlt
    refine hlI_eq σ m (hlLabel σ a2) (hlLabel σ a1) hm.symm hlt (by rw [hs, sx2]; simp) ?_
    intro r hr1 hr2
    rw [hs]
    rcases hr : hlSign σ r with _ | _
    · have := F2 r hr; omega
    · rfl
  have KlowB : ∀ m : ℕ, m + 1 = (hlLabel σ b1).val → (hlLabel σ b1).val < (hlLabel σ b2).val →
      hlK σ m = (hlLabel σ b2).val := by
    intro m hm hlt
    refine hlK_eq σ m (hlLabel σ b2) (hlLabel σ b1) hm.symm (by omega) (by rw [sy1, sy2]; simp) ?_
    intro r hr1 hr2
    rw [sy1]
    rcases hr : hlSign σ r with _ | _
    · rfl
    · have := F3 r hr; omega
  have KupB : ∀ m : ℕ, m + 1 = (hlLabel σ b2).val → (hlLabel σ b2).val < (hlLabel σ b1).val →
      hlK σ m = (hlLabel σ b1).val := by
    intro m hm hlt
    refine hlK_eq σ m (hlLabel σ b1) (hlLabel σ b2) hm.symm (by omega) (by rw [sy1, sy2]; simp) ?_
    intro r hr1 hr2
    rw [sy2]
    rcases hr : hlSign σ r with _ | _
    · have := F2 r hr; omega
    · rfl
  rcases lt_or_gt_of_ne hxx with hx | hx <;> rcases lt_or_gt_of_ne hyy with hy | hy
  · -- x1 < x2, y1 < y2
    have e : (hlLabel σ a2).val + 1 = (hlLabel σ b1).val := by
      by_contra h; exact nogap ((hlLabel σ a2).val + 1) (by omega) ⟨by omega, by omega, by omega, by omega⟩
    obtain ⟨j, hj⟩ : ∃ j : Fin n, j.val + 1 = (hlLabel σ a2).val :=
      ⟨⟨(hlLabel σ a2).val - 1, by omega⟩, by show (hlLabel σ a2).val - 1 + 1 = _; omega⟩
    refine ⟨j, a1, a2, b1, b2, (IlowA _ hj (by omega)).symm, by omega, by omega,
      (KlowB _ (by omega) hy).symm, hcross,
      vA a1 b1 a2 b2,
      Seq j (by omega) (by omega) (by omega) (by omega)⟩
  · -- x1 < x2, y2 < y1
    have e : (hlLabel σ a2).val + 1 = (hlLabel σ b2).val := by
      by_contra h; exact nogap ((hlLabel σ a2).val + 1) (by omega) ⟨by omega, by omega, by omega, by omega⟩
    obtain ⟨j, hj⟩ : ∃ j : Fin n, j.val + 1 = (hlLabel σ a2).val :=
      ⟨⟨(hlLabel σ a2).val - 1, by omega⟩, by show (hlLabel σ a2).val - 1 + 1 = _; omega⟩
    refine ⟨j, a1, a2, b2, b1, (IlowA _ hj (by omega)).symm, by omega, by omega,
      (KupB _ (by omega) hy).symm, hcross,
      vB a1 b1 a2 b2,
      Seq j (by omega) (by omega) (by omega) (by omega)⟩
  · -- x2 < x1, y1 < y2
    have e : (hlLabel σ a1).val + 1 = (hlLabel σ b1).val := by
      by_contra h; exact nogap ((hlLabel σ a1).val + 1) (by omega) ⟨by omega, by omega, by omega, by omega⟩
    obtain ⟨j, hj⟩ : ∃ j : Fin n, j.val + 1 = (hlLabel σ a1).val :=
      ⟨⟨(hlLabel σ a1).val - 1, by omega⟩, by show (hlLabel σ a1).val - 1 + 1 = _; omega⟩
    refine ⟨j, a2, a1, b1, b2, (IupA _ hj (by omega)).symm, by omega, by omega,
      (KlowB _ (by omega) hy).symm, hcross,
      vC a1 b1 a2 b2,
      Seq j (by omega) (by omega) (by omega) (by omega)⟩
  · -- x2 < x1, y2 < y1
    have e : (hlLabel σ a1).val + 1 = (hlLabel σ b2).val := by
      by_contra h; exact nogap ((hlLabel σ a1).val + 1) (by omega) ⟨by omega, by omega, by omega, by omega⟩
    obtain ⟨j, hj⟩ : ∃ j : Fin n, j.val + 1 = (hlLabel σ a1).val :=
      ⟨⟨(hlLabel σ a1).val - 1, by omega⟩, by show (hlLabel σ a1).val - 1 + 1 = _; omega⟩
    refine ⟨j, a2, a1, b2, b1, (IupA _ hj (by omega)).symm, by omega, by omega,
      (KupB _ (by omega) hy).symm, hcross,
      vD a1 b1 a2 b2,
      Seq j (by omega) (by omega) (by omega) (by omega)⟩

lemma forward (e f : Sym2 (Fin (n + 3))) (he : IsDiagonal e) (hf : IsDiagonal f)
    (hop : Opposite (hlVec σ e) (hlVec σ f)) :
    ∃ j : Fin n, ∃ a b c d : Fin (n + 3),
        (hlLabel σ a).val = hlI σ (j.val + 1) ∧
        (hlLabel σ b).val = j.val + 1 ∧
        (hlLabel σ c).val = j.val + 2 ∧
        (hlLabel σ d).val = hlK σ (j.val + 1) ∧
        Crosses e f ∧
        (∀ p : Fin (n + 3), (p ∈ e ∨ p ∈ f) ↔
          (p = a ∨ p = b ∨ p = c ∨ p = d)) ∧
        ((hlS σ e = Finset.univ.filter
              (fun k : Fin (n + 3) => 1 ≤ k.val ∧ k.val ≤ j.val + 1) ∧
            hlS σ f = Finset.univ.filter
              (fun k : Fin (n + 3) => j.val + 2 ≤ k.val ∧ k.val ≤ n + 1)) ∨
          (hlS σ f = Finset.univ.filter
              (fun k : Fin (n + 3) => 1 ≤ k.val ∧ k.val ≤ j.val + 1) ∧
            hlS σ e = Finset.univ.filter
              (fun k : Fin (n + 3) => j.val + 2 ≤ k.val ∧ k.val ≤ n + 1))) := by
  obtain ⟨a1, b1, rfl, h1⟩ := ordered σ e he
  obtain ⟨a2, b2, rfl, h2⟩ := ordered σ f hf
  obtain ⟨c, hc, hv⟩ := hop
  have comp := comp_of_opp σ a1 b1 a2 b2 he h1 c hc hv
  by_cases hs : hlSign σ (hlLabel σ a1) = true
  · obtain ⟨j, a, b, c', d, i1, i2, i3, i4, hx, hp, hS⟩ := core σ a1 b1 a2 b2 he hf h1 h2 comp hs
    exact ⟨j, a, b, c', d, i1, i2, i3, i4, hx, hp, Or.inl hS⟩
  · have comp' : ∀ k : Fin (n + 3), 1 ≤ k.val → k.val ≤ n + 1 →
        (k ∈ hlS σ s(a2, b2) ↔ k ∉ hlS σ s(a1, b1)) := fun k k1 k2 =>
      ⟨fun h h1 => (comp k k1 k2).1 h1 h, fun h => by
        by_contra h2; exact h ((comp k k1 k2).2 h2)⟩
    have hs2 : hlSign σ (hlLabel σ a2) = true := by
      have := comp ⟨1, by omega⟩ le_rfl (by show 1 ≤ n + 1; omega)
      rw [one_mem σ a1 b1 he h1, one_mem σ a2 b2 hf h2] at this
      simpa [hs] using this
    obtain ⟨j, a, b, c', d, i1, i2, i3, i4, hx, hp, hS⟩ :=
      core σ a2 b2 a1 b1 hf he h2 h1 comp' hs2
    exact ⟨j, a, b, c', d, i1, i2, i3, i4, crosses_symm _ _ hx,
      fun p => or_comm.trans (hp p), Or.inr hS⟩

lemma backward (e f : Sym2 (Fin (n + 3))) (j : Fin n)
    (hS : (hlS σ e = Finset.univ.filter
              (fun k : Fin (n + 3) => 1 ≤ k.val ∧ k.val ≤ j.val + 1) ∧
            hlS σ f = Finset.univ.filter
              (fun k : Fin (n + 3) => j.val + 2 ≤ k.val ∧ k.val ≤ n + 1)) ∨
          (hlS σ f = Finset.univ.filter
              (fun k : Fin (n + 3) => 1 ≤ k.val ∧ k.val ≤ j.val + 1) ∧
            hlS σ e = Finset.univ.filter
              (fun k : Fin (n + 3) => j.val + 2 ≤ k.val ∧ k.val ≤ n + 1))) :
    Opposite (hlVec σ e) (hlVec σ f) := by
  have hj := j.isLt
  refine ⟨1, one_pos, ?_⟩
  funext k
  have hk := k.isLt
  simp only [hlVec, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, one_mul]
  rcases hS with ⟨he, hf⟩ | ⟨hf, he⟩ <;> rw [he, hf] <;>
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_mk] <;>
    split_ifs <;> first | (exfalso; omega) | norm_num

end P47

end Phl

open ChvatalArtGallery.FanPartition AssocRealizations.TypesMeet in
theorem solution (n : ℕ) (σ : Fin (n - 1) → Bool)
    (e f : Sym2 (Fin (n + 3))) (he : IsDiagonal e) (hf : IsDiagonal f)
    (hne : e ≠ f) :
    Opposite (hlVec σ e) (hlVec σ f) ↔
      ∃ j : Fin n, ∃ a b c d : Fin (n + 3),
        (hlLabel σ a).val = hlI σ (j.val + 1) ∧
        (hlLabel σ b).val = j.val + 1 ∧
        (hlLabel σ c).val = j.val + 2 ∧
        (hlLabel σ d).val = hlK σ (j.val + 1) ∧
        Crosses e f ∧
        (∀ p : Fin (n + 3), (p ∈ e ∨ p ∈ f) ↔
          (p = a ∨ p = b ∨ p = c ∨ p = d)) ∧
        ((hlS σ e = Finset.univ.filter
              (fun k : Fin (n + 3) => 1 ≤ k.val ∧ k.val ≤ j.val + 1) ∧
            hlS σ f = Finset.univ.filter
              (fun k : Fin (n + 3) => j.val + 2 ≤ k.val ∧ k.val ≤ n + 1)) ∨
          (hlS σ f = Finset.univ.filter
              (fun k : Fin (n + 3) => 1 ≤ k.val ∧ k.val ≤ j.val + 1) ∧
            hlS σ e = Finset.univ.filter
              (fun k : Fin (n + 3) => j.val + 2 ≤ k.val ∧ k.val ≤ n + 1))) := by
  constructor
  · exact Phl.forward σ e f he hf
  · rintro ⟨j, -, -, -, -, -, -, -, -, -, -, hS⟩
    exact Phl.backward σ e f j hS
