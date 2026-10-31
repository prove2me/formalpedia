-- Prove2me | solution 1 for AssocRealizations.TypesMeet.three_properties_snake
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-30T13:10:49.744662+00:00
-- url     : https://prove2.me/submissions/b57708f6-2032-4ac4-b8ba-b144cfe3ad17

import Mathlib
import Definitions.Def_AssocRealizations_TypesMeet_Setting

set_option autoImplicit false

open ChvatalArtGallery.FanPartition

namespace Pfd4

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

lemma isTri_image {N : ℕ} [NeZero N] (r : Fin N) (refl : Bool) (T : Finset (Sym2 (Fin N)))
    (hT : IsTriangulation N T) : IsTriangulation N (T.image (Sym2.map (dihedral r refl))) := by
  obtain ⟨h3, hd, hc, hm⟩ := hT
  obtain ⟨r', refl', hr⟩ := dihInv_eq r refl
  refine ⟨h3, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.1 he
    exact diagonal_dihedral r refl e' (hd e' he')
  · intro e he f hf
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.1 he
    obtain ⟨f', hf', rfl⟩ := Finset.mem_image.1 hf
    rw [crosses_dihedral_iff]; exact hc e' he' f' hf'
  · intro e he hno
    have hd' : IsDiagonal (Sym2.map (dihInv r refl) e) := by
      rw [hr]; exact diagonal_dihedral r' refl' e he
    have hmem : Sym2.map (dihInv r refl) e ∈ T := by
      apply hm _ hd'
      intro f hf hcr
      apply hno _ (Finset.mem_image_of_mem _ hf)
      have := (crosses_dihedral_iff r refl _ _).2 hcr
      rwa [map_dihedral_map_inv] at this
    exact Finset.mem_image.2 ⟨_, hmem, map_dihedral_map_inv r refl e⟩

lemma apex {N : ℕ} [NeZero N] (T : Finset (Sym2 (Fin N)))
    (hT : IsTriangulation N T) (a b : Fin N) (hab : 2 ≤ cdist a b)
    (hno : ∀ g ∈ T, ¬ Crosses s(a, b) g) :
    ∃ p : Fin N, 0 < cdist a p ∧ cdist a p < cdist a b ∧
      (cdist a p = 1 ∨ s(a, p) ∈ T) ∧ (cdist a b - cdist a p = 1 ∨ s(p, b) ∈ T) := by
  classical
  have hN := hT.1
  have hbN := cdist_lt a b
  have h00 : cdist a a = 0 := (cdist_eq_zero a a).2 rfl
  let S := Finset.univ.filter (fun p : Fin N => 0 < cdist a p ∧ cdist a p < cdist a b ∧
      (cdist a p = 1 ∨ s(a, p) ∈ T))
  have h1 : cdist a (a + 1) = 1 := by
    rw [cdist_add_self, Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  have hne : S.Nonempty := ⟨a + 1, by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨by omega, by omega, Or.inl h1⟩⟩
  obtain ⟨p, hpS, hpmax⟩ := S.exists_max_image (fun p => cdist a p) hne
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hpS
  obtain ⟨hp0, hpb, hpe⟩ := hpS
  refine ⟨p, hp0, hpb, hpe, ?_⟩
  by_contra hcon
  push_neg at hcon
  obtain ⟨hpb1, hpbT⟩ := hcon
  have hcpb : cdist p b = cdist a b - cdist a p := cdist_tri a b p (by omega)
  have hpne : p ≠ b := by intro h; subst h; omega
  have hbp : cdist b p = N - cdist p b := cdist_swap p b hpne
  have hdiag : IsDiagonal s(p, b) := by
    intro x y hxy
    rcases Sym2.eq_iff.1 hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hpne, by omega, by omega⟩
    · exact ⟨fun h => hpne h.symm, by omega, by omega⟩
  obtain ⟨g, hgT, hcr⟩ : ∃ g ∈ T, Crosses s(p, b) g := by
    by_contra h
    push_neg at h
    exact hpbT (hT.2.2.2 _ hdiag h)
  have key : ∀ w z : Fin N, s(w, z) ∈ T → cdist a w = 0 → cdist a p < cdist a z →
      cdist a z < cdist a b → False := by
    intro w z hT' hw hz1 hz2
    have hwa : a = w := (cdist_eq_zero a w).1 hw
    subst hwa
    have hzS : z ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by omega, hz2, Or.inr hT'⟩
    have := hpmax z hzS
    omega
  induction g using Sym2.ind with
  | _ u v =>
  have hI := (crosses_pos a p b u v).1 hcr
  have h2 : ¬ Inter 0 (cdist a b) (cdist a u) (cdist a v) := by
    intro h; rw [← h00] at h; exact hno _ hgT ((crosses_pos a a b u v).2 h)
  have h3 : cdist a p = 1 ∨ ¬ Inter 0 (cdist a p) (cdist a u) (cdist a v) := by
    rcases hpe with h | h
    · exact Or.inl h
    · right; intro hh; rw [← h00] at hh
      exact hT.2.2.1 _ h _ hgT ((crosses_pos a a p u v).2 hh)
  have hu := cdist_lt a u
  have hv := cdist_lt a v
  -- orient the crossing
  have hcase : (cdist a p < cdist a u ∧ cdist a u < cdist a b ∧
        (cdist a v < cdist a p ∨ cdist a b < cdist a v)) ∨
      (cdist a p < cdist a v ∧ cdist a v < cdist a b ∧
        (cdist a u < cdist a p ∨ cdist a b < cdist a u)) := by
    unfold Inter at hI; omega
  rcases hcase with ⟨c1, c2, c3⟩ | ⟨c1, c2, c3⟩
  · rcases (show cdist a v = 0 ∨ (0 < cdist a v ∧ cdist a v < cdist a p) ∨
        cdist a b < cdist a v by omega) with c | c | c
    · exact key v u (by rw [Sym2.eq_swap]; exact hgT) c c1 c2
    · rcases h3 with h | h
      · omega
      · exact h (by unfold Inter; omega)
    · exact h2 (by unfold Inter; omega)
  · rcases (show cdist a u = 0 ∨ (0 < cdist a u ∧ cdist a u < cdist a p) ∨
        cdist a b < cdist a u by omega) with c | c | c
    · exact key u v hgT c c1 c2
    · rcases h3 with h | h
      · omega
      · exact h (by unfold Inter; omega)
    · exact h2 (by unfold Inter; omega)

/-! ## Part C: the zigzag walk along a strip -/

open Fin.NatCast

def V {N : ℕ} [NeZero N] (o : Fin N) (k : ℕ) : Fin N := o + (k : Fin N)

lemma cdist_V {N : ℕ} [NeZero N] (o : Fin N) (k : ℕ) (hk : k < N) : cdist o (V o k) = k := by
  unfold V; rw [cdist_add_self, Fin.val_natCast, Nat.mod_eq_of_lt hk]

lemma V_inj {N : ℕ} [NeZero N] (o : Fin N) {a b : ℕ} (ha : a < N) (hb : b < N)
    (h : V o a = V o b) : a = b := by
  have h1 := cdist_V o a ha
  rw [h, cdist_V o b hb] at h1
  exact h1.symm

lemma V_of {N : ℕ} [NeZero N] (o x : Fin N) : V o (cdist o x) = x :=
  cdist_inj o _ _ (cdist_V o _ (cdist_lt o x))

lemma cdist_VV {N : ℕ} [NeZero N] (o : Fin N) (a b : ℕ) (ha : a < N) (hb : b < N) :
    cdist (V o a) (V o b) = if a ≤ b then b - a else b + N - a := by
  rw [cdist_via o, cdist_V o a ha, cdist_V o b hb]

lemma bdry_V {N : ℕ} [NeZero N] (o : Fin N) (a : ℕ) (h : a + 1 < N) :
    IsBoundaryEdge s(V o a, V o (a + 1)) :=
  ⟨_, _, rfl, by rw [cdist_VV o a (a + 1) (by omega) h, if_pos (by omega)]; omega⟩

lemma bdry_cases {N : ℕ} [NeZero N] (x y : Fin N) (h : IsBoundaryEdge s(x, y)) :
    cdist x y = 1 ∨ cdist y x = 1 := by
  obtain ⟨u, v, he, h1⟩ := h
  rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl h1
  · exact Or.inr h1

lemma bdry_VV {N : ℕ} [NeZero N] (o : Fin N) (a b : ℕ) (ha : a < N) (hb : b < N)
    (h : IsBoundaryEdge s(V o a, V o b)) :
    b = a + 1 ∨ a = b + 1 ∨ (a = 0 ∧ b = N - 1) ∨ (b = 0 ∧ a = N - 1) := by
  rcases bdry_cases _ _ h with h | h
  · rw [cdist_VV o a b ha hb] at h; split_ifs at h <;> omega
  · rw [cdist_VV o b a hb ha] at h; split_ifs at h <;> omega

lemma edge_nocross {N : ℕ} [NeZero N] (T : Finset (Sym2 (Fin N))) (hT : IsTriangulation N T)
    (a b : Fin N) (h : IsEdge T s(a, b)) : ∀ g ∈ T, ¬ Crosses s(a, b) g := by
  intro g hg hc
  rcases h with h | h
  · induction g using Sym2.ind with
    | _ u w =>
    rw [crosses_pos a] at hc
    have h0 : cdist a a = 0 := (cdist_eq_zero a a).2 rfl
    have l1 := cdist_lt a b
    have l2 := cdist_lt a u
    have l3 := cdist_lt a w
    have hb := bdry_cases a b h
    have hab : a ≠ b := by rintro rfl; omega
    rw [cdist_swap a b hab] at hb
    rw [h0] at hc
    unfold Inter at hc
    omega
  · exact hT.2.2.1 _ h _ hg hc

lemma mk_tri {N : ℕ} (T : Finset (Sym2 (Fin N))) (x y z : Fin N) (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) (e1 : IsEdge T s(x, y)) (e2 : IsEdge T s(x, z)) (e3 : IsEdge T s(y, z)) :
    ({x, y, z} : Finset (Fin N)) ∈ triangles N T := by
  simp only [triangles, Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
  refine ⟨Finset.card_eq_three.2 ⟨x, y, z, hxy, hxz, hyz, rfl⟩, ?_⟩
  intro a ha b hb hab
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  all_goals first
    | exact absurd rfl hab
    | assumption
    | (rw [Sym2.eq_swap]; assumption)

lemma hpath_step {N : ℕ} [NeZero N] (T : Finset (Sym2 (Fin N))) (sg : Fin N → Bool)
    (hpath : ∀ t ∈ triangles N T, ∃ a ∈ t, ∃ b ∈ t, a ≠ b ∧
      IsBoundaryEdge s(a, b) ∧ sg a = sg b)
    (o : Fin N) (a b P : ℕ) (haP : a < P) (hPb : P < b) (hb : b < N)
    (e1 : IsEdge T s(V o a, V o b)) (e2 : IsEdge T s(V o a, V o P))
    (e3 : IsEdge T s(V o P, V o b)) (hs : sg (V o a) ≠ sg (V o b)) :
    (P = a + 1 ∧ sg (V o P) = sg (V o a)) ∨ (P = b - 1 ∧ sg (V o P) = sg (V o b)) := by
  have dab : V o a ≠ V o b := fun h => by have := V_inj o (by omega) hb h; omega
  have daP : V o a ≠ V o P := fun h => by have := V_inj o (by omega) (by omega) h; omega
  have dbP : V o b ≠ V o P := fun h => by have := V_inj o hb (by omega) h; omega
  have ht := mk_tri T (V o a) (V o b) (V o P) dab daP dbP e1 e2 (by rw [Sym2.eq_swap]; exact e3)
  obtain ⟨u, hu, w, hw, huw, hbd, hsg⟩ := hpath _ ht
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hw
  rcases hu with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl
  · exact absurd rfl huw
  · exact absurd hsg hs
  · have := bdry_VV o a P (by omega) (by omega) hbd; left; exact ⟨by omega, hsg.symm⟩
  · exact absurd hsg.symm hs
  · exact absurd rfl huw
  · have := bdry_VV o b P hb (by omega) hbd; right; exact ⟨by omega, hsg.symm⟩
  · have := bdry_VV o P a (by omega) (by omega) hbd; left; exact ⟨by omega, hsg⟩
  · have := bdry_VV o P b (by omega) hb hbd; right; exact ⟨by omega, hsg⟩
  · exact absurd rfl huw

lemma apex_step {N : ℕ} [NeZero N] (T : Finset (Sym2 (Fin N))) (hT : IsTriangulation N T)
    (o : Fin N) (a b : ℕ) (hab : a + 2 ≤ b) (hb : b < N) (e : IsEdge T s(V o a, V o b)) :
    ∃ P, a < P ∧ P < b ∧ IsEdge T s(V o a, V o P) ∧ IsEdge T s(V o P, V o b) := by
  have hd : cdist (V o a) (V o b) = b - a := by
    rw [cdist_VV o a b (by omega) hb, if_pos (by omega)]
  obtain ⟨p, h1, h2, h3, h4⟩ := apex T hT (V o a) (V o b) (by omega) (edge_nocross T hT _ _ e)
  obtain ⟨P, hPN, rfl⟩ : ∃ P, P < N ∧ p = V o P := ⟨cdist o p, cdist_lt o p, (V_of o p).symm⟩
  have hc : cdist (V o a) (V o P) = P - a := by
    rw [cdist_VV o a P (by omega) hPN] at h1 h2 ⊢
    rw [hd] at h2
    split_ifs at h1 h2 ⊢ <;> omega
  rw [hc] at h1 h2 h3 h4
  rw [hd] at h2 h4
  refine ⟨P, by omega, by omega, ?_, ?_⟩
  · rcases h3 with h3 | h3
    · left; exact ⟨_, _, rfl, by rw [hc]; exact h3⟩
    · right; exact h3
  · rcases h4 with h4 | h4
    · left; exact ⟨_, _, rfl, by rw [cdist_VV o P b hPN hb, if_pos (by omega)]; omega⟩
    · right; exact h4

def I (ε : Bool) (k : ℕ) : ℕ := if ε then (k + 1) / 2 else k / 2

def J (N : ℕ) (ε : Bool) (k : ℕ) : ℕ := N - 1 - (if ε then k / 2 else (k + 1) / 2)

lemma IJ0 (N : ℕ) (ε : Bool) : I ε 0 = 0 ∧ J N ε 0 = N - 1 := by
  cases ε <;> simp [I, J]

lemma IJ_gap (N : ℕ) (ε : Bool) (k : ℕ) (hk : k ≤ N - 1) : J N ε k = I ε k + (N - 1 - k) := by
  cases ε <;> simp [I, J] <;> omega

lemma J_lt (N : ℕ) (ε : Bool) (k : ℕ) (hN : 1 ≤ N) : J N ε k < N := by
  unfold J; omega

lemma step1 (N : ℕ) (ε : Bool) (k : ℕ) (hk : k + 1 ≤ N - 1) :
    (I ε (k + 1) = I ε k + 1 ∧ J N ε (k + 1) = J N ε k) ∨
    (I ε (k + 1) = I ε k ∧ J N ε (k + 1) + 1 = J N ε k) := by
  cases ε <;> simp [I, J] <;> omega

lemma step_cases (N : ℕ) (ε : Bool) (k : ℕ) (hk : k + 2 ≤ N - 1) :
    (I ε (k + 1) = I ε k + 1 ∧ J N ε (k + 1) = J N ε k ∧
      I ε (k + 1 + 1) = I ε (k + 1) ∧ J N ε (k + 1 + 1) + 1 = J N ε (k + 1)) ∨
    (I ε (k + 1) = I ε k ∧ J N ε (k + 1) + 1 = J N ε k ∧
      I ε (k + 1 + 1) = I ε (k + 1) + 1 ∧ J N ε (k + 1 + 1) = J N ε (k + 1)) := by
  cases ε <;> simp [I, J] <;> omega

def E {N : ℕ} [NeZero N] (T : Finset (Sym2 (Fin N))) (sg : Fin N → Bool) (o : Fin N)
    (i j : ℕ) : Prop :=
  IsEdge T s(V o i, V o j) ∧ sg (V o i) ≠ sg (V o j)

lemma bool3 {a b c : Bool} (h1 : a ≠ c) (h2 : b ≠ c) : a = b := by
  cases a <;> cases b <;> cases c <;> simp_all

section walk

variable {N : ℕ} [NeZero N] (T : Finset (Sym2 (Fin N))) (sg : Fin N → Bool)

lemma chain_ind (hN : 4 ≤ N) (hT : IsTriangulation N T)
    (hpath : ∀ t ∈ triangles N T, ∃ a ∈ t, ∃ b ∈ t, a ≠ b ∧
      IsBoundaryEdge s(a, b) ∧ sg a = sg b)
    (halt : ¬ ∃ a b c p : Fin N,
      a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ p ≠ a ∧ p ≠ b ∧ p ≠ c ∧
      IsBoundaryEdge s(a, b) ∧ IsBoundaryEdge s(b, c) ∧
      sg a = sg b ∧ sg b = sg c ∧
      ({a, b, p} : Finset (Fin N)) ∈ triangles N T ∧
      ({b, c, p} : Finset (Fin N)) ∈ triangles N T)
    (o : Fin N) (ε : Bool)
    (E0 : E T sg o (I ε 0) (J N ε 0)) (E1 : E T sg o (I ε 1) (J N ε 1)) :
    ∀ k, k + 1 ≤ N - 2 → E T sg o (I ε k) (J N ε k) ∧ E T sg o (I ε (k + 1)) (J N ε (k + 1)) := by
  intro k
  induction k with
  | zero => intro _; exact ⟨E0, E1⟩
  | succ k ih =>
    intro hk
    obtain ⟨Ek, Ek1⟩ := ih (by omega)
    refine ⟨Ek1, ?_⟩
    have gap := IJ_gap N ε (k + 1) (by omega)
    have jl := J_lt N ε (k + 1) (by omega)
    have jl0 := J_lt N ε k (by omega)
    rcases step_cases N ε k (by omega) with ⟨A1, A2, A3, A4⟩ | ⟨A1, A2, A3, A4⟩
    · generalize I ε k = i0 at *
      generalize I ε (k + 1) = i at *
      generalize I ε (k + 1 + 1) = i2 at *
      generalize J N ε k = j0 at *
      generalize J N ε (k + 1) = j at *
      generalize J N ε (k + 1 + 1) = j2 at *
      subst i
      subst i2
      subst j
      subst j0
      unfold E at Ek Ek1 ⊢
      obtain ⟨P, h1, h2, ea, eb⟩ := apex_step T hT o (i0 + 1) (j2 + 1) (by omega) (by omega) Ek1.1
      rcases hpath_step T sg hpath o (i0 + 1) (j2 + 1) P h1 h2 (by omega) Ek1.1 ea eb Ek1.2 with
        ⟨hP, hsP⟩ | ⟨hP, hsP⟩
      · exfalso
        subst hP
        apply halt
        have d1 : V o i0 ≠ V o (i0 + 1) := fun h => by have := V_inj o (by omega) (by omega) h; omega
        have d2 : V o (i0 + 1) ≠ V o (i0 + 1 + 1) := fun h => by
          have := V_inj o (by omega) (by omega) h; omega
        have d3 : V o i0 ≠ V o (i0 + 1 + 1) := fun h => by
          have := V_inj o (by omega) (by omega) h; omega
        have d4 : V o (j2 + 1) ≠ V o i0 := fun h => by have := V_inj o (by omega) (by omega) h; omega
        have d5 : V o (j2 + 1) ≠ V o (i0 + 1) := fun h => by
          have := V_inj o (by omega) (by omega) h; omega
        have d6 : V o (j2 + 1) ≠ V o (i0 + 1 + 1) := fun h => by
          have := V_inj o (by omega) (by omega) h; omega
        refine ⟨V o i0, V o (i0 + 1), V o (i0 + 1 + 1), V o (j2 + 1), d1, d2, d3, d4, d5, d6,
          bdry_V o i0 (by omega), bdry_V o (i0 + 1) (by omega), bool3 Ek.2 Ek1.2, hsP.symm, ?_, ?_⟩
        · exact mk_tri T _ _ _ d1 (Ne.symm d4) (Ne.symm d5) (Or.inl (bdry_V o i0 (by omega))) Ek.1 Ek1.1
        · exact mk_tri T _ _ _ d2 (Ne.symm d5) (Ne.symm d6) ea Ek1.1 eb
      · obtain rfl : P = j2 := by omega
        exact ⟨ea, by rw [hsP]; exact Ek1.2⟩
    · generalize I ε k = i0 at *
      generalize I ε (k + 1) = i at *
      generalize I ε (k + 1 + 1) = i2 at *
      generalize J N ε k = j0 at *
      generalize J N ε (k + 1) = j at *
      generalize J N ε (k + 1 + 1) = j2 at *
      subst i
      subst i2
      subst j2
      subst j0
      unfold E at Ek Ek1 ⊢
      obtain ⟨P, h1, h2, ea, eb⟩ := apex_step T hT o i0 j (by omega) (by omega) Ek1.1
      rcases hpath_step T sg hpath o i0 j P h1 h2 (by omega) Ek1.1 ea eb Ek1.2 with
        ⟨hP, hsP⟩ | ⟨hP, hsP⟩
      · subst hP
        exact ⟨eb, by rw [hsP]; exact Ek1.2⟩
      · exfalso
        obtain rfl : j = P + 1 := by omega
        apply halt
        have d1 : V o (P + 1 + 1) ≠ V o (P + 1) := fun h => by
          have := V_inj o (by omega) (by omega) h; omega
        have d2 : V o (P + 1) ≠ V o P := fun h => by have := V_inj o (by omega) (by omega) h; omega
        have d3 : V o (P + 1 + 1) ≠ V o P := fun h => by
          have := V_inj o (by omega) (by omega) h; omega
        have d4 : V o i0 ≠ V o (P + 1 + 1) := fun h => by
          have := V_inj o (by omega) (by omega) h; omega
        have d5 : V o i0 ≠ V o (P + 1) := fun h => by have := V_inj o (by omega) (by omega) h; omega
        have d6 : V o i0 ≠ V o P := fun h => by have := V_inj o (by omega) (by omega) h; omega
        have b1 : IsBoundaryEdge s(V o (P + 1 + 1), V o (P + 1)) := by
          rw [Sym2.eq_swap]; exact bdry_V o (P + 1) (by omega)
        have b2 : IsBoundaryEdge s(V o (P + 1), V o P) := by
          rw [Sym2.eq_swap]; exact bdry_V o P (by omega)
        refine ⟨V o (P + 1 + 1), V o (P + 1), V o P, V o i0, d1, d2, d3, d4, d5, d6,
          b1, b2, bool3 (Ne.symm Ek.2) (Ne.symm Ek1.2), hsP.symm, ?_, ?_⟩
        · exact mk_tri T _ _ _ d1 (Ne.symm d4) (Ne.symm d5) (Or.inl b1)
            (by rw [Sym2.eq_swap]; exact Ek.1) (by rw [Sym2.eq_swap]; exact Ek1.1)
        · exact mk_tri T _ _ _ d2 (Ne.symm d5) (Ne.symm d6) (by rw [Sym2.eq_swap]; exact eb)
            (by rw [Sym2.eq_swap]; exact Ek1.1) (by rw [Sym2.eq_swap]; exact ea)

lemma interF (i j X Y : ℕ) (h : i ≤ X) (h1 : ¬ i + 1 ≤ X) (hY : Y ≠ X + 1) (hXY : X < Y)
    (hYj : Y < j) : Inter (i + 1) j X Y := by
  unfold Inter; omega

lemma interU (i j X Y : ℕ) (hY : Y = j) (hX : i < X) (hXY : Y ≠ X + 1) (hXY' : X < Y) :
    Inter i (j - 1) X Y := by
  unfold Inter; omega

lemma mem_Z_of (hN : 4 ≤ N) (hT : IsTriangulation N T) (o : Fin N) (ε : Bool)
    (hE : ∀ k, k ≤ N - 2 → E T sg o (I ε k) (J N ε k))
    (X Y : ℕ) (hXY : X < Y) (hY : Y < N) (hd : Y ≠ X + 1 ∧ ¬ (X = 0 ∧ Y = N - 1))
    (he : s(V o X, V o Y) ∈ T) :
    ∃ k, 1 ≤ k ∧ k ≤ N - 3 ∧ s(V o X, V o Y) = s(V o (I ε k), V o (J N ε k)) := by
  have hX : X < N := by omega
  have claim : ∀ k, k ≤ N - 2 → (∃ k', 1 ≤ k' ∧ k' ≤ N - 3 ∧ X = I ε k' ∧ Y = J N ε k') ∨
      (I ε k ≤ X ∧ Y ≤ J N ε k) := by
    intro k
    induction k with
    | zero => intro _; right; have := IJ0 N ε; omega
    | succ k ih =>
      intro hk
      rcases ih (by omega) with h | ⟨hx, hy⟩
      · exact Or.inl h
      · by_cases heq : X = I ε k ∧ Y = J N ε k
        · left
          have g := IJ0 N ε
          refine ⟨k, ?_, by omega, heq.1, heq.2⟩
          by_contra h0
          have : k = 0 := by omega
          subst this
          omega
        · have gap := IJ_gap N ε k (by omega)
          have gap1 := IJ_gap N ε (k + 1) (by omega)
          have jl := J_lt N ε (k + 1) (by omega)
          have hz := (hE (k + 1) hk).1
          have c1 := cdist_V o (I ε (k + 1)) (by omega)
          have c2 := cdist_V o (J N ε (k + 1)) jl
          have c3 := cdist_V o X hX
          have c4 := cdist_V o Y hY
          rcases step1 N ε k (by omega) with ⟨A1, A2⟩ | ⟨A1, A2⟩
          · by_cases hx1 : I ε k + 1 ≤ X
            · right; omega
            · exfalso
              refine edge_nocross T hT _ _ hz _ he ?_
              rw [crosses_pos o, c1, c2, c3, c4, A1, A2]
              exact interF _ _ X Y hx hx1 hd.1 hXY (by omega)
          · by_cases hy1 : Y + 1 ≤ J N ε k
            · right; omega
            · exfalso
              refine edge_nocross T hT _ _ hz _ he ?_
              have A3 : J N ε (k + 1) = J N ε k - 1 := by omega
              rw [crosses_pos o, c1, c2, c3, c4, A1, A3]
              exact interU _ _ X Y (by omega) (by omega) hd.1 hXY
  rcases claim (N - 2) le_rfl with h | ⟨hx, hy⟩
  · obtain ⟨k, h1, h2, h3, h4⟩ := h
    exact ⟨k, h1, h2, by rw [h3, h4]⟩
  · exfalso
    have := IJ_gap N ε (N - 2) (by omega)
    omega

lemma chain_eq (hN : 4 ≤ N) (hT : IsTriangulation N T) (o : Fin N) (ε : Bool)
    (hE : ∀ k, k ≤ N - 2 → E T sg o (I ε k) (J N ε k)) (e : Sym2 (Fin N)) :
    e ∈ T ↔ ∃ k, 1 ≤ k ∧ k ≤ N - 3 ∧ e = s(V o (I ε k), V o (J N ε k)) := by
  constructor
  · intro he
    induction e using Sym2.ind with
    | _ x y =>
    obtain ⟨X, hX, rfl⟩ : ∃ X, X < N ∧ x = V o X := ⟨_, cdist_lt o x, (V_of o x).symm⟩
    obtain ⟨Y, hY, rfl⟩ : ∃ Y, Y < N ∧ y = V o Y := ⟨_, cdist_lt o y, (V_of o y).symm⟩
    have hd := hT.2.1 _ he (V o X) (V o Y) rfl
    rw [cdist_VV o X Y hX hY, cdist_VV o Y X hY hX] at hd
    obtain ⟨hne, hd1, hd2⟩ := hd
    have hXY : X ≠ Y := fun h => hne (by rw [h])
    rcases Nat.lt_or_gt_of_ne hXY with h | h
    · exact mem_Z_of T sg hN hT o ε hE X Y h hY (by split_ifs at hd1 hd2 <;> omega) he
    · obtain ⟨k, h1, h2, h3⟩ := mem_Z_of T sg hN hT o ε hE Y X h hX
        (by split_ifs at hd1 hd2 <;> omega) (by rw [Sym2.eq_swap]; exact he)
      exact ⟨k, h1, h2, by rw [Sym2.eq_swap]; exact h3⟩
  · rintro ⟨k, h1, h2, rfl⟩
    have Ek := (hE k (by omega)).1
    have gap := IJ_gap N ε k (by omega)
    have jl := J_lt N ε k (by omega)
    rcases Ek with hb | hb
    · exfalso
      have := bdry_VV o _ _ (by omega) jl hb
      omega
    · exact hb

lemma chain (hN : 4 ≤ N) (hT : IsTriangulation N T)
    (hpath : ∀ t ∈ triangles N T, ∃ a ∈ t, ∃ b ∈ t, a ≠ b ∧
      IsBoundaryEdge s(a, b) ∧ sg a = sg b)
    (halt : ¬ ∃ a b c p : Fin N,
      a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ p ≠ a ∧ p ≠ b ∧ p ≠ c ∧
      IsBoundaryEdge s(a, b) ∧ IsBoundaryEdge s(b, c) ∧
      sg a = sg b ∧ sg b = sg c ∧
      ({a, b, p} : Finset (Fin N)) ∈ triangles N T ∧
      ({b, c, p} : Finset (Fin N)) ∈ triangles N T)
    (o : Fin N) (h0 : sg (V o 0) ≠ sg (V o (N - 1))) :
    ∃ ε : Bool, ∀ k, k ≤ N - 2 → E T sg o (I ε k) (J N ε k) := by
  have e0 : IsEdge T s(V o 0, V o (N - 1)) :=
    Or.inl ⟨V o (N - 1), V o 0, Sym2.eq_swap, by
      rw [cdist_VV o (N - 1) 0 (by omega) (by omega), if_neg (by omega)]; omega⟩
  obtain ⟨P, h1, h2, ea, eb⟩ := apex_step T hT o 0 (N - 1) (by omega) (by omega) e0
  have fin : ∀ ε : Bool, E T sg o (I ε 0) (J N ε 0) → E T sg o (I ε 1) (J N ε 1) →
      ∃ ε : Bool, ∀ k, k ≤ N - 2 → E T sg o (I ε k) (J N ε k) := by
    intro ε E0 E1
    refine ⟨ε, fun k hk => ?_⟩
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact E0
    · have := (chain_ind T sg hN hT hpath halt o ε E0 E1 (k - 1) (by omega)).2
      rwa [Nat.sub_add_cancel hpos] at this
  rcases hpath_step T sg hpath o 0 (N - 1) P h1 h2 (by omega) e0 ea eb h0 with
    ⟨hP, hsP⟩ | ⟨hP, hsP⟩
  · obtain rfl : P = 1 := by omega
    refine fin true ?_ ?_
    · have g := IJ0 N true
      rw [g.1, g.2]; exact ⟨e0, h0⟩
    · have g1 : I true 1 = 1 := by simp [I]
      have g2 : J N true 1 = N - 1 := by simp [J]
      rw [g1, g2]; exact ⟨eb, by rw [hsP]; exact h0⟩
  · obtain rfl : P = N - 2 := by omega
    refine fin false ?_ ?_
    · have g := IJ0 N false
      rw [g.1, g.2]; exact ⟨e0, h0⟩
    · have g1 : I false 1 = 0 := by simp [I]
      have g2 : J N false 1 = N - 2 := by simp [J] <;> omega
      rw [g1, g2]; exact ⟨ea, by rw [hsP]; exact h0⟩

lemma ivt (u v : Fin N) (h : sg u ≠ sg v) : ∃ o : Fin N, sg (V o 0) ≠ sg (V o (N - 1)) := by
  by_contra hc
  simp only [not_exists, ne_eq, not_not] at hc
  have hN1 : 1 ≤ N := NeZero.one_le
  have key : ∀ k : ℕ, sg (V u k) = sg u := by
    intro k
    induction k with
    | zero => simp [V]
    | succ k ih =>
      have h1 := hc (V u (k + 1))
      have e1 : V (V u (k + 1)) 0 = V u (k + 1) := by simp [V]
      have e2 : V (V u (k + 1)) (N - 1) = V u k := by
        obtain ⟨M, hM⟩ : ∃ M, M + 1 = N := ⟨N - 1, by omega⟩
        have h3 : ((M + 1 : ℕ) : Fin N) = 0 := by rw [hM]; exact Fin.natCast_self N
        push_cast at h3
        simp only [V]
        rw [show N - 1 = M by omega]
        push_cast
        rw [show u + ((k : Fin N) + 1) + (M : Fin N) = u + (k : Fin N) + ((M : Fin N) + 1) by abel,
          h3, add_zero]
      rw [e1, e2, ih] at h1
      exact h1
  have := key (cdist u v)
  rw [V_of] at this
  exact h this.symm

lemma nonconst (hN : 4 ≤ N) (hT : IsTriangulation N T)
    (hsep : ∀ t ∈ triangles N T, ¬ ∃ sign : Bool, ∀ p ∈ t, sg p = sign) :
    ∃ u v : Fin N, sg u ≠ sg v := by
  let o : Fin N := ⟨0, by omega⟩
  have e0 : IsEdge T s(V o 0, V o (N - 1)) :=
    Or.inl ⟨V o (N - 1), V o 0, Sym2.eq_swap, by
      rw [cdist_VV o (N - 1) 0 (by omega) (by omega), if_neg (by omega)]; omega⟩
  obtain ⟨P, h1, h2, ea, eb⟩ := apex_step T hT o 0 (N - 1) (by omega) (by omega) e0
  have d1 : V o 0 ≠ V o (N - 1) := fun h => by have := V_inj o (by omega) (by omega) h; omega
  have d2 : V o 0 ≠ V o P := fun h => by have := V_inj o (by omega) (by omega) h; omega
  have d3 : V o (N - 1) ≠ V o P := fun h => by have := V_inj o (by omega) (by omega) h; omega
  have ht := mk_tri T _ _ _ d1 d2 d3 e0 ea (by rw [Sym2.eq_swap]; exact eb)
  by_contra hc
  simp only [not_exists, ne_eq, not_not] at hc
  exact hsep _ ht ⟨sg o, fun p _ => hc p o⟩

end walk

lemma pt_even (n t : ℕ) : snakePt n (2 * t) = ((1 + t : ℕ) : Fin (n + 3)) := by
  unfold snakePt
  rw [if_pos (by omega)]
  ext
  simp only [Fin.val_natCast]
  congr 1
  omega

lemma pt_odd (n t : ℕ) : snakePt n (2 * t + 1) = ((n + 2 - t : ℕ) : Fin (n + 3)) := by
  unfold snakePt
  rw [if_neg (by omega)]
  ext
  simp only [Fin.val_natCast]
  congr 1
  omega

lemma sym_eq {N : ℕ} {a b c d : Fin N} (h1 : a = c) (h2 : b = d) : s(a, b) = s(c, d) := by
  rw [h1, h2]

lemma sym_eq' {N : ℕ} {a b c d : Fin N} (h1 : a = d) (h2 : b = c) : s(a, b) = s(c, d) := by
  rw [h1, h2, Sym2.eq_swap]

lemma hz (n : ℕ) : ((n : ℕ) : Fin (n + 3)) = -3 := by
  rw [eq_neg_iff_add_eq_zero]
  have := Fin.natCast_self (n + 3)
  push_cast at this
  exact this

lemma fix {N : ℕ} [NeZero N] (o a b : Fin N) (h : a + b = 0) : o + a = o - b := by
  rw [eq_sub_iff_add_eq, add_assoc, h, add_zero]

lemma zmatch (n : ℕ) (o : Fin (n + 3)) (ε : Bool) (m : ℕ) (hm : m < n) :
    s(V o (I ε (m + 1)), V o (J (n + 3) ε (m + 1))) =
      Sym2.map (dihedral (if ε then o else o - 1) ε) s(snakePt n m, snakePt n (m + 1)) := by
  rw [Sym2.map_pair_eq]
  obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' m
  · obtain ⟨d, hd⟩ : ∃ d, t + d = n + 1 := ⟨n + 1 - t, by omega⟩
    have Z : ((t : ℕ) : Fin (n + 3)) + 1 + ((d : Fin (n + 3)) + 1) = 0 := by
      have h3 : ((t + 1 + (d + 1) : ℕ) : Fin (n + 3)) = 0 := by
        rw [show t + 1 + (d + 1) = n + 3 by omega]; exact Fin.natCast_self (n + 3)
      push_cast at h3; exact h3
    rw [pt_even, pt_odd, show n + 2 - t = d + 1 by omega]
    cases ε
    · have hI : I false (2 * t + 1) = t := by simp [I] <;> omega
      have hJ : J (n + 3) false (2 * t + 1) = d := by simp [J] <;> omega
      rw [hI, hJ, if_neg Bool.false_ne_true]
      refine sym_eq ?_ ?_ <;> simp only [V, dihedral, Bool.false_eq_true, if_false] <;>
        push_cast <;> abel
    · have hI : I true (2 * t + 1) = t + 1 := by simp [I] <;> omega
      have hJ : J (n + 3) true (2 * t + 1) = d + 1 := by simp [J] <;> omega
      rw [hI, hJ, if_pos rfl]
      refine sym_eq' ?_ ?_ <;> simp only [V, dihedral, if_true] <;>
        push_cast <;> apply fix <;> rw [← Z] <;> abel
  · obtain ⟨d, hd⟩ : ∃ d, t + d = n + 1 := ⟨n + 1 - t, by omega⟩
    have Z : ((t : ℕ) : Fin (n + 3)) + 1 + ((d : Fin (n + 3)) + 1) = 0 := by
      have h3 : ((t + 1 + (d + 1) : ℕ) : Fin (n + 3)) = 0 := by
        rw [show t + 1 + (d + 1) = n + 3 by omega]; exact Fin.natCast_self (n + 3)
      push_cast at h3; exact h3
    rw [pt_odd, show 2 * t + 1 + 1 = 2 * (t + 1) by ring, pt_even, show n + 2 - t = d + 1 by omega]
    cases ε
    · have hI : I false (2 * (t + 1)) = t + 1 := by simp [I] <;> omega
      have hJ : J (n + 3) false (2 * (t + 1)) = d := by simp [J] <;> omega
      rw [hI, hJ, if_neg Bool.false_ne_true]
      refine sym_eq' ?_ ?_ <;> simp only [V, dihedral, Bool.false_eq_true, if_false] <;>
        push_cast <;> abel
    · have hI : I true (2 * (t + 1)) = t + 1 := by simp [I] <;> omega
      have hJ : J (n + 3) true (2 * (t + 1)) = d := by simp [J] <;> omega
      rw [hI, hJ, if_pos rfl]
      refine sym_eq ?_ ?_ <;> simp only [V, dihedral, if_true] <;>
        push_cast <;> apply fix <;> rw [← Z] <;> abel

end Pfd4

open ChvatalArtGallery.FanPartition AssocRealizations.TypesMeet in
theorem solution (n : ℕ) (σ : Fin (n - 1) → Bool)
    (T : Finset (Sym2 (Fin (n + 3))))
    (hT : IsTriangulation (n + 3) T)
    (hpath : ∀ t ∈ triangles (n + 3) T,
      ∃ a ∈ t, ∃ b ∈ t, a ≠ b ∧
        IsBoundaryEdge s(a, b) ∧ hlSignPos σ a = hlSignPos σ b)
    (hseparates : ∀ t ∈ triangles (n + 3) T,
      ¬ ∃ sign : Bool, ∀ p ∈ t, hlSignPos σ p = sign)
    (halternates : ¬ ∃ a b c p : Fin (n + 3),
      a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ p ≠ a ∧ p ≠ b ∧ p ≠ c ∧
      IsBoundaryEdge s(a, b) ∧ IsBoundaryEdge s(b, c) ∧
      hlSignPos σ a = hlSignPos σ b ∧ hlSignPos σ b = hlSignPos σ c ∧
      ({a, b, p} : Finset (Fin (n + 3))) ∈ triangles (n + 3) T ∧
      ({b, c, p} : Finset (Fin (n + 3))) ∈ triangles (n + 3) T) :
    IsDihedralImage (snake n) T := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have nod : ∀ e : Sym2 (Fin (0 + 3)), ¬ IsDiagonal e := by decide
    have hT0 : T = ∅ := by
      ext e
      simp only [Finset.notMem_empty, iff_false]
      intro he
      exact nod e (hT.2.1 e he)
    subst hT0
    exact ⟨0, false, by simp [snake]⟩
  · have hN : 4 ≤ n + 3 := by omega
    obtain ⟨u, v, huv⟩ := Pfd4.nonconst T (hlSignPos σ) hN hT hseparates
    obtain ⟨o, ho⟩ := Pfd4.ivt (hlSignPos σ) u v huv
    obtain ⟨ε, hE⟩ := Pfd4.chain T (hlSignPos σ) hN hT hpath halternates o ho
    refine ⟨if ε then o else o - 1, ε, ?_⟩
    ext e
    rw [Pfd4.chain_eq T (hlSignPos σ) hN hT o ε hE e]
    constructor
    · rintro ⟨k, h1, h2, rfl⟩
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      refine Finset.mem_image.2 ⟨s(snakePt n m, snakePt n (m + 1)),
        Finset.mem_image.2 ⟨m, Finset.mem_range.2 (by omega), rfl⟩, ?_⟩
      exact (Pfd4.zmatch n o ε m (by omega)).symm
    · intro he
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 he
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 ha
      exact ⟨m + 1, by omega, by have := Finset.mem_range.1 hm; omega,
        (Pfd4.zmatch n o ε m (Finset.mem_range.1 hm)).symm⟩
