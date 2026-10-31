-- Prove2me | solution 1 for AssocRealizations.TypesMeet.proposition_5_5
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-30T12:31:20.465309+00:00
-- url     : https://prove2.me/submissions/76de8231-1245-4fb8-945c-f1edba933f11

import Mathlib
import Definitions.Def_AssocRealizations_TypesMeet_Setting

set_option autoImplicit false

open ChvatalArtGallery.FanPartition

namespace Pb73

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

/-- the arithmetic core of "the flipped diagonal crosses nothing else" -/
lemma pos_noncross_aux (N P B Q U V : ℕ) (h0P : 0 < P) (hPB : P < B) (hBQ : B < Q) (hQN : Q < N)
    (hd : ¬ Inter 0 B U V) (hap : P = 1 ∨ ¬ Inter 0 P U V)
    (hpb : B - P = 1 ∨ ¬ Inter P B U V) (hbq : Q - B = 1 ∨ ¬ Inter B Q U V)
    (hqa : N - Q = 1 ∨ ¬ Inter Q 0 U V) (hne : ¬ ((U = 0 ∧ V = B) ∨ (U = B ∧ V = 0)))
    (hU1 : P < U) (hU2 : U < Q) (hV : V < P ∨ Q < V) (hVN : V < N) : False := by
  rcases (show U < B ∨ U = B ∨ B < U by omega) with c1 | c1 | c1 <;>
  rcases (show V = 0 ∨ (0 < V ∧ V < P) ∨ Q < V by omega) with c2 | c2 | c2
  · rcases hpb with h | h
    · omega
    · exact h (by unfold Inter; omega)
  · rcases hap with h | h
    · omega
    · exact h (by unfold Inter; omega)
  · exact hd (by unfold Inter; omega)
  · omega
  · rcases hap with h | h
    · omega
    · exact h (by unfold Inter; omega)
  · rcases hqa with h | h
    · omega
    · exact h (by unfold Inter; omega)
  · rcases hbq with h | h
    · omega
    · exact h (by unfold Inter; omega)
  · exact hd (by unfold Inter; omega)
  · rcases hbq with h | h
    · omega
    · exact h (by unfold Inter; omega)

lemma not_inter_swap {u v w z : ℕ} (h : ¬ Inter u v w z) : ¬ Inter u v z w :=
  fun h' => h (inter_swap h')

lemma pos_noncross (N P B Q U V : ℕ) (h0P : 0 < P) (hPB : P < B) (hBQ : B < Q) (hQN : Q < N)
    (hUN : U < N) (hVN : V < N)
    (hd : ¬ Inter 0 B U V) (hap : P = 1 ∨ ¬ Inter 0 P U V)
    (hpb : B - P = 1 ∨ ¬ Inter P B U V) (hbq : Q - B = 1 ∨ ¬ Inter B Q U V)
    (hqa : N - Q = 1 ∨ ¬ Inter Q 0 U V) (hne : ¬ ((U = 0 ∧ V = B) ∨ (U = B ∧ V = 0)))
    (hI : Inter P Q U V) : False := by
  have hcase : (P < U ∧ U < Q ∧ (V < P ∨ Q < V)) ∨ (P < V ∧ V < Q ∧ (U < P ∨ Q < U)) := by
    unfold Inter at hI; omega
  rcases hcase with ⟨c1, c2, c3⟩ | ⟨c1, c2, c3⟩
  · exact pos_noncross_aux N P B Q U V h0P hPB hBQ hQN hd hap hpb hbq hqa hne c1 c2 c3 hVN
  · exact pos_noncross_aux N P B Q V U h0P hPB hBQ hQN (not_inter_swap hd)
      (hap.imp id not_inter_swap) (hpb.imp id not_inter_swap) (hbq.imp id not_inter_swap)
      (hqa.imp id not_inter_swap) (by omega) c1 c2 c3 hUN

lemma pos_eq (N P B Q X Y : ℕ) (h0P : 0 < P) (hPB : P < B) (hBQ : B < Q) (hQN : Q < N)
    (hXN : X < N) (hYN : Y < N)
    (hI : Inter 0 B X Y) (hap : P = 1 ∨ ¬ Inter 0 P X Y)
    (hpb : B - P = 1 ∨ ¬ Inter P B X Y) (hbq : Q - B = 1 ∨ ¬ Inter B Q X Y)
    (hqa : N - Q = 1 ∨ ¬ Inter Q 0 X Y) :
    (X = P ∧ Y = Q) ∨ (X = Q ∧ Y = P) := by
  have aux : ∀ X Y : ℕ, X < N → Y < N → 0 < X → X < B → B < Y →
      (P = 1 ∨ ¬ Inter 0 P X Y) → (B - P = 1 ∨ ¬ Inter P B X Y) →
      (Q - B = 1 ∨ ¬ Inter B Q X Y) → (N - Q = 1 ∨ ¬ Inter Q 0 X Y) → X = P ∧ Y = Q := by
    intro X Y hX hY c1 c2 c3 hap hpb hbq hqa
    constructor
    · rcases (show X < P ∨ X = P ∨ P < X by omega) with c | c | c
      · rcases hap with h | h
        · omega
        · exact absurd (by unfold Inter; omega) h
      · exact c
      · rcases hpb with h | h
        · omega
        · exact absurd (by unfold Inter; omega) h
    · rcases (show Y < Q ∨ Y = Q ∨ Q < Y by omega) with c | c | c
      · rcases hbq with h | h
        · omega
        · exact absurd (by unfold Inter; omega) h
      · exact c
      · rcases hqa with h | h
        · omega
        · exact absurd (by unfold Inter; omega) h
  have hcase : (0 < X ∧ X < B ∧ B < Y) ∨ (0 < Y ∧ Y < B ∧ B < X) := by
    unfold Inter at hI; omega
  rcases hcase with ⟨c1, c2, c3⟩ | ⟨c1, c2, c3⟩
  · exact Or.inl (aux X Y hXN hYN c1 c2 c3 hap hpb hbq hqa)
  · have := aux Y X hYN hXN c1 c2 c3 (hap.imp id not_inter_swap) (hpb.imp id not_inter_swap)
      (hbq.imp id not_inter_swap) (hqa.imp id not_inter_swap)
    exact Or.inr ⟨this.2, this.1⟩

lemma opp_symm {V : Type*} [AddCommGroup V] [Module ℝ V] {v w : V} (h : Opposite v w) :
    Opposite w v := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨c⁻¹, inv_pos.2 hc, ?_⟩
  rw [smul_neg, neg_neg, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]


lemma flip_char {N : ℕ} [NeZero N] (T : Finset (Sym2 (Fin N)))
    (hT : IsTriangulation N T) (d : Sym2 (Fin N)) (hd : d ∈ T) :
    ∃ f, IsTriangulation N (insert f (T.erase d)) ∧
      ∀ g : Sym2 (Fin N), Crosses g d → (∀ h ∈ T.erase d, ¬ Crosses g h) → g = f := by
  classical
  induction d using Sym2.ind with
  | _ a b =>
  have hdg := hT.2.1 _ hd a b rfl
  have hN := hT.1
  have hB := cdist_lt a b
  have hba : cdist b a = N - cdist a b := cdist_swap a b hdg.1
  have hB0 : cdist a b ≠ 0 := fun h => hdg.1 ((cdist_eq_zero a b).1 h)
  have hd1 := hdg.2.1
  have hd2 := hdg.2.2
  have hnoT : ∀ g ∈ T, ¬ Crosses s(a, b) g := fun g hg => hT.2.2.1 _ hd g hg
  have hnoT' : ∀ g ∈ T, ¬ Crosses s(b, a) g := by rw [Sym2.eq_swap]; exact hnoT
  obtain ⟨p, hp0, hpb, hap, hpbT⟩ := apex T hT a b (by omega) hnoT
  obtain ⟨q, hq0, hqa, hbq, hqaT⟩ := apex T hT b a (by omega) hnoT'
  have h00 : cdist a a = 0 := (cdist_eq_zero a a).2 rfl
  have hP := cdist_lt a p
  have hQ := cdist_lt a q
  have hbqv := cdist_via a b q
  have hQB : cdist a b < cdist a q ∧ cdist b q = cdist a q - cdist a b := by
    split_ifs at hbqv with hh <;> exact ⟨by omega, by omega⟩
  have side : ∀ x y u v : Fin N, s(x, y) ∈ T → s(u, v) ∈ T →
      ¬ Inter (cdist a x) (cdist a y) (cdist a u) (cdist a v) :=
    fun x y u v h1 h2 h => hT.2.2.1 _ h1 _ h2 ((crosses_pos a x y u v).2 h)
  have sides : ∀ u v : Fin N, s(u, v) ∈ T →
      ¬ Inter 0 (cdist a b) (cdist a u) (cdist a v) ∧
      (cdist a p = 1 ∨ ¬ Inter 0 (cdist a p) (cdist a u) (cdist a v)) ∧
      (cdist a b - cdist a p = 1 ∨ ¬ Inter (cdist a p) (cdist a b) (cdist a u) (cdist a v)) ∧
      (cdist a q - cdist a b = 1 ∨ ¬ Inter (cdist a b) (cdist a q) (cdist a u) (cdist a v)) ∧
      (N - cdist a q = 1 ∨ ¬ Inter (cdist a q) 0 (cdist a u) (cdist a v)) := by
    intro u v hg
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have := side a b u v hd hg; rwa [h00] at this
    · rcases hap with h | h
      · exact Or.inl h
      · right; have := side a p u v h hg; rwa [h00] at this
    · rcases hpbT with h | h
      · exact Or.inl h
      · exact Or.inr (side p b u v h hg)
    · rcases hbq with h | h
      · left; omega
      · exact Or.inr (side b q u v h hg)
    · rcases hqaT with h | h
      · left; omega
      · right; have := side q a u v h hg; rwa [h00] at this
  have hpq := cdist_via a p q
  have hqp := cdist_via a q p
  have hpqne : p ≠ q := by intro h; subst h; omega
  have hfd : IsDiagonal s(p, q) := by
    intro x y hxy
    rcases Sym2.eq_iff.1 hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨hpqne, ?_, ?_⟩ <;> split_ifs at hpq hqp <;> omega
    · refine ⟨fun h => hpqne h.symm, ?_, ?_⟩ <;> split_ifs at hpq hqp <;> omega
  have hne_of : ∀ u v : Fin N, (cdist a u ≠ 0 ∧ cdist a u ≠ cdist a b) ∨
      (cdist a v ≠ 0 ∧ cdist a v ≠ cdist a b) → s(u, v) ≠ s(a, b) := by
    intro u v h heq
    rcases Sym2.eq_iff.1 heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
  have hcrd : Crosses s(a, b) s(p, q) := by
    rw [crosses_pos a]; rw [h00]; unfold Inter; omega
  have fgood : ∀ g ∈ T.erase s(a, b), ¬ Crosses s(p, q) g := by
    intro g hg hcr
    obtain ⟨hgne, hgT⟩ := Finset.mem_erase.1 hg
    induction g using Sym2.ind with
    | _ u v =>
    obtain ⟨s1, s2, s3, s4, s5⟩ := sides u v hgT
    have hI := (crosses_pos a p q u v).1 hcr
    have hne : ¬ ((cdist a u = 0 ∧ cdist a v = cdist a b) ∨
        (cdist a u = cdist a b ∧ cdist a v = 0)) := by
      rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · apply hgne
        have hu : a = u := (cdist_eq_zero a u).1 h1
        have hv : v = b := cdist_inj a v b h2
        rw [← hu, hv]
      · apply hgne
        have hu : u = b := cdist_inj a u b h1
        have hv : a = v := (cdist_eq_zero a v).1 h2
        rw [hu, ← hv, Sym2.eq_swap]
    exact pos_noncross N (cdist a p) (cdist a b) (cdist a q) (cdist a u) (cdist a v) hp0 hpb
      hQB.1 hQ (cdist_lt a u) (cdist_lt a v) s1 s2 s3 s4 s5 hne hI
  have memE : ∀ u v : Fin N, s(u, v) ∈ T → s(u, v) ≠ s(a, b) →
      s(u, v) ∈ T.erase s(a, b) :=
    fun u v h1 h2 => Finset.mem_erase.2 ⟨h2, h1⟩
  have uniq : ∀ x y : Fin N, Crosses s(x, y) s(a, b) →
      (∀ g ∈ T.erase s(a, b), ¬ Crosses s(x, y) g) → s(x, y) = s(p, q) := by
    intro x y hc hno
    have noX : ∀ u v : Fin N, s(u, v) ∈ T.erase s(a, b) →
        ¬ Inter (cdist a u) (cdist a v) (cdist a x) (cdist a y) :=
      fun u v hm hI => hno _ hm (crosses_symm _ _ ((crosses_pos a u v x y).2 hI))
    have hI : Inter 0 (cdist a b) (cdist a x) (cdist a y) := by
      rw [← h00]; exact (crosses_pos a a b x y).1 (crosses_symm _ _ hc)
    have t2 : cdist a p = 1 ∨ ¬ Inter 0 (cdist a p) (cdist a x) (cdist a y) := by
      rcases hap with h | h
      · exact Or.inl h
      · right; have := noX a p (memE a p h (hne_of a p (Or.inr ⟨by omega, by omega⟩)))
        rwa [h00] at this
    have t3 : cdist a b - cdist a p = 1 ∨
        ¬ Inter (cdist a p) (cdist a b) (cdist a x) (cdist a y) := by
      rcases hpbT with h | h
      · exact Or.inl h
      · exact Or.inr (noX p b (memE p b h (hne_of p b (Or.inl ⟨by omega, by omega⟩))))
    have t4 : cdist a q - cdist a b = 1 ∨
        ¬ Inter (cdist a b) (cdist a q) (cdist a x) (cdist a y) := by
      rcases hbq with h | h
      · left; omega
      · exact Or.inr (noX b q (memE b q h (hne_of b q (Or.inr ⟨by omega, by omega⟩))))
    have t5 : N - cdist a q = 1 ∨ ¬ Inter (cdist a q) 0 (cdist a x) (cdist a y) := by
      rcases hqaT with h | h
      · left; omega
      · right; have := noX q a (memE q a h (hne_of q a (Or.inl ⟨by omega, by omega⟩)))
        rwa [h00] at this
    rcases pos_eq N (cdist a p) (cdist a b) (cdist a q) (cdist a x) (cdist a y) hp0 hpb
      hQB.1 hQ (cdist_lt a x) (cdist_lt a y) hI t2 t3 t4 t5 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [cdist_inj a x p h1, cdist_inj a y q h2]
    · rw [cdist_inj a x q h1, cdist_inj a y p h2, Sym2.eq_swap]
  refine ⟨s(p, q), ⟨hN, ?_, ?_, ?_⟩, ?_⟩
  · intro e he
    rcases Finset.mem_insert.1 he with rfl | he
    · exact hfd
    · exact hT.2.1 e (Finset.mem_of_mem_erase he)
  · intro e he g hg
    rcases Finset.mem_insert.1 he with rfl | he <;> rcases Finset.mem_insert.1 hg with rfl | hg
    · exact crosses_irrefl _
    · exact fgood g hg
    · exact fun h => fgood e he (crosses_symm _ _ h)
    · exact hT.2.2.1 e (Finset.mem_of_mem_erase he) g (Finset.mem_of_mem_erase hg)
  · intro e hed hno
    by_cases hc : Crosses e s(a, b)
    · induction e using Sym2.ind with
      | _ x y =>
      rw [uniq x y hc (fun g hg => hno g (Finset.mem_insert_of_mem hg))]
      exact Finset.mem_insert_self _ _
    · have heT : e ∈ T := by
        apply hT.2.2.2 e hed
        intro g hg
        by_cases hgd : g = s(a, b)
        · subst hgd; exact hc
        · exact hno g (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hgd, hg⟩))
      have hed' : e ≠ s(a, b) := by
        rintro rfl
        exact hno _ (Finset.mem_insert_self _ _) hcrd
      exact Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hed', heT⟩)
  · intro g hg hno
    induction g using Sym2.ind with
    | _ x y => exact uniq x y hg hno

/-! ## Proposition 5.5 -/

/-- a diagonal outside a triangulation crosses one of its members -/
lemma cross_of_not_mem {N : ℕ} (T : Finset (Sym2 (Fin N))) (hT : IsTriangulation N T)
    (f : Sym2 (Fin N)) (hf : IsDiagonal f) (hfT : f ∉ T) : ∃ g ∈ T, Crosses f g := by
  by_contra h
  push_neg at h
  exact hfT (hT.2.2.2 f hf h)

/-- for `e ∈ T`, `f ∉ T`: `f` crosses exactly `e` iff `T - e + f` is a triangulation -/
lemma flip_iff {N : ℕ} [NeZero N] (T : Finset (Sym2 (Fin N))) (hT : IsTriangulation N T)
    (e f : Sym2 (Fin N)) (he : e ∈ T) (hf : IsDiagonal f) (hfT : f ∉ T) :
    (∀ g ∈ T, Crosses f g ↔ g = e) ↔ IsTriangulation N (insert f (T.erase e)) := by
  classical
  constructor
  · intro hx
    obtain ⟨f0, htri, huniq⟩ := flip_char T hT e he
    have : f = f0 := huniq f ((hx e he).2 rfl) (fun h hh hc =>
      (Finset.mem_erase.1 hh).1 ((hx h (Finset.mem_of_mem_erase hh)).1 hc))
    rw [this]; exact htri
  · intro htri g hg
    constructor
    · intro hc
      by_contra hge
      exact htri.2.2.1 f (Finset.mem_insert_self _ _) g
        (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hge, hg⟩)) hc
    · rintro rfl
      obtain ⟨g', hg'T, hc'⟩ := cross_of_not_mem T hT f hf hfT
      by_contra hne
      have hg'e : g' ≠ g := by rintro rfl; exact hne hc'
      exact htri.2.2.1 f (Finset.mem_insert_self _ _) g'
        (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hg'e, hg'T⟩)) hc'

lemma not_tri_erase {N : ℕ} (T : Finset (Sym2 (Fin N))) (hT : IsTriangulation N T)
    (e : Sym2 (Fin N)) (he : e ∈ T) : ¬ IsTriangulation N (T.erase e) := by
  intro h
  have := h.2.2.2 e (hT.2.1 e he) (fun g hg => hT.2.2.1 e he g (Finset.mem_of_mem_erase hg))
  exact (Finset.mem_erase.1 this).1 rfl

/-- Opposite for a seed diagonal `e ∈ T` and a non-seed `f` -/
lemma opp_in_out {N : ℕ} (T : Finset (Sym2 (Fin N))) (e f : Sym2 (Fin N))
    (he : e ∈ T) (hfT : f ∉ T) :
    Opposite (santosVec T e) (santosVec T f) ↔ ∀ g ∈ T, Crosses f g ↔ g = e := by
  classical
  constructor
  · rintro ⟨c, hc, hv⟩
    have key : ∀ g (hg : g ∈ T), (if e = g then (-1 : ℝ) else 0) =
        -(c * (if Crosses f g then 1 else 0)) := by
      intro g hg
      have := congrFun hv ⟨g, hg⟩
      simpa [santosVec, he, hfT] using this
    intro g hg
    have k := key g hg
    by_cases h1 : e = g <;> by_cases h2 : Crosses f g <;> simp only [h1, h2, if_true, if_false] at k
    · simp [h1, h2]
    · norm_num at k
    · norm_num at k; exact absurd k hc.ne'
    · simp [h2, Ne.symm h1]
  · intro hx
    refine ⟨1, one_pos, ?_⟩
    funext g
    have := hx g.1 g.2
    by_cases h1 : e = g.1
    · have h2 : Crosses f g.1 := this.2 h1.symm
      simp [santosVec, he, hfT, h1, h2]
    · have h2 : ¬ Crosses f g.1 := fun h => h1 (this.1 h).symm
      simp [santosVec, he, hfT, h1, h2]

end Pb73

open ChvatalArtGallery.FanPartition AssocRealizations.TypesMeet in
theorem solution (n : ℕ)
    (T₀ : Finset (Sym2 (Fin (n + 3))))
    (hT : IsTriangulation (n + 3) T₀)
    (e f : Sym2 (Fin (n + 3))) (he : IsDiagonal e) (hf : IsDiagonal f)
    (hne : e ≠ f) :
    Opposite (santosVec T₀ e) (santosVec T₀ f) ↔
      (e ∈ T₀ ∧ IsTriangulation (n + 3) (insert f (T₀.erase e))) ∨
      (f ∈ T₀ ∧ IsTriangulation (n + 3) (insert e (T₀.erase f))) := by
  classical
  by_cases heT : e ∈ T₀ <;> by_cases hfT : f ∈ T₀
  · -- both seeds
    have h1 : insert f (T₀.erase e) = T₀.erase e :=
      Finset.insert_eq_of_mem (Finset.mem_erase.2 ⟨Ne.symm hne, hfT⟩)
    have h2 : insert e (T₀.erase f) = T₀.erase f :=
      Finset.insert_eq_of_mem (Finset.mem_erase.2 ⟨hne, heT⟩)
    rw [h1, h2]
    constructor
    · rintro ⟨c, hc, hv⟩
      have := congrFun hv ⟨e, heT⟩
      simp [santosVec, heT, hfT, Ne.symm hne] at this
    · rintro (⟨_, h⟩ | ⟨_, h⟩)
      · exact absurd h (Pb73.not_tri_erase T₀ hT e heT)
      · exact absurd h (Pb73.not_tri_erase T₀ hT f hfT)
  · rw [Pb73.opp_in_out T₀ e f heT hfT, Pb73.flip_iff T₀ hT e f heT hf hfT]
    simp [heT, hfT]
  · have hs : Opposite (santosVec T₀ e) (santosVec T₀ f) ↔
        Opposite (santosVec T₀ f) (santosVec T₀ e) :=
      ⟨Pb73.opp_symm, Pb73.opp_symm⟩
    rw [hs, Pb73.opp_in_out T₀ f e hfT heT, Pb73.flip_iff T₀ hT f e hfT he heT]
    simp [heT, hfT]
  · -- neither is a seed
    obtain ⟨g, hg, hc⟩ := Pb73.cross_of_not_mem T₀ hT e he heT
    simp only [heT, hfT, false_and, or_self, iff_false]
    rintro ⟨c, hc0, hv⟩
    have := congrFun hv ⟨g, hg⟩
    simp only [santosVec, heT, hfT, if_false, hc, if_true, Pi.neg_apply, Pi.smul_apply,
      smul_eq_mul] at this
    split_ifs at this <;> linarith
