-- Prove2me | solution 1 for AssocRealizations.TypesMeet.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-30T11:34:37.140632+00:00
-- url     : https://prove2.me/submissions/516b0183-fdb1-40b8-8982-e919655de326

import Mathlib
import Definitions.Def_AssocRealizations_TypesMeet_Setting

set_option autoImplicit false

open ChvatalArtGallery.FanPartition

namespace Pe82b

open AssocRealizations.TypesMeet

/-! ## cdist basics -/

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


/-! ## more cdist arithmetic -/

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


/-! ## step B: automorphisms of the crossing graph are dihedral -/

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

lemma cdist_inj {N : ℕ} [NeZero N] (a x y : Fin N) (h : cdist a x = cdist a y) : x = y := by
  rw [cdist_eq_sub, cdist_eq_sub] at h
  exact sub_left_injective (Fin.ext h)

lemma crosses_disjoint {N : ℕ} [NeZero N] (e f : Sym2 (Fin N)) (h : Crosses e f) (x : Fin N)
    (hx : x ∈ e) (hy : x ∈ f) : False := by
  obtain ⟨a, b, c, d, rfl, rfl, h1, h2, h3⟩ := h
  have h0 : cdist a a = 0 := (cdist_eq_zero a a).2 rfl
  rw [Sym2.mem_iff] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> omega

/-- the short diagonal around `x` -/
def short {N : ℕ} [NeZero N] (x : Fin N) : Sym2 (Fin N) := s(x - 1, x + 1)

lemma short_diag {N : ℕ} [NeZero N] (hN : 5 ≤ N) (x : Fin N) : IsDiagonal (short x) := by
  have c0 : cdist (x - 1) x = 1 := by
    have := cdist_add_self (x - 1) 1
    rw [sub_add_cancel, Fin.val_one', Nat.mod_eq_of_lt (by omega)] at this
    exact this
  have c1 : cdist (x - 1) (x + 1) = 2 := by
    rw [cdist_succ (by omega), c0]; split_ifs <;> omega
  have hne : x - 1 ≠ x + 1 := by
    intro h; have := (cdist_eq_zero _ _).2 h; omega
  have c2 := cdist_swap _ _ hne
  rw [c1] at c2
  intro u v huv
  rcases Sym2.eq_iff.1 huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨hne, by omega, by omega⟩
  · exact ⟨fun h => hne h.symm, by omega, by omega⟩

lemma crosses_short_iff {N : ℕ} [NeZero N] (hN : 5 ≤ N) (e : Sym2 (Fin N)) (he : IsDiagonal e)
    (x : Fin N) : Crosses e (short x) ↔ x ∈ e := by
  constructor
  · intro h
    by_contra hx
    obtain ⟨a, b, c, d, rfl, hcd, h1, h2, h3⟩ := h
    have hxa : x ≠ a := fun h' => hx (h' ▸ Sym2.mem_mk_left _ _)
    have hxb : x ≠ b := fun h' => hx (h' ▸ Sym2.mem_mk_right _ _)
    have pa : cdist a x ≠ 0 := fun h' => hxa ((cdist_eq_zero a x).1 h').symm
    have pb : cdist a x ≠ cdist a b := fun h' => hxb (cdist_inj a x b h')
    have hs := cdist_succ (by omega) a x
    have hp := cdist_pred (by omega) a x
    have hlt := cdist_lt a x
    unfold short at hcd
    rcases Sym2.eq_iff.1 hcd with ⟨h4, h5⟩ | ⟨h4, h5⟩
    · rw [h4] at hp; rw [h5] at hs
      split_ifs at hs hp <;> omega
    · rw [h4] at hp; rw [h5] at hs
      split_ifs at hs hp <;> omega
  · intro hx
    induction e using Sym2.ind with
    | _ a b =>
    have key : ∀ u v : Fin N, IsDiagonal s(u, v) → Crosses s(u, v) (short u) := by
      intro u v huv
      have h := huv u v rfl
      have hk := cdist_lt u v
      have hk0 : cdist u v ≠ 0 := fun h' => h.1 ((cdist_eq_zero u v).1 h')
      have hk2 := cdist_swap u v h.1
      have h1 := h.2.1
      have h2 := h.2.2
      refine ⟨u, v, u + 1, u - 1, rfl, Sym2.eq_swap, ?_⟩
      rw [cdist_succ (by omega), cdist_pred (by omega)]
      have h0 : cdist u u = 0 := (cdist_eq_zero u u).2 rfl
      rw [h0]
      split_ifs <;> omega
    rcases Sym2.mem_iff.1 hx with rfl | rfl
    · exact key _ _ he
    · rw [Sym2.eq_swap]
      exact key _ _ (by rw [Sym2.eq_swap]; exact he)

lemma short_inj {N : ℕ} [NeZero N] (hN : 5 ≤ N) (x y : Fin N) (h : short x = short y) :
    x = y := by
  unfold short at h
  rcases Sym2.eq_iff.1 h with ⟨h1, _⟩ | ⟨h1, h2⟩
  · exact sub_left_injective h1
  · exfalso
    have e1 : x = y + 1 + 1 := by rw [← h1]; abel
    have e2 : x + 1 + 1 = y := by rw [h2]; abel
    rw [e1] at e2
    have := cdist_add_self y (1 + 1 + 1 + 1)
    rw [show y + (1 + 1 + 1 + 1) = y + 1 + 1 + 1 + 1 by abel, e2,
      (cdist_eq_zero y y).2 rfl] at this
    simp only [Fin.val_add, Fin.val_one'] at this
    rw [Nat.mod_eq_of_lt (show 1 < N by omega)] at this
    norm_num at this
    rw [Nat.mod_eq_of_lt (show 4 < N by omega)] at this
    omega

/-- the short-diagonal property: its crossers pairwise do not cross -/
def ShortProp {N : ℕ} (e : Sym2 (Fin N)) : Prop :=
  ∀ f g : Sym2 (Fin N), IsDiagonal f → IsDiagonal g → Crosses e f → Crosses e g → ¬ Crosses f g

lemma short_shortProp {N : ℕ} [NeZero N] (hN : 5 ≤ N) (x : Fin N) : ShortProp (short x) := by
  intro f g hf hg h1 h2 h3
  have a1 := (crosses_short_iff hN f hf x).1 (crosses_symm _ _ h1)
  have a2 := (crosses_short_iff hN g hg x).1 (crosses_symm _ _ h2)
  exact crosses_disjoint f g h3 x a1 a2

lemma shortProp_short {N : ℕ} [NeZero N] (hN : 5 ≤ N) (e : Sym2 (Fin N)) (he : IsDiagonal e)
    (hs : ShortProp e) : ∃ x, e = short x := by
  induction e using Sym2.ind with
  | _ a b =>
  have hab := he a b rfl
  have hk := cdist_lt a b
  have hk0 : cdist a b ≠ 0 := fun h => hab.1 ((cdist_eq_zero a b).1 h)
  have hk2 : cdist b a = N - cdist a b := cdist_swap a b hab.1
  have hk1 := hab.2.1
  have hk3 := hab.2.2
  have two : ∀ u v : Fin N, cdist u v = 2 → s(u, v) = short (u + 1) := by
    intro u v huv
    unfold short
    have : u + 1 + 1 = v := by
      apply cdist_inj u
      rw [cdist_succ (by omega), cdist_succ (by omega), (cdist_eq_zero u u).2 rfl, huv]
      split_ifs <;> omega
    rw [add_sub_cancel_right, this]
  by_cases hk : cdist a b = 2
  · exact ⟨_, two a b hk⟩
  by_cases hk' : cdist b a = 2
  · exact ⟨_, by rw [Sym2.eq_swap]; exact two b a hk'⟩
  exfalso
  set k := cdist a b with hkdef
  have hdiag : ∀ (p q : ℕ) (hp : p < N) (hq : q < N), p < q → q - p ≠ 1 → p + N - q ≠ 1 →
      IsDiagonal s(a + (⟨p, hp⟩ : Fin N), a + (⟨q, hq⟩ : Fin N)) := by
    intro p q hp hq hpq h1 h2 u v huv
    have c1 : cdist (a + (⟨p, hp⟩ : Fin N)) (a + ⟨q, hq⟩) = q - p := by
      rw [cdist_rot, cdist_of_le _ _ (by simp <;> omega)]
    have c2 : cdist (a + (⟨q, hq⟩ : Fin N)) (a + ⟨p, hp⟩) = p + N - q := by
      rw [cdist_rot, cdist_of_gt _ _ (by simp <;> omega)]
    have hne : a + (⟨p, hp⟩ : Fin N) ≠ a + ⟨q, hq⟩ := by
      intro h; have := congrArg Fin.val (add_left_cancel h); simp at this; omega
    rcases Sym2.eq_iff.1 huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hne, by rw [c1]; exact h1, by rw [c2]; exact h2⟩
    · exact ⟨fun h => hne h.symm, by rw [c2]; exact h2, by rw [c1]; exact h1⟩
  have hcross : ∀ (p q : ℕ) (hp : p < N) (hq : q < N), 0 < p → p < k → k < q →
      Crosses s(a, b) s(a + (⟨p, hp⟩ : Fin N), a + (⟨q, hq⟩ : Fin N)) := by
    intro p q hp hq h1 h2 h3
    refine ⟨a, b, _, _, rfl, rfl, ?_⟩
    rw [cdist_add_self, cdist_add_self]
    exact ⟨h1, h2, h3⟩
  refine hs _ _ (hdiag 1 (k + 1) (by omega) (by omega) (by omega) (by omega) (by omega))
    (hdiag 2 (k + 2) (by omega) (by omega) (by omega) (by omega) (by omega))
    (hcross 1 (k + 1) (by omega) (by omega) (by omega) (by omega) (by omega))
    (hcross 2 (k + 2) (by omega) (by omega) (by omega) (by omega) (by omega)) ?_
  refine ⟨_, _, _, _, rfl, rfl, ?_⟩
  simp only [cdist_rot]
  rw [cdist_of_le _ _ (by simp), cdist_of_le _ _ (by simp <;> omega),
    cdist_of_le _ _ (by simp <;> omega)]
  all_goals (try simp only)
  all_goals omega

open Fin.NatCast in
lemma cycle_plus {N : ℕ} [NeZero N] (hN : 3 ≤ N) (σ : Fin N → Fin N)
    (hinj : Function.Injective σ) (hstep : ∀ i, σ (i + 1) = σ i + 1 ∨ σ (i + 1) = σ i - 1)
    (h1 : σ 1 = σ 0 + 1) : ∀ i, σ i = σ 0 + i := by
  have two : (1 + 1 : Fin N) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (show 1 < N by omega)] at this
    simp only [Fin.val_zero] at this
    rw [Nat.mod_eq_of_lt (show 2 < N by omega)] at this
    omega
  have key : ∀ m : ℕ, σ (m : Fin N) = σ 0 + m ∧ σ ((m : Fin N) + 1) = σ (m : Fin N) + 1 := by
    intro m
    induction m with
    | zero => simp [h1]
    | succ m ih =>
      have e1 : σ ((m + 1 : ℕ) : Fin N) = σ 0 + ((m + 1 : ℕ) : Fin N) := by
        push_cast; rw [ih.2, ih.1]; abel
      refine ⟨e1, ?_⟩
      rcases hstep ((m + 1 : ℕ) : Fin N) with h | h
      · exact h
      · exfalso
        have : σ (((m + 1 : ℕ) : Fin N) + 1) = σ (m : Fin N) := by
          rw [h]; push_cast; rw [ih.2]; abel
        have := hinj this
        apply two
        push_cast at this
        have h3 : (m : Fin N) + (1 + 1) = (m : Fin N) + 0 := by
          rw [add_zero, ← add_assoc]; exact this
        exact add_left_cancel h3
  intro i
  have := (key i.val).1
  rwa [Fin.cast_val_eq_self] at this

lemma cycle_dihedral {N : ℕ} [NeZero N] (hN : 3 ≤ N) (σ : Fin N → Fin N)
    (hinj : Function.Injective σ) (hstep : ∀ i, σ (i + 1) = σ i + 1 ∨ σ (i + 1) = σ i - 1) :
    ∃ r refl, ∀ i, σ i = dihedral r refl i := by
  rcases hstep 0 with h | h
  · rw [zero_add] at h
    exact ⟨σ 0, false, fun i => by rw [cycle_plus hN σ hinj hstep h i]; rfl⟩
  · rw [zero_add] at h
    let τ : Fin N → Fin N := fun i => -σ i
    have tinj : Function.Injective τ := fun x y hxy => hinj (neg_injective hxy)
    have tstep : ∀ i, τ (i + 1) = τ i + 1 ∨ τ (i + 1) = τ i - 1 := by
      intro i
      rcases hstep i with h' | h'
      · right; simp only [τ, h']; abel
      · left; simp only [τ, h']; abel
    have t1 : τ 1 = τ 0 + 1 := by simp only [τ, h]; abel
    refine ⟨σ 0, true, fun i => ?_⟩
    have := cycle_plus hN τ tinj tstep t1 i
    simp only [τ] at this
    show σ i = σ 0 - i
    rw [← neg_neg (σ i), this]; abel

theorem auto_dihedral {N : ℕ} [NeZero N] (hN : 5 ≤ N) (φ : Sym2 (Fin N) → Sym2 (Fin N))
    (hφd : ∀ e, IsDiagonal e → IsDiagonal (φ e))
    (hφinj : ∀ e f, IsDiagonal e → IsDiagonal f → φ e = φ f → e = f)
    (hφsurj : ∀ f, IsDiagonal f → ∃ e, IsDiagonal e ∧ φ e = f)
    (hφc : ∀ e f, IsDiagonal e → IsDiagonal f → (Crosses (φ e) (φ f) ↔ Crosses e f)) :
    ∃ r refl, ∀ e, IsDiagonal e → φ e = Sym2.map (dihedral r refl) e := by
  have hsh : ∀ x : Fin N, ∃ y, φ (short x) = short y := by
    intro x
    apply shortProp_short hN _ (hφd _ (short_diag hN x))
    intro f' g' hf' hg' h1 h2 h3
    obtain ⟨f, hf, rfl⟩ := hφsurj f' hf'
    obtain ⟨g, hg, rfl⟩ := hφsurj g' hg'
    rw [hφc _ _ (short_diag hN x) hf] at h1
    rw [hφc _ _ (short_diag hN x) hg] at h2
    rw [hφc _ _ hf hg] at h3
    exact short_shortProp hN x f g hf hg h1 h2 h3
  choose σ hσ using hsh
  have sinj : Function.Injective σ := by
    intro x y hxy
    apply short_inj hN
    apply hφinj _ _ (short_diag hN x) (short_diag hN y)
    rw [hσ, hσ, hxy]
  have sstep : ∀ i, σ (i + 1) = σ i + 1 ∨ σ (i + 1) = σ i - 1 := by
    intro i
    have hc : Crosses (short (i + 1)) (short i) := by
      rw [crosses_short_iff hN _ (short_diag hN _)]
      unfold short; rw [add_sub_cancel_right]; exact Sym2.mem_mk_left _ _
    rw [← hφc _ _ (short_diag hN _) (short_diag hN _), hσ, hσ,
      crosses_short_iff hN _ (short_diag hN _)] at hc
    unfold short at hc
    rcases Sym2.mem_iff.1 hc with h | h
    · left; rw [h, sub_add_cancel]
    · right; rw [h, add_sub_cancel_right]
  obtain ⟨r, refl, hr⟩ := cycle_dihedral (by omega) σ sinj sstep
  refine ⟨r, refl, fun e he => ?_⟩
  have ssurj : Function.Surjective σ := Finite.surjective_of_injective sinj
  ext y
  obtain ⟨x, rfl⟩ := ssurj y
  rw [← crosses_short_iff hN _ (hφd e he), ← hσ, hφc _ _ he (short_diag hN x),
    crosses_short_iff hN _ he, hr, Sym2.mem_map]
  constructor
  · intro hx; exact ⟨x, hx, rfl⟩
  · rintro ⟨z, hz, hzx⟩
    rwa [← dihedral_injective r refl hzx]

/-! ## small polygons -/


/-! ## lemma 2.2 assembly -/

lemma map_short {N : ℕ} [NeZero N] (r : Fin N) (refl : Bool) (x : Fin N) :
    Sym2.map (dihedral r refl) (short x) = short (dihedral r refl x) := by
  cases refl
  · simp only [short, dihedral, Sym2.map_pair_eq, Bool.false_eq_true, ↓reduceIte]
    rw [show r + (x - 1) = r + x - 1 by abel, show r + (x + 1) = r + x + 1 by abel]
  · simp only [short, dihedral, Sym2.map_pair_eq, ↓reduceIte]
    rw [Sym2.eq_swap, show r - (x - 1) = r - x + 1 by abel, show r - (x + 1) = r - x - 1 by abel]

lemma two_ne {N : ℕ} [NeZero N] (hN : 3 ≤ N) : (1 + 1 : Fin N) ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (show 1 < N by omega)] at this
  simp only [Fin.val_zero] at this
  rw [Nat.mod_eq_of_lt (show 2 < N by omega)] at this
  omega

lemma big_case {N : ℕ} [NeZero N] (hN : 5 ≤ N)
    (π : Sym2 (Fin N) ≃ Sym2 (Fin N))
    (hdiag : ∀ e, IsDiagonal e ↔ IsDiagonal (π e))
    (hcross : ∀ e f, IsDiagonal e → IsDiagonal f →
      (Crosses e f ↔ Crosses (π e) (π f))) :
    ∃ r refl, (∀ e, IsDiagonal e → π e = Sym2.map (dihedral r refl) e) ∧
      (∀ r' refl', (∀ e, IsDiagonal e → π e = Sym2.map (dihedral r' refl') e) →
        r' = r ∧ refl' = refl) := by
  obtain ⟨r, refl, hr⟩ := auto_dihedral hN π (fun e he => (hdiag e).1 he)
    (fun e f _ _ h => π.injective h)
    (fun f hf => ⟨π.symm f, by rw [hdiag, Equiv.apply_symm_apply]; exact hf,
      Equiv.apply_symm_apply _ _⟩)
    (fun e f he hf => (hcross e f he hf).symm)
  refine ⟨r, refl, hr, fun r' refl' h' => ?_⟩
  have hd : ∀ x, dihedral r refl x = dihedral r' refl' x := fun x =>
    short_inj hN _ _ (by rw [← map_short, ← map_short, ← hr _ (short_diag hN x),
      h' _ (short_diag hN x)])
  have h0 := hd 0
  have h1 := hd 1
  have t2 := two_ne (N := N) (by omega)
  cases refl <;> cases refl' <;>
    simp only [dihedral, Bool.false_eq_true, ↓reduceIte, sub_zero, add_zero] at h0 h1
  · exact ⟨h0.symm, rfl⟩
  · exfalso; subst h0
    apply t2
    have h3 : r + (1 + 1) = r + 0 := by rw [add_zero, ← add_assoc, h1, sub_add_cancel]
    exact add_left_cancel h3
  · exfalso; subst h0
    apply t2
    have h3 : r + (1 + 1) = r + 0 := by rw [add_zero, ← add_assoc, ← h1, sub_add_cancel]
    exact add_left_cancel h3
  · exact ⟨h0.symm, rfl⟩

lemma case4 (π : Sym2 (Fin (1 + 3)) ≃ Sym2 (Fin (1 + 3)))
    (hdiag : ∀ e, IsDiagonal e ↔ IsDiagonal (π e)) :
    ∃ r refl, (∀ e, IsDiagonal e → π e = Sym2.map (dihedral r refl) e) := by
  have hd : ∀ e : Sym2 (Fin 4), IsDiagonal e → e = s(0, 2) ∨ e = s(1, 3) := by decide
  have d02 : IsDiagonal (s(0, 2) : Sym2 (Fin 4)) := by decide
  have d13 : IsDiagonal (s(1, 3) : Sym2 (Fin 4)) := by decide
  have p02 := hd _ ((hdiag _).1 d02)
  have p13 := hd _ ((hdiag _).1 d13)
  have hne : π s(0, 2) ≠ π s(1, 3) := π.injective.ne (by decide)
  rcases p02 with h02 | h02 <;> rcases p13 with h13 | h13
  · exact absurd (h02.trans h13.symm) hne
  · refine ⟨0, false, fun e he => ?_⟩
    rcases hd e he with rfl | rfl
    · rw [h02]; decide
    · rw [h13]; decide
  · refine ⟨1, false, fun e he => ?_⟩
    rcases hd e he with rfl | rfl
    · rw [h02]; decide
    · rw [h13]; decide
  · exact absurd (h02.trans h13.symm) hne

end Pe82b

open ChvatalArtGallery.FanPartition AssocRealizations.TypesMeet in
theorem solution (n : ℕ)
    (π : Sym2 (Fin (n + 3)) ≃ Sym2 (Fin (n + 3)))
    (hdiag : ∀ e, IsDiagonal e ↔ IsDiagonal (π e))
    (hcross : ∀ e f, IsDiagonal e → IsDiagonal f →
      (Crosses e f ↔ Crosses (π e) (π f))) :
    ∃ r refl, (∀ e, IsDiagonal e → π e = Sym2.map (dihedral r refl) e) ∧
      (2 ≤ n → ∀ r' refl', (∀ e, IsDiagonal e → π e = Sym2.map (dihedral r' refl') e) →
        r' = r ∧ refl' = refl) := by
  rcases n with _ | _ | n
  · have hnd : ∀ e : Sym2 (Fin 3), ¬ IsDiagonal e := by decide
    exact ⟨0, false, fun e he => absurd he (hnd e), fun h => by omega⟩
  · obtain ⟨r, refl, hr⟩ := Pe82b.case4 π hdiag
    exact ⟨r, refl, hr, fun h => by omega⟩
  · obtain ⟨r, refl, hr, hu⟩ := Pe82b.big_case (by omega) π hdiag hcross
    exact ⟨r, refl, hr, fun _ => hu⟩
