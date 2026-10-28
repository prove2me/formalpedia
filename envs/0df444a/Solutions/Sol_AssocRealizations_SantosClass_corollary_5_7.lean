-- Prove2me | solution 1 for AssocRealizations.SantosClass.corollary_5_7
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T06:29:23.525743+00:00
-- url     : https://prove2.me/submissions/f27b7fdf-6866-4766-ae9d-b65ffb3e8698

import Mathlib
import Definitions.Def_AssocRealizations_SantosClass_Setting

set_option autoImplicit false

open ChvatalArtGallery.FanPartition

namespace P0e6c

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

/-! ## the easy direction -/

lemma santosVec_dihedral {N : ℕ} [NeZero N] (r : Fin N) (refl : Bool)
    (T : Finset (Sym2 (Fin N))) (e d : Sym2 (Fin N)) (hd : d ∈ T)
    (hd' : Sym2.map (dihedral r refl) d ∈ T.image (Sym2.map (dihedral r refl))) :
    santosVec (T.image (Sym2.map (dihedral r refl))) (Sym2.map (dihedral r refl) e)
      ⟨Sym2.map (dihedral r refl) d, hd'⟩ = santosVec T e ⟨d, hd⟩ := by
  have hinj : Function.Injective (Sym2.map (dihedral r refl)) :=
    Sym2.map.injective (dihedral_injective r refl)
  simp only [santosVec, hinj.mem_finset_image, hinj.eq_iff, crosses_dihedral_iff]

theorem easy_dir {N : ℕ} [NeZero N] (T₁ T₂ : Finset (Sym2 (Fin N)))
    (h : IsDihedralImage T₁ T₂) :
    NormallyIsomorphic (santosFan T₁) (santosFan T₂) := by
  obtain ⟨r, refl, rfl⟩ := h
  have hinj : Function.Injective (Sym2.map (dihedral r refl)) :=
    Sym2.map.injective (dihedral_injective r refl)
  let σ : {d // d ∈ T₁} ≃ {d // d ∈ T₁.image (Sym2.map (dihedral r refl))} :=
    Equiv.ofBijective (fun d => ⟨Sym2.map (dihedral r refl) d.1, Finset.mem_image_of_mem _ d.2⟩)
      ⟨fun x y hxy => Subtype.ext (hinj (congrArg Subtype.val hxy)), fun y => by
        obtain ⟨x, hx, hxy⟩ := Finset.mem_image.1 y.2
        exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩
  let L : ({d // d ∈ T₁} → ℝ) ≃ₗ[ℝ] ({d // d ∈ T₁.image (Sym2.map (dihedral r refl))} → ℝ) :=
    LinearEquiv.funCongrLeft ℝ ℝ σ.symm
  have hL : ∀ e, L (santosVec T₁ e) =
      santosVec (T₁.image (Sym2.map (dihedral r refl))) (Sym2.map (dihedral r refl) e) := by
    intro e
    funext j
    obtain ⟨d, rfl⟩ := σ.surjective j
    simp only [L, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
      Equiv.symm_apply_apply]
    exact (santosVec_dihedral r refl T₁ e d.1 d.2 _).symm
  refine ⟨L, ?_⟩
  rintro C ⟨D, hD1, hD2, rfl⟩
  refine ⟨D.image (Sym2.map (dihedral r refl)), ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.1 he
    exact diagonal_dihedral r refl e' (hD1 e' he')
  · intro e he f hf
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.1 he
    obtain ⟨f', hf', rfl⟩ := Finset.mem_image.1 hf
    rw [crosses_dihedral_iff]
    exact hD2 e' he' f' hf'
  · have : (L.toLinearMap.restrictScalars {c : ℝ // 0 ≤ c}) '' (santosVec T₁ '' (↑D : Set _)) =
        santosVec (T₁.image (Sym2.map (dihedral r refl))) ''
          (↑(D.image (Sym2.map (dihedral r refl))) : Set _) := by
      rw [Finset.coe_image, Set.image_image, Set.image_image]
      ext v
      simp [hL]
    rw [PointedCone.hull, PointedCone.hull, ← this,
      Submodule.span_image (L.toLinearMap.restrictScalars {c : ℝ // 0 ≤ c}), Submodule.map_coe]
    rfl

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

lemma santosVec_mem' {N : ℕ} (T : Finset (Sym2 (Fin N))) (x : {d // d ∈ T}) :
    santosVec T x.1 = -(fun j => if x = j then (1:ℝ) else 0) := by
  funext j
  simp only [santosVec, x.2, if_true, Pi.neg_apply]
  by_cases h : x = j
  · subst h; simp
  · have : x.1 ≠ j.1 := fun h' => h (Subtype.ext h')
    simp [this, h]

lemma exists_other_crosser {N : ℕ} [NeZero N] (hN : 5 ≤ N) (d : Sym2 (Fin N))
    (hd : IsDiagonal d) (y₀ : Sym2 (Fin N)) :
    ∃ w, IsDiagonal w ∧ Crosses d w ∧ w ≠ y₀ := by
  induction d using Sym2.ind with
  | _ a b =>
  have hab := hd a b rfl
  have hk := cdist_lt a b
  have hk0 : cdist a b ≠ 0 := fun h => hab.1 ((cdist_eq_zero a b).1 h)
  have hk1 := hab.2.1
  have hk2 : cdist b a = N - cdist a b := cdist_swap a b hab.1
  have hk3 := hab.2.2
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
  have hA := hdiag 1 (k + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hB := hdiag (k - 1) (N - 1) (by omega) (by omega) (by omega) (by omega) (by omega)
  have cA := hcross 1 (k + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
  have cB := hcross (k - 1) (N - 1) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hAB : s(a + (⟨1, by omega⟩ : Fin N), a + (⟨k + 1, by omega⟩ : Fin N)) ≠
      s(a + (⟨k - 1, by omega⟩ : Fin N), a + (⟨N - 1, by omega⟩ : Fin N)) := by
    intro h
    rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have e1 := congrArg Fin.val (add_left_cancel h1)
      have e2 := congrArg Fin.val (add_left_cancel h2)
      simp at e1 e2; omega
    · have e1 := congrArg Fin.val (add_left_cancel h1)
      simp at e1; omega
  by_cases hy : s(a + (⟨1, by omega⟩ : Fin N), a + (⟨k + 1, by omega⟩ : Fin N)) = y₀
  · exact ⟨_, hB, cB, fun h => hAB (hy.trans h.symm)⟩
  · exact ⟨_, hA, cA, hy⟩

/-! ## linear rigidity: rays fixed by a dihedral map force the seed -/

theorem rigidity {N : ℕ} [NeZero N] (hN : 5 ≤ N) (T₁ T₂ : Finset (Sym2 (Fin N)))
    (h₁ : IsTriangulation N T₁) (h₂ : IsTriangulation N T₂) (r : Fin N) (refl : Bool)
    (L : ({d // d ∈ T₁} → ℝ) →ₗ[ℝ] ({d // d ∈ T₂} → ℝ)) (c : Sym2 (Fin N) → ℝ)
    (hc : ∀ e, IsDiagonal e → 0 < c e)
    (hL : ∀ e, IsDiagonal e →
      L (santosVec T₁ e) = c e • santosVec T₂ (Sym2.map (dihedral r refl) e)) :
    T₂ = T₁.image (Sym2.map (dihedral r refl)) := by
  have ginj : Function.Injective (Sym2.map (dihedral r refl)) :=
    Sym2.map.injective (dihedral_injective r refl)
  have hb : ∀ x : {d // d ∈ T₁}, L (fun j => if x = j then (1:ℝ) else 0) =
      -(c x.1 • santosVec T₂ (Sym2.map (dihedral r refl) x.1)) := by
    intro x
    have h := hL x.1 (h₁.2.1 x.1 x.2)
    rw [santosVec_mem' T₁ x, map_neg] at h
    rw [← h, neg_neg]
  have hexp : ∀ e, IsDiagonal e → ∀ z : {d // d ∈ T₂},
      c e * santosVec T₂ (Sym2.map (dihedral r refl) e) z =
        -∑ x : {d // d ∈ T₁}, santosVec T₁ e x *
          (c x.1 * santosVec T₂ (Sym2.map (dihedral r refl) x.1) z) := by
    intro e he z
    have h := congrFun (hL e he) z
    rw [LinearMap.pi_apply_eq_sum_univ L] at h
    simp only [hb, Finset.sum_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, mul_neg,
      Finset.sum_neg_distrib] at h
    rw [← h]
  have hinvd : ∀ e, IsDiagonal e → IsDiagonal (Sym2.map (dihInv r refl) e) := by
    intro e he
    obtain ⟨r', refl', hr⟩ := dihInv_eq r refl
    rw [hr]; exact diagonal_dihedral _ _ _ he
  have hsub : ∀ d ∈ T₁, Sym2.map (dihedral r refl) d ∈ T₂ := by
    intro d hd
    by_contra hgd
    have hdd : IsDiagonal d := h₁.2.1 d hd
    have hgdd := diagonal_dihedral r refl d hdd
    obtain ⟨y, hy, hcy⟩ : ∃ y ∈ T₂, Crosses (Sym2.map (dihedral r refl) d) y := by
      by_contra hno
      push_neg at hno
      exact hgd (h₂.2.2.2 _ hgdd hno)
    have hgy : Sym2.map (dihedral r refl) (Sym2.map (dihInv r refl) y) = y :=
      map_dihedral_map_inv r refl y
    set y₀ := Sym2.map (dihInv r refl) y with hy₀def
    have hy₀d : IsDiagonal y₀ := hinvd y (h₂.2.1 y hy)
    have hcd : Crosses d y₀ := by
      rw [← crosses_dihedral_iff r refl, hgy]; exact hcy
    have hy₀T : y₀ ∉ T₁ := fun h => h₁.2.2.1 d hd y₀ h hcd
    have step1 : ∀ z : {d // d ∈ T₂}, z.1 ≠ y →
        ¬ Crosses (Sym2.map (dihedral r refl) d) z.1 := by
      intro z hzy hcz
      have E := hexp y₀ hy₀d z
      have hl : santosVec T₂ (Sym2.map (dihedral r refl) y₀) z = 0 := by
        rw [hgy]; simp [santosVec, hy, Ne.symm hzy]
      rw [hl, mul_zero] at E
      have hterm : ∀ x : {d // d ∈ T₁}, 0 ≤ santosVec T₁ y₀ x *
          (c x.1 * santosVec T₂ (Sym2.map (dihedral r refl) x.1) z) := by
        intro x
        by_cases hx : Crosses y₀ x.1
        · have h1' : santosVec T₁ y₀ x = 1 := by simp [santosVec, hy₀T, hx]
          have hgx : Sym2.map (dihedral r refl) x.1 ∉ T₂ := by
            intro hm
            refine h₂.2.2.1 _ hm y hy ?_
            rw [← hgy]
            exact crosses_symm _ _ ((crosses_dihedral_iff r refl _ _).2 hx)
          have : 0 ≤ santosVec T₂ (Sym2.map (dihedral r refl) x.1) z := by
            simp only [santosVec, hgx, if_false]; split_ifs <;> norm_num
          rw [h1', one_mul]; exact mul_nonneg (hc _ (h₁.2.1 _ x.2)).le this
        · have h0 : santosVec T₁ y₀ x = 0 := by simp [santosVec, hy₀T, hx]
          rw [h0, zero_mul]
      have hsum0 : ∑ x : {d // d ∈ T₁}, santosVec T₁ y₀ x *
          (c x.1 * santosVec T₂ (Sym2.map (dihedral r refl) x.1) z) = 0 := by
        linarith [Finset.sum_nonneg (fun x (_ : x ∈ Finset.univ) => hterm x)]
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hterm x)).1 hsum0 ⟨d, hd⟩
        (Finset.mem_univ _)
      have hdcross : Crosses y₀ d := crosses_symm _ _ hcd
      simp only [santosVec, hy₀T, hdcross, hgd, hcz, if_false, if_true, one_mul,
        mul_one] at this
      exact (hc d hdd).ne' this
    obtain ⟨w₀, hw₀d, hw₀c, hw₀ne⟩ := exists_other_crosser hN d hdd y₀
    have hw₀T : w₀ ∉ T₁ := fun h => h₁.2.2.1 d hd w₀ h hw₀c
    have hgw₀T : Sym2.map (dihedral r refl) w₀ ∉ T₂ := by
      intro hm
      have hne : Sym2.map (dihedral r refl) w₀ ≠ y := by
        intro h
        rw [← hgy] at h
        exact hw₀ne (ginj h)
      exact step1 ⟨_, hm⟩ hne ((crosses_dihedral_iff r refl _ _).2 hw₀c)
    have E := hexp w₀ hw₀d ⟨y, hy⟩
    have hl : 0 ≤ c w₀ * santosVec T₂ (Sym2.map (dihedral r refl) w₀) ⟨y, hy⟩ := by
      refine mul_nonneg (hc _ hw₀d).le ?_
      simp only [santosVec, hgw₀T, if_false]; split_ifs <;> norm_num
    have hterm : ∀ x : {d // d ∈ T₁}, 0 ≤ santosVec T₁ w₀ x *
        (c x.1 * santosVec T₂ (Sym2.map (dihedral r refl) x.1) ⟨y, hy⟩) := by
      intro x
      by_cases hx : Crosses w₀ x.1
      · rw [show santosVec T₁ w₀ x = 1 by simp [santosVec, hw₀T, hx], one_mul]
        refine mul_nonneg (hc _ (h₁.2.1 _ x.2)).le ?_
        by_cases hgx : Sym2.map (dihedral r refl) x.1 ∈ T₂
        · have hne : Sym2.map (dihedral r refl) x.1 ≠ y := by
            intro h
            rw [← hgy] at h
            have := ginj h
            exact hy₀T (this ▸ x.2)
          simp [santosVec, hgx, hne]
        · simp only [santosVec, hgx, if_false]; split_ifs <;> norm_num
      · rw [show santosVec T₁ w₀ x = 0 by simp [santosVec, hw₀T, hx], zero_mul]
    have hpos : 0 < santosVec T₁ w₀ ⟨d, hd⟩ *
        (c d * santosVec T₂ (Sym2.map (dihedral r refl) d) ⟨y, hy⟩) := by
      have : Crosses w₀ d := crosses_symm _ _ hw₀c
      simp only [santosVec, hw₀T, this, hgd, hcy, if_false, if_true, one_mul, mul_one]
      exact hc d hdd
    have hsum := lt_of_lt_of_le hpos
      (Finset.single_le_sum (fun x (_ : x ∈ Finset.univ) => hterm x) (Finset.mem_univ (⟨d, hd⟩ : {d // d ∈ T₁})))
    linarith
  apply Finset.Subset.antisymm
  · intro e he
    have hge : Sym2.map (dihedral r refl) (Sym2.map (dihInv r refl) e) = e :=
      map_dihedral_map_inv r refl e
    have he₀d := hinvd e (h₂.2.1 e he)
    have hmem : Sym2.map (dihInv r refl) e ∈ T₁ := by
      refine h₁.2.2.2 _ he₀d (fun f hf hcr => h₂.2.2.1 e he _ (hsub f hf) ?_)
      rw [← hge]; exact (crosses_dihedral_iff r refl _ _).2 hcr
    exact Finset.mem_image.2 ⟨_, hmem, hge⟩
  · intro e he
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.1 he
    exact hsub e' he'

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

lemma small3 (T₁ T₂ : Finset (Sym2 (Fin 3))) (h₁ : IsTriangulation 3 T₁)
    (h₂ : IsTriangulation 3 T₂) : IsDihedralImage T₁ T₂ := by
  have hnd : ∀ e : Sym2 (Fin 3), ¬ IsDiagonal e := by decide
  have e1 : T₁ = ∅ := Finset.eq_empty_of_forall_notMem (fun e he => hnd e (h₁.2.1 e he))
  have e2 : T₂ = ∅ := Finset.eq_empty_of_forall_notMem (fun e he => hnd e (h₂.2.1 e he))
  subst e1 e2
  exact ⟨0, false, by simp⟩

lemma small4_classify (T : Finset (Sym2 (Fin 4))) (hT : IsTriangulation 4 T) :
    T = {s(0, 2)} ∨ T = {s(1, 3)} := by
  have hd : ∀ e : Sym2 (Fin 4), IsDiagonal e → e = s(0, 2) ∨ e = s(1, 3) := by decide
  have hc : Crosses (s(0, 2) : Sym2 (Fin 4)) s(1, 3) := by decide
  have hd02 : IsDiagonal (s(0, 2) : Sym2 (Fin 4)) := by decide
  have hd13 : IsDiagonal (s(1, 3) : Sym2 (Fin 4)) := by decide
  have hsub : ∀ e ∈ T, e = s(0, 2) ∨ e = s(1, 3) := fun e he => hd e (hT.2.1 e he)
  have not_both : s(0, 2) ∈ T → s(1, 3) ∈ T → False := fun a b => hT.2.2.1 _ a _ b hc
  by_cases h02 : s(0, 2) ∈ T
  · left
    ext e
    simp only [Finset.mem_singleton]
    constructor
    · intro he
      rcases hsub e he with rfl | rfl
      · rfl
      · exact (not_both h02 he).elim
    · rintro rfl; exact h02
  · right
    have h13 : s(1, 3) ∈ T := by
      by_contra h13
      apply h02
      apply hT.2.2.2 _ hd02
      intro f hf
      rcases hsub f hf with rfl | rfl
      · exact (h02 hf).elim
      · exact (h13 hf).elim
    ext e
    simp only [Finset.mem_singleton]
    constructor
    · intro he
      rcases hsub e he with rfl | rfl
      · exact (h02 he).elim
      · rfl
    · rintro rfl; exact h13

lemma small4 (T₁ T₂ : Finset (Sym2 (Fin 4))) (h₁ : IsTriangulation 4 T₁)
    (h₂ : IsTriangulation 4 T₂) : IsDihedralImage T₁ T₂ := by
  rcases small4_classify T₁ h₁ with rfl | rfl <;> rcases small4_classify T₂ h₂ with rfl | rfl
  · exact ⟨0, false, by decide⟩
  · exact ⟨1, false, by decide⟩
  · exact ⟨1, false, by decide⟩
  · exact ⟨0, false, by decide⟩

/-! ## step A basics -/

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

lemma santos_indep {N : ℕ} [NeZero N] (hN : 5 ≤ N) (T : Finset (Sym2 (Fin N)))
    (hT : IsTriangulation N T) (e f : Sym2 (Fin N)) (he : IsDiagonal e) (hf : IsDiagonal f)
    (hne : e ≠ f) (hnc : ¬ Crosses e f) (l : ℝ) : santosVec T f ≠ l • santosVec T e := by
  intro hl
  obtain ⟨i, hi⟩ : ∃ i, santosVec T e i ≠ 0 := by
    by_contra h; push_neg at h; exact santos_ne_zero T hT e he (funext h)
  have hfi := congrFun hl i
  simp only [Pi.smul_apply, smul_eq_mul] at hfi
  have hl3 : l = 0 ∨ l = 1 ∨ l = -1 := by
    rcases santos_entries T e i with h1 | h1 | h1 <;>
      rcases santos_entries T f i with h2 | h2 | h2 <;> rw [h1, h2] at hfi <;>
      first | exact absurd h1 hi | (left; linarith) | (right; left; linarith) |
        (right; right; linarith)
  rcases hl3 with rfl | rfl | rfl
  · rw [zero_smul] at hl; exact santos_ne_zero T hT f hf hl
  · rw [one_smul] at hl; exact hne (santos_inj hN T hT e f he hf hl.symm)
  · have hnc' : ¬ Crosses f e := fun h => hnc (crosses_symm _ _ h)
    by_cases heT : e ∈ T
    · have := congrFun hl ⟨e, heT⟩
      by_cases hfT : f ∈ T
      · simp [santosVec, heT, hfT, Ne.symm hne] at this
      · simp [santosVec, heT, hfT, hnc'] at this
    · by_cases hfT : f ∈ T
      · have := congrFun hl ⟨f, hfT⟩
        simp [santosVec, heT, hfT, hnc] at this
      · have hfi' := congrFun hl i
        simp only [Pi.smul_apply, smul_eq_mul] at hfi'
        have h1 : santosVec T e i = 1 := by
          unfold santosVec at hi ⊢; simp only [heT, if_false] at hi ⊢
          split_ifs at hi ⊢ <;> simp_all
        have h2 : 0 ≤ santosVec T f i := by
          unfold santosVec; simp only [hfT, if_false]; split_ifs <;> norm_num
        rw [h1] at hfi'; linarith

/-! ## step A: cone lemmas -/

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

theorem ray_map {N : ℕ} [NeZero N] (hN : 5 ≤ N) (T₁ T₂ : Finset (Sym2 (Fin N)))
    (h₁ : IsTriangulation N T₁) (h₂ : IsTriangulation N T₂)
    (L : ({d // d ∈ T₁} → ℝ) ≃ₗ[ℝ] ({d // d ∈ T₂} → ℝ))
    (hL : ∀ C ∈ santosFan T₁, L '' C ∈ santosFan T₂) :
    ∃ φ : Sym2 (Fin N) → Sym2 (Fin N), ∃ c : Sym2 (Fin N) → ℝ,
      (∀ e, IsDiagonal e → IsDiagonal (φ e) ∧ 0 < c e ∧
        L (santosVec T₁ e) = c e • santosVec T₂ (φ e)) ∧
      (∀ e f, IsDiagonal e → IsDiagonal f → ¬ Crosses e f → ¬ Crosses (φ e) (φ f)) := by
  have imh : ∀ S : Set ({d // d ∈ T₁} → ℝ),
      L '' (PointedCone.hull ℝ S : Set _) = (PointedCone.hull ℝ (L '' S) : Set _) := by
    intro S
    have : (L '' S) = (L.toLinearMap.restrictScalars {c : ℝ // 0 ≤ c}) '' S := rfl
    rw [this, PointedCone.hull, PointedCone.hull,
      Submodule.span_image (L.toLinearMap.restrictScalars {c : ℝ // 0 ≤ c}), Submodule.map_coe]
    rfl
  have Lne : ∀ e, IsDiagonal e → L (santosVec T₁ e) ≠ 0 := fun e he =>
    (L.map_ne_zero_iff).2 (santos_ne_zero T₁ h₁ e he)
  have hray : ∀ e, ∃ f, ∃ t : ℝ, IsDiagonal e →
      (IsDiagonal f ∧ 0 < t ∧ L (santosVec T₁ e) = t • santosVec T₂ f) := by
    intro e
    by_cases he : IsDiagonal e
    · obtain ⟨D', hD1, _, hD3⟩ := hL _ ⟨{e}, by
          intro x hx; rw [Finset.mem_singleton] at hx; rw [hx]; exact he, by
          intro x hx y hy; rw [Finset.mem_singleton] at hx hy; rw [hx, hy]
          exact crosses_irrefl e, rfl⟩
      rw [Finset.coe_singleton, Set.image_singleton, imh, Set.image_singleton] at hD3
      obtain ⟨d, hd, t, ht, hw⟩ := ray_pick (santosVec T₂) (↑D') _ (Lne e he)
        (fun d hd => santos_ne_zero T₂ h₂ d (hD1 d hd)) hD3
      exact ⟨d, t, fun _ => ⟨hD1 d hd, ht, hw⟩⟩
    · exact ⟨e, 1, fun h => absurd h he⟩
  choose φ c hφ using hray
  refine ⟨φ, c, fun e he => hφ e he, ?_⟩
  have pick : ∀ e f, IsDiagonal e → IsDiagonal f → e ≠ f → ¬ Crosses e f →
      ∀ D' : Finset (Sym2 (Fin N)), (∀ d ∈ D', IsDiagonal d) →
      (PointedCone.hull ℝ {L (santosVec T₁ e), L (santosVec T₁ f)} : Set ({d // d ∈ T₂} → ℝ)) =
        (PointedCone.hull ℝ (santosVec T₂ '' ↑D') : Set ({d // d ∈ T₂} → ℝ)) → φ e ∈ D' := by
    intro e f he hf hne hnc D' hD1 hD3
    have hind : ∀ l : ℝ, L (santosVec T₁ f) ≠ l • L (santosVec T₁ e) := by
      intro l h
      rw [← map_smul] at h
      exact santos_indep hN T₁ h₁ e f he hf hne hnc l (L.injective h)
    obtain ⟨d, hd, t, ht, hdeq⟩ := cone2_pick (santosVec T₂) (↑D') _ _ (Lne e he) hind hD3
    obtain ⟨hφd, hc, hφL⟩ := hφ e he
    have hv : santosVec T₂ d = santosVec T₂ (φ e) :=
      posparallel_eq _ _ (santos_entries T₂ d) (santos_entries T₂ (φ e))
        (santos_ne_zero T₂ h₂ _ hφd) (t * c e) (mul_pos ht hc)
        (by rw [hdeq, hφL, smul_smul])
    have := santos_inj hN T₂ h₂ d (φ e) (hD1 d hd) hφd hv
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

/-! ## counting -/

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

theorem hard_dir {N : ℕ} [NeZero N] (hN : 5 ≤ N) (T₁ T₂ : Finset (Sym2 (Fin N)))
    (h₁ : IsTriangulation N T₁) (h₂ : IsTriangulation N T₂)
    (h : NormallyIsomorphic (santosFan T₁) (santosFan T₂)) : IsDihedralImage T₁ T₂ := by
  obtain ⟨L, hL⟩ := h
  obtain ⟨φ, c, hφ, hnc⟩ := ray_map hN T₁ T₂ h₁ h₂ L hL
  have hinj : ∀ e f, IsDiagonal e → IsDiagonal f → φ e = φ f → e = f := by
    intro e f he hf hef
    obtain ⟨hφe, hce, hLe⟩ := hφ e he
    obtain ⟨hφf, hcf, hLf⟩ := hφ f hf
    have h1 : santosVec T₁ e = (c e / c f) • santosVec T₁ f := by
      apply L.injective
      rw [map_smul, hLe, hLf, hef, smul_smul, div_mul_cancel₀ _ hcf.ne']
    have h2 := posparallel_eq _ _ (santos_entries T₁ e) (santos_entries T₁ f)
      (santos_ne_zero T₁ h₁ f hf) (c e / c f) (div_pos hce hcf) h1
    exact santos_inj hN T₁ h₁ e f he hf h2
  have hsurj : ∀ f, IsDiagonal f → ∃ e, IsDiagonal e ∧ φ e = f :=
    fin_surj IsDiagonal φ (fun e he => (hφ e he).1) hinj
  have hcr : ∀ e f, IsDiagonal e → IsDiagonal f → (Crosses (φ e) (φ f) ↔ Crosses e f) := by
    intro e f he hf
    constructor
    · intro h; by_contra hc; exact hnc e f he hf hc h
    · intro h; by_contra hc
      obtain ⟨⟨e', f'⟩, ⟨he', hf', hnc'⟩, heq⟩ := fin_surj
        (fun p : Sym2 (Fin N) × Sym2 (Fin N) => IsDiagonal p.1 ∧ IsDiagonal p.2 ∧ ¬ Crosses p.1 p.2)
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
  obtain ⟨r, refl, hr⟩ := auto_dihedral hN φ (fun e he => (hφ e he).1) hinj hsurj hcr
  exact ⟨r, refl, rigidity hN T₁ T₂ h₁ h₂ r refl L.toLinearMap c (fun e he => (hφ e he).2.1)
    (fun e he => by rw [← hr e he]; exact (hφ e he).2.2)⟩

end P0e6c

open ChvatalArtGallery.FanPartition in
theorem solution (n : ℕ)
    (T₁ T₂ : Finset (Sym2 (Fin (n + 3))))
    (h₁ : IsTriangulation (n + 3) T₁)
    (h₂ : IsTriangulation (n + 3) T₂) :
    AssocRealizations.TypesMeet.NormallyIsomorphic (AssocRealizations.TypesMeet.santosFan T₁) (AssocRealizations.TypesMeet.santosFan T₂) ↔
      AssocRealizations.TypesMeet.IsDihedralImage T₁ T₂ := by
  refine ⟨fun h => ?_, P0e6c.easy_dir T₁ T₂⟩
  rcases n with _ | _ | n
  · exact P0e6c.small3 T₁ T₂ h₁ h₂
  · exact P0e6c.small4 T₁ T₂ h₁ h₂
  · exact P0e6c.hard_dir (by omega) T₁ T₂ h₁ h₂ h
