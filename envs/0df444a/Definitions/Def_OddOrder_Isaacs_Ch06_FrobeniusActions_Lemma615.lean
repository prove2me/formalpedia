-- Prove2me | Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_Lemma615
-- name    : OddOrder_Isaacs_Ch06_FrobeniusActions_Lemma615
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:42:04.853352+00:00
-- url     : https://prove2.me/theorems/7e714437-4997-4f75-95f0-a737e0ee7e02
-- title:
--   Isaacs Lemma 6.15: characteristic elementary abelian subgroups of order $p^2$
-- statement:
--   Formalizes Isaacs, *Finite Group Theory*, Chapter 6, Lemma 6.15 (pp. 193–197): existence of a characteristic elementary abelian subgroup of order $p^2$, in the odd case and the case $p=2$. It includes results on groups whose center has index $p^2$.
--
--   The one definition is `characteristicRestrictMulEquiv` (restrict an automorphism of $G$ to a characteristic subgroup).
--
--   The bundle also proves 34 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch06_FrobeniusActions/Lemma615.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch06_FrobeniusActions/Lemma615.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_DQSDRecognition

namespace OddOrder.Isaacs.Ch06

open OddOrder.GroupTheory

/-- **Step 0 of Lem 6.15**: under the hypothesis `Z(T) ≤ C` and `|T : Z(T)| = p²` with
`Z(T) ≠ C`, we get `|T : C| = p`. -/
private lemma index_eq_prime_of_center_lt_of_center_index_pow_two
    {T : Type*} [Group T] [Finite T] {p : ℕ} [hp : Fact p.Prime]
    (h_idx : (Subgroup.center T).index = p ^ 2)
    {C : Subgroup T} (hZ_lt_C : Subgroup.center T < C) (hC_lt_T : C < ⊤) :
    C.index = p := by
  -- C.index ∣ Z.index = p^2
  have h_dvd : C.index ∣ (Subgroup.center T).index :=
    Subgroup.index_dvd_of_le hZ_lt_C.le
  rw [h_idx] at h_dvd
  -- C.index ∈ {1, p, p^2}
  rcases (Nat.dvd_prime_pow hp.out).mp h_dvd with ⟨k, hk, hkpow⟩
  interval_cases k
  · -- k = 0: C = ⊤
    rw [pow_zero] at hkpow
    have : C = ⊤ := Subgroup.index_eq_one.mp hkpow
    exact absurd this hC_lt_T.ne
  · rw [pow_one] at hkpow; exact hkpow
  · -- k = 2: C = Z(T)
    exfalso
    rw [← h_idx] at hkpow
    -- From C.index = (Z(T)).index = p^2 and index_mul_card, |C| = |Z(T)|.
    have h_card_eq : Nat.card C = Nat.card (Subgroup.center T) := by
      have h1 := C.index_mul_card
      have h2 := (Subgroup.center T).index_mul_card
      rw [hkpow, ← h2] at h1
      have hidx_pos : 0 < (Subgroup.center T).index := by
        rw [h_idx]; exact Nat.pos_of_ne_zero (pow_ne_zero _ hp.out.ne_zero)
      exact Nat.eq_of_mul_eq_mul_left hidx_pos h1
    have hZ_eq_C : Subgroup.center T = C :=
      Subgroup.eq_of_le_of_card_ge hZ_lt_C.le (le_of_eq h_card_eq)
    exact hZ_lt_C.ne hZ_eq_C

/-- **Step 0 of Lem 6.15**: under the hypothesis of Lem 6.15, `commutator T ≤ Z(T)`
(i.e. `T` has nilpotence class ≤ 2). -/
private lemma commutator_le_center_of_index_pow_two
    {T : Type*} [Group T] [Finite T] {p : ℕ} [hp : Fact p.Prime]
    (h_idx : (Subgroup.center T).index = p ^ 2) :
    _root_.commutator T ≤ Subgroup.center T := by
  have hZnorm : (Subgroup.center T).Normal := inferInstance
  -- `T ⧸ Z(T)` of order p² is abelian.
  have h_card_quot : Nat.card (T ⧸ Subgroup.center T) = p ^ 2 := by
    rw [← Subgroup.index_eq_card]; exact h_idx
  have h_quot_comm : ∀ a b : T ⧸ Subgroup.center T, a * b = b * a :=
    isMulCommutative_iff.mp
      (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := p) h_card_quot)
  exact hZnorm.quotient_commutative_iff_commutator_le.mp ⟨⟨h_quot_comm⟩⟩

/-- **Step 0 of Lem 6.15**: under the hypothesis `Z(T) ≤ C` and `|T : Z(T)| = p²`, `C` is
normal in `T`. (Because `T/Z(T)` of order `p²` is abelian, so every subgroup of `T/Z(T)`
is normal, and `C/Z(T)` lifts back to `C` normal in `T`.) -/
private lemma normal_of_center_le_of_center_index_pow_two
    {T : Type*} [Group T] [Finite T] {p : ℕ} [hp : Fact p.Prime]
    (h_idx : (Subgroup.center T).index = p ^ 2)
    {C : Subgroup T} (hZ_le_C : Subgroup.center T ≤ C) : C.Normal := by
  have hZnorm : (Subgroup.center T).Normal := inferInstance
  -- T/Z(T) of order p² is abelian.
  have h_card_quot : Nat.card (T ⧸ Subgroup.center T) = p ^ 2 := by
    rw [← Subgroup.index_eq_card]; exact h_idx
  have hQuot_comm : ∀ a b : T ⧸ Subgroup.center T, a * b = b * a :=
    isMulCommutative_iff.mp
      (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := p) h_card_quot)
  -- Image of C under the quotient map: C/Z(T) ≤ T/Z(T).
  let C' : Subgroup (T ⧸ Subgroup.center T) := C.map (QuotientGroup.mk' (Subgroup.center T))
  have hC'Norm : C'.Normal := by
    -- Subgroups of an abelian quotient are normal: g*n*g⁻¹ = n via mul_comm.
    refine ⟨fun n hn g => ?_⟩
    have h_eq : g * n * g⁻¹ = n := by
      rw [hQuot_comm g n, mul_assoc, mul_inv_cancel, mul_one]
    rw [h_eq]; exact hn
  -- C = preimage of C' under mk' Z(T) (because Z(T) ≤ C).
  have h_comap_eq : C'.comap (QuotientGroup.mk' (Subgroup.center T)) = C := by
    change ((C.map (QuotientGroup.mk' (Subgroup.center T))).comap _) = C
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    exact sup_eq_left.mpr hZ_le_C
  rw [← h_comap_eq]
  exact hC'Norm.comap _

/-- **Helper for Lem 6.15**: if `|T : Z(T)| = p²` then `T` is nonabelian. -/
private lemma exists_not_commute_of_center_index_pow_two
    {T : Type*} [Group T] [Finite T] {p : ℕ} [hp : Fact p.Prime]
    (h_idx : (Subgroup.center T).index = p ^ 2) :
    ∃ x y : T, x * y ≠ y * x := by
  by_contra h
  push Not at h
  -- T abelian ⇒ Z(T) = ⊤ ⇒ index = 1.
  have hZ_top : Subgroup.center T = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro x
    rw [Subgroup.mem_center_iff]
    exact fun y => (h y x)
  rw [hZ_top, Subgroup.index_top] at h_idx
  have hp1 : 1 < p := hp.out.one_lt
  have hp_sq_lt : 1 < p ^ 2 := by
    calc 1 = 1 ^ 2 := (one_pow 2).symm
      _ < p ^ 2 := Nat.pow_lt_pow_left hp1 (by norm_num)
  omega

/-- **Lem 6.15 `p = 2` setup**: the quotient `T/T'` is abelian. -/
theorem quotient_commutator_commutative
    {T : Type*} [Group T] :
    ∀ a b : T ⧸ _root_.commutator T, a * b = b * a := by
  exact (Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
    (le_rfl : _root_.commutator T ≤ _root_.commutator T)).is_comm.comm

/-- **Lem 6.15 `p = 2` setup**: under the center-index hypothesis of Lemma 6.15,
the quotient `T/T'` is not cyclic.

This isolates Isaacs's observation that, once `T' ≤ Z(T)`, cyclicity of `T/T'` would make
`T` itself abelian by `MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center`, contradicting
`|T : Z(T)| = p²`. -/
theorem quotient_commutator_not_isCyclic_of_center_index_prime_sq
    {T : Type*} [Group T] [Finite T] {p : ℕ} [hp : Fact p.Prime]
    (h_idx : (Subgroup.center T).index = p ^ 2) :
    ¬ IsCyclic (T ⧸ _root_.commutator T) := by
  intro h_cyc
  obtain ⟨x, y, hxy⟩ := exists_not_commute_of_center_index_pow_two h_idx
  let f : T →* T ⧸ _root_.commutator T := QuotientGroup.mk' (_root_.commutator T)
  have hker : f.ker ≤ Subgroup.center T := by
    rw [QuotientGroup.ker_mk']
    exact commutator_le_center_of_index_pow_two h_idx
  have : IsCyclic (T ⧸ _root_.commutator T) := h_cyc
  exact hxy ((f.isMulCommutative_of_isCyclic_of_ker_le_center hker).is_comm.comm x y)

/-- **Lem 6.15 `p = 2` setup**: the image of Isaacs's cyclic subgroup `C` in `T/T'`
is cyclic of index `2`.

This supplies the `D ≤ T/T'` input for
`exists_characteristic_isElementaryAbelian_four_of_noncyclic_abelian_two_group`. -/
theorem quotient_commutator_image_cyclic_index_two_of_center_index_four
    {T : Type*} [Group T] [Finite T]
    (h_idx : (Subgroup.center T).index = 2 ^ 2)
    {C : Subgroup T} (hC_cyclic : IsCyclic C)
    (hC_lt_T : C < ⊤) (hZ_lt_C : Subgroup.center T < C) :
    IsCyclic (C.map (QuotientGroup.mk' (_root_.commutator T))) ∧
      (C.map (QuotientGroup.mk' (_root_.commutator T))).index = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · have : IsCyclic C := hC_cyclic
    exact isCyclic_of_surjective
      ((QuotientGroup.mk' (_root_.commutator T)).subgroupMap C)
      ((QuotientGroup.mk' (_root_.commutator T)).subgroupMap_surjective C)
  · have hcomm_le_C : _root_.commutator T ≤ C :=
      (commutator_le_center_of_index_pow_two (p := 2) h_idx).trans hZ_lt_C.le
    calc
      (C.map (QuotientGroup.mk' (_root_.commutator T))).index = C.index := by
        exact Subgroup.index_map_eq C
          (QuotientGroup.mk'_surjective (_root_.commutator T)) (by
            rw [QuotientGroup.ker_mk']
            exact hcomm_le_C)
      _ = 2 :=
        index_eq_prime_of_center_lt_of_center_index_pow_two
          (p := 2) h_idx hZ_lt_C hC_lt_T

/-- **Step 0 of Lem 6.15** (cardinality): under the hypothesis of Lem 6.15,
`|commutator T| = p`. -/
private lemma card_commutator_eq_prime_of_lem_6_15
    {T : Type*} [Group T] [Finite T] {p : ℕ} [hp : Fact p.Prime]
    (h_idx : (Subgroup.center T).index = p ^ 2)
    {C : Subgroup T} [C.Normal] (hC_cyclic : IsCyclic C)
    (hC_lt_T : C < ⊤) (hZ_lt_C : Subgroup.center T < C) :
    Nat.card (_root_.commutator T) = p := by
  have hC_idx : C.index = p :=
    index_eq_prime_of_center_lt_of_center_index_pow_two h_idx hZ_lt_C hC_lt_T
  -- Cyclic quotient T/C.
  have hCT_card : Nat.card (T ⧸ C) = p := by rw [← Subgroup.index_eq_card]; exact hC_idx
  have : IsCyclic (T ⧸ C) := isCyclic_of_prime_card hCT_card
  -- Use Lem 4.6: |commutator T| · |C ⊓ Z(T)| = |C|.
  have h_lem46 :
      Nat.card (_root_.commutator T) * Nat.card (C ⊓ Subgroup.center T : Subgroup T)
        = Nat.card C := by
    refine
      Ch04.card_commutator_mul_card_inf_center_eq_card_of_normal_abelian_cyclic_quotient
      (A := C) ?_ ?_
    · -- C abelian (cyclic)
      intro a ha b hb
      have := hC_cyclic
      let : CommGroup C := IsCyclic.commGroup
      have h_comm : ∀ x y : ↥C, x * y = y * x := mul_comm
      exact congrArg (fun (z : ↥C) => (z : T)) (h_comm ⟨a, ha⟩ ⟨b, hb⟩)
    · -- T/C cyclic
      infer_instance
  -- C ⊓ Z(T) = Z(T) since Z(T) ≤ C.
  have h_inf : C ⊓ Subgroup.center T = Subgroup.center T := inf_eq_right.mpr hZ_lt_C.le
  rw [h_inf] at h_lem46
  -- |C| / |Z(T)| = p. From |T| = p²·|Z(T)| = p·|C|, we get |C| = p·|Z(T)|.
  have h_card_T_Z : (Subgroup.center T).index * Nat.card (Subgroup.center T) = Nat.card T :=
    Subgroup.index_mul_card _
  have h_card_T_C : C.index * Nat.card C = Nat.card T := Subgroup.index_mul_card _
  rw [h_idx] at h_card_T_Z
  rw [hC_idx] at h_card_T_C
  have h_card_C : Nat.card C = p * Nat.card (Subgroup.center T) := by
    have hp_pos : 0 < p := hp.out.pos
    have hT_eq : p ^ 2 * Nat.card (Subgroup.center T) = p * Nat.card C := by
      rw [h_card_T_Z, h_card_T_C]
    have hT_eq' : p * (p * Nat.card (Subgroup.center T)) = p * Nat.card C := by
      have : p ^ 2 * Nat.card (Subgroup.center T) = p * (p * Nat.card (Subgroup.center T)) := by
        ring
      rw [← this]; exact hT_eq
    exact (Nat.eq_of_mul_eq_mul_left hp_pos hT_eq').symm
  rw [h_card_C] at h_lem46
  -- Now: |commutator T| · |Z(T)| = p · |Z(T)|, so |commutator T| = p (since |Z(T)| > 0).
  have hZ_pos : 0 < Nat.card (Subgroup.center T) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hZ_pos h_lem46

/-- **Lem 6.15 odd-p helper**: under the hypothesis of Lem 6.15 with `p` odd, the set
`{x : T | x^p = 1}` is characteristic, i.e., preserved by any automorphism. The same set
is also a subgroup (via `Ch04.setOfPowEqOne`); here we record characteristicity. -/
private lemma setOfPowEqOne_characteristic_of_class_le_two_odd
    {T : Type*} [Group T] {p : ℕ} (hp : Odd p)
    (hC : _root_.commutator T ≤ Subgroup.center T) :
    (OddOrder.Isaacs.Ch04.setOfPowEqOne hC hp).Characteristic := by
  refine ⟨fun φ => ?_⟩
  ext x
  rw [Subgroup.mem_comap]
  change (φ x) ^ p = 1 ↔ x ^ p = 1
  refine ⟨fun hpx => ?_, fun hpx => ?_⟩
  · -- φ x ^ p = 1 ⇒ φ (x^p) = 1 ⇒ x^p = 1 by injectivity
    rw [← map_pow] at hpx
    have : φ (x ^ p) = φ 1 := by rw [hpx, map_one]
    exact φ.injective this
  · rw [← map_pow, hpx, map_one]

/-- **Lem 6.15 odd-p helper**: Under the hypothesis of Lem 6.15 with `p` odd,
the image of `θ : T → T, θ(x) = x^p` is contained in `Z(T)`. -/
private lemma pow_p_mem_center_of_index_pow_two_odd
    {T : Type*} [Group T] [Finite T] {p : ℕ} [hp : Fact p.Prime]
    (h_idx : (Subgroup.center T).index = p ^ 2) (x : T) :
    x ^ p ∈ Subgroup.center T := by
  -- T/Z(T) has order p² and is noncyclic (otherwise T abelian, contradiction).
  have hZnorm : (Subgroup.center T).Normal := inferInstance
  have h_card_quot : Nat.card (T ⧸ Subgroup.center T) = p ^ 2 := by
    rw [← Subgroup.index_eq_card]; exact h_idx
  -- Get T is nonabelian:
  obtain ⟨a, b, hab⟩ := exists_not_commute_of_center_index_pow_two h_idx
  -- The quotient T/Z(T) is not cyclic (because then T abelian).
  have h_quot_not_cyclic : ¬ IsCyclic (T ⧸ Subgroup.center T) := by
    intro h_cyc
    let f : T →* T ⧸ Subgroup.center T := QuotientGroup.mk' (Subgroup.center T)
    have hker : f.ker ≤ Subgroup.center T := by
      rw [QuotientGroup.ker_mk']
    let : IsCyclic (T ⧸ Subgroup.center T) := h_cyc
    have h_comm : ∀ a b : T, a * b = b * a :=
      (f.isMulCommutative_of_isCyclic_of_ker_le_center hker).is_comm.comm
    exact hab (h_comm a b)
  -- T/Z(T) of order p² noncyclic ⇒ exponent = p.
  have hp_prime : Fact p.Prime := hp
  have h_quot_exp : Monoid.exponent (T ⧸ Subgroup.center T) = p :=
    (not_isCyclic_iff_exponent_eq_prime hp.out h_card_quot).mp h_quot_not_cyclic
  -- So every element x : T satisfies (x : T/Z(T))^p = 1, i.e., x^p ∈ Z(T).
  have h_pow_eq_one : (QuotientGroup.mk x : T ⧸ Subgroup.center T) ^ p = 1 := by
    rw [← h_quot_exp]; exact Monoid.pow_exponent_eq_one _
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h_pow_eq_one
  exact h_pow_eq_one

/-- **Lem 6.15 odd-p helper**: the kernel of `θ : T → T, x ↦ x^p` has order ≥ p².
Given the commutator structure (class ≤ 2) with `|commutator T| = p` (Step 0)
and `|T : Z(T)| = p²`. -/
private lemma card_setOfPowEqOne_ge_pow_two_of_index_pow_two_odd
    {T : Type*} [Group T] [Finite T] {p : ℕ} [hp : Fact p.Prime]
    (hp_odd : Odd p) (h_idx : (Subgroup.center T).index = p ^ 2)
    (hC : _root_.commutator T ≤ Subgroup.center T)
    (h_commp : ∀ c ∈ _root_.commutator T, c ^ p = 1) :
    p ^ 2 ≤ Nat.card (OddOrder.Isaacs.Ch04.setOfPowEqOne hC hp_odd) := by
  -- Define θ : T → T as a homomorphism (Ch04.powPHom). Use Lagrange: |K| · |im| = |T|.
  let θ := OddOrder.Isaacs.Ch04.powPHom hC hp_odd h_commp
  -- ker θ = setOfPowEqOne
  have h_ker_eq : θ.ker = OddOrder.Isaacs.Ch04.setOfPowEqOne hC hp_odd := by
    ext x
    constructor
    · intro hx
      change x ^ p = 1
      exact hx
    · intro hx
      change x ^ p = 1 at hx
      exact hx
  -- im θ ⊆ Z(T)
  have h_im_le_Z : θ.range ≤ Subgroup.center T := by
    rintro _ ⟨x, rfl⟩
    change x ^ p ∈ Subgroup.center T
    exact pow_p_mem_center_of_index_pow_two_odd h_idx x
  -- |ker| · |im| = |T| and |im| ≤ |Z(T)|, so |ker| ≥ |T| / |Z(T)| = p²
  have h_lag : Nat.card θ.ker * θ.ker.index = Nat.card T :=
    Subgroup.card_mul_index _
  rw [Subgroup.index_ker] at h_lag
  have h_im_card_le : Nat.card θ.range ≤ Nat.card (Subgroup.center T) :=
    Subgroup.card_le_of_le h_im_le_Z
  rw [h_ker_eq] at h_lag
  -- |T| = (Z(T)).index * |Z(T)| = p² * |Z(T)|
  have hT_card : Nat.card T = p ^ 2 * Nat.card (Subgroup.center T) := by
    have := (Subgroup.center T).index_mul_card
    rw [h_idx] at this
    exact this.symm
  rw [hT_card] at h_lag
  -- p² * |Z(T)| ≤ |K| * |Z(T)| (using h_im_card_le and h_lag)
  have hZ_pos : 0 < Nat.card (Subgroup.center T) := Nat.card_pos
  by_contra hKlt
  push Not at hKlt
  -- |K| < p² ⇒ |K| * |Z(T)| < p² * |Z(T)|. But |K| * |im θ| = |T| = p² * |Z(T)|
  -- and |im θ| ≤ |Z(T)|.
  have h_lt : Nat.card (OddOrder.Isaacs.Ch04.setOfPowEqOne hC hp_odd) * Nat.card θ.range
            < p ^ 2 * Nat.card (Subgroup.center T) := by
    calc Nat.card (OddOrder.Isaacs.Ch04.setOfPowEqOne hC hp_odd) * Nat.card θ.range
        ≤ Nat.card (OddOrder.Isaacs.Ch04.setOfPowEqOne hC hp_odd) * Nat.card (Subgroup.center T) :=
          Nat.mul_le_mul_left _ h_im_card_le
      _ < p ^ 2 * Nat.card (Subgroup.center T) := by
          exact (Nat.mul_lt_mul_right hZ_pos).mpr hKlt
  omega

/-- **Lem 6.15 odd-p helper**: `K ⊓ C` has order ≤ p, where `K = {x | x^p = 1}` and
`C` is cyclic. This uses: subgroup of cyclic is cyclic, and a cyclic group all of whose
elements have order dividing p has order ≤ p. -/
private lemma card_setOfPowEqOne_inf_le_prime
    {T : Type*} [Group T] [Finite T] {p : ℕ} [hp : Fact p.Prime]
    (hp_odd : Odd p) (hC : _root_.commutator T ≤ Subgroup.center T)
    {C : Subgroup T} (hC_cyclic : IsCyclic C) :
    Nat.card ((OddOrder.Isaacs.Ch04.setOfPowEqOne hC hp_odd) ⊓ C : Subgroup T) ≤ p := by
  -- The inf K ⊓ C is a subgroup of C (cyclic), hence cyclic.
  set K := OddOrder.Isaacs.Ch04.setOfPowEqOne hC hp_odd with hK_def
  -- Every element x ∈ K ⊓ C satisfies x^p = 1, so orderOf x ∣ p, i.e., orderOf x = 1 or p.
  -- A finite cyclic group all of whose elements have order dividing p has order ≤ p.
  -- Approach: take generator g of K ⊓ C (cyclic); g^p = 1; orderOf g ≤ p; |K ⊓ C| = orderOf g.
  have : IsCyclic ((K ⊓ C : Subgroup T).subgroupOf C) :=
    Subgroup.isCyclic_of_le (le_top : (K ⊓ C : Subgroup T).subgroupOf C ≤ ⊤)
  -- The subgroup K ⊓ C ↪ C is cyclic.
  have : IsCyclic (K ⊓ C : Subgroup T) := by
    -- Use isCyclic_of_le with K ⊓ C ≤ C: but this needs a coercion from Subgroup C, while
    -- here both K ⊓ C and C are subgroups of T. We use the equivalence via subgroupOf.
    refine isCyclic_of_injective ((K ⊓ C : Subgroup T).inclusion (inf_le_right : K ⊓ C ≤ C)) ?_
    exact Subgroup.inclusion_injective _
  -- Every element x ∈ K ⊓ C satisfies x^p = 1, so the exponent of K ⊓ C divides p.
  -- Since K ⊓ C is cyclic, its exponent equals its cardinality, hence |K ⊓ C| ≤ p.
  have h_exp_dvd : Monoid.exponent (K ⊓ C : Subgroup T) ∣ p := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro x
    apply Subtype.ext
    change ((x : T) ^ p : T) = (1 : T)
    have h_mem : (x : T) ∈ K := (Subgroup.mem_inf.mp x.2).1
    exact h_mem
  have h_card_eq : Nat.card (K ⊓ C : Subgroup T) = Monoid.exponent (K ⊓ C : Subgroup T) :=
    (IsCyclic.exponent_eq_card (α := (K ⊓ C : Subgroup T))).symm
  rw [h_card_eq]
  exact Nat.le_of_dvd hp.out.pos h_exp_dvd

/-- **Lem 6.15 odd-p helper**: `|K| ≤ p²` where `K = {x | x^p = 1}`.
Use `|K| = |K : K ⊓ C| · |K ⊓ C|`, `|K : K ⊓ C| = C.relIndex K ≤ C.index = p`, and
`|K ⊓ C| ≤ p`. -/
private lemma card_setOfPowEqOne_le_pow_two_of_index_pow_two_odd
    {T : Type*} [Group T] [Finite T] {p : ℕ} [hp : Fact p.Prime]
    (hp_odd : Odd p) (h_idx : (Subgroup.center T).index = p ^ 2)
    (hC : _root_.commutator T ≤ Subgroup.center T)
    {C : Subgroup T} (hC_cyclic : IsCyclic C)
    (hZ_lt_C : Subgroup.center T < C) (hC_lt_T : C < ⊤) :
    Nat.card (OddOrder.Isaacs.Ch04.setOfPowEqOne hC hp_odd) ≤ p ^ 2 := by
  set K := OddOrder.Isaacs.Ch04.setOfPowEqOne hC hp_odd with hK_def
  have hC_idx : C.index = p :=
    index_eq_prime_of_center_lt_of_center_index_pow_two h_idx hZ_lt_C hC_lt_T
  have h_int_le : Nat.card (K ⊓ C : Subgroup T) ≤ p :=
    card_setOfPowEqOne_inf_le_prime hp_odd hC hC_cyclic
  -- |K : K ⊓ C| · |K ⊓ C| = |K| in subgroup K. The standard fact is
  -- (K ⊓ C).relIndex K = C.relIndex K, and `relIndex_le_of_le_right` then bounds
  -- `C.relIndex K ≤ C.relIndex ⊤ = C.index = p`.
  have hC_idx_ne_zero : C.index ≠ 0 := by rw [hC_idx]; exact hp.out.ne_zero
  have hC_relIndex_le : C.relIndex K ≤ C.index := by
    have h := Subgroup.relIndex_le_of_le_right (H := C) (K := K) (L := ⊤) le_top ?_
    · simpa [Subgroup.relIndex_top_right] using h
    · simp [Subgroup.relIndex_top_right, hC_idx_ne_zero]
  -- (K ⊓ C).index_within_K equals C.relIndex K.
  -- Use the Lagrange relation in K. Lemma: H ⊆ K' with H.subgroupOf K' has
  -- (H.subgroupOf K').index = K'.relIndex (H ⊔ K') ... we'll just use:
  -- |K| = (C.subgroupOf K).index * Nat.card (C.subgroupOf K) (subgroup of K)
  -- But Nat.card (C.subgroupOf K) = Nat.card (K ⊓ C). Let's use directly.
  have h_lag_in_K :
      (C.subgroupOf K).index * Nat.card (C.subgroupOf K) = Nat.card K :=
    Subgroup.index_mul_card _
  -- (C.subgroupOf K).index = C.relIndex K by definition.
  have h_relIndex_def : C.relIndex K = (C.subgroupOf K).index := rfl
  -- Nat.card (C.subgroupOf K) = Nat.card (K ⊓ C : Subgroup T).
  have h_card_subgroupOf : Nat.card (C.subgroupOf K) = Nat.card (K ⊓ C : Subgroup T) := by
    refine Nat.card_congr ?_
    refine {
      toFun := fun x => ⟨((x : K) : T), ?_⟩
      invFun := fun y => ⟨⟨(y : T), (Subgroup.mem_inf.mp y.2).1⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_
    }
    · -- ((x : K) : T) ∈ K ⊓ C
      refine Subgroup.mem_inf.mpr ⟨(x : K).2, ?_⟩
      have := x.2
      rw [Subgroup.mem_subgroupOf] at this
      exact this
    · rw [Subgroup.mem_subgroupOf]
      exact (Subgroup.mem_inf.mp y.2).2
    · intro x; rfl
    · intro y; rfl
  rw [h_card_subgroupOf, ← h_relIndex_def] at h_lag_in_K
  -- |K| = C.relIndex K * |K ⊓ C| ≤ p * p = p².
  rw [← h_lag_in_K]
  calc C.relIndex K * Nat.card (K ⊓ C : Subgroup T)
      ≤ p * p := by
        have h1 : C.relIndex K ≤ p := by rw [← hC_idx]; exact hC_relIndex_le
        exact Nat.mul_le_mul h1 h_int_le
    _ = p ^ 2 := by ring

/-- **Isaacs Lemma 6.15** (odd `p` case): Let `T` be a group with `|T : Z(T)| = p²` and a
cyclic subgroup `C` with `Z(T) < C < T`. If `p` is odd, then there is a characteristic
elementary abelian subgroup of `T` of order `p²` (specifically `K = {x | x^p = 1}`). -/
private theorem char_elementaryAbelian_p_sq_of_index_p_sq_odd
    {T : Type*} [Group T] [Finite T] {p : ℕ} [hp : Fact p.Prime]
    (hp_odd : Odd p) (h_idx : (Subgroup.center T).index = p ^ 2)
    {C : Subgroup T} (hC_cyclic : IsCyclic C)
    (hZ_lt_C : Subgroup.center T < C) (hC_lt_T : C < ⊤) :
    ∃ K : Subgroup T, K.Characteristic ∧
      IsElementaryAbelian p K ∧ Nat.card K = p ^ 2 := by
  have hC : _root_.commutator T ≤ Subgroup.center T :=
    commutator_le_center_of_index_pow_two h_idx
  have hC_normal : C.Normal :=
    normal_of_center_le_of_center_index_pow_two h_idx hZ_lt_C.le
  -- |commutator T| = p
  have h_card_comm : Nat.card (_root_.commutator T) = p :=
    card_commutator_eq_prime_of_lem_6_15 h_idx hC_cyclic hC_lt_T hZ_lt_C
  -- Every element of commutator T has order ∣ p (Lagrange), so c^p = 1.
  have h_commp : ∀ c ∈ _root_.commutator T, c ^ p = 1 := by
    intro c hc
    -- Work in the subgroup commutator T (as a group), use Nat.card.
    have h_pow_in : (⟨c, hc⟩ : _root_.commutator T) ^ Nat.card (_root_.commutator T) = 1 :=
      pow_card_eq_one'
    rw [h_card_comm] at h_pow_in
    have : ((⟨c, hc⟩ : _root_.commutator T) ^ p : _root_.commutator T) = (1 : _root_.commutator
        T) :=
      h_pow_in
    have h_pow' : (c : T) ^ p = 1 := by
      have h1 := congrArg Subtype.val this
      simpa using h1
    exact h_pow'
  -- K = ker (x ↦ x^p), realized as setOfPowEqOne.
  set K := OddOrder.Isaacs.Ch04.setOfPowEqOne hC hp_odd with hK_def
  refine ⟨K, ?_, ?_, ?_⟩
  · exact setOfPowEqOne_characteristic_of_class_le_two_odd hp_odd hC
  · -- K is elementary abelian: K commutes pointwise (subset of abelian T? No, T might be
    -- nonabelian. But K ⊆ ... wait, the def of IsElementaryAbelian is commutativity in K,
    -- and every element to the p is 1.)
    -- We need: ∀ x y ∈ K, xy = yx; and ∀ x ∈ K, x^p = 1.
    -- The second is by definition of K. The first: K ⊆ Z(T)? No, that's stronger than needed.
    -- Actually: K has order p², so K of prime-square order is abelian (by mathlib
    -- `IsPGroup.isMulCommutative_of_card_eq_prime_sq`).
    -- But we need K's order. We have |K| ≥ p² and |K| ≤ p², so |K| = p².
    have h_card_ge : p ^ 2 ≤ Nat.card K :=
      card_setOfPowEqOne_ge_pow_two_of_index_pow_two_odd hp_odd h_idx hC h_commp
    have h_card_le : Nat.card K ≤ p ^ 2 :=
      card_setOfPowEqOne_le_pow_two_of_index_pow_two_odd hp_odd h_idx hC hC_cyclic hZ_lt_C hC_lt_T
    have h_card : Nat.card K = p ^ 2 := le_antisymm h_card_le h_card_ge
    refine ⟨?_, ?_⟩
    · -- commute
      exact isMulCommutative_iff.mp
        (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := p) (G := K) h_card)
    · -- ∀ x : K, x^p = 1
      intro x
      apply Subtype.ext
      change ((x : T) ^ p : T) = (1 : T)
      have h_mem : (x : T) ∈ K := x.2
      change (x : T) ^ p = 1 at h_mem
      exact h_mem
  · -- |K| = p²
    have h_card_ge : p ^ 2 ≤ Nat.card K :=
      card_setOfPowEqOne_ge_pow_two_of_index_pow_two_odd hp_odd h_idx hC h_commp
    have h_card_le : Nat.card K ≤ p ^ 2 :=
      card_setOfPowEqOne_le_pow_two_of_index_pow_two_odd hp_odd h_idx hC hC_cyclic hZ_lt_C hC_lt_T
    exact le_antisymm h_card_le h_card_ge

/-- **Isaacs Lemma 6.15** (odd prime case).

Let `T` be a finite group with `|T : Z(T)| = p^2` and a cyclic subgroup `C` with
`Z(T) < C < T`. If `p` is odd, then `T` has a characteristic elementary abelian subgroup
of order `p^2`.

The full `p = 2` branch is handled separately below; this theorem exposes the completed
odd-`p` half for later Ch.6/Ch.7 use. -/
theorem exists_characteristic_isElementaryAbelian_of_center_index_prime_sq_odd
    {T : Type*} [Group T] [Finite T] {p : ℕ} [hp : Fact p.Prime]
    (hp_odd : Odd p) (h_idx : (Subgroup.center T).index = p ^ 2)
    {C : Subgroup T} (hC_cyclic : IsCyclic C)
    (hZ_lt_C : Subgroup.center T < C) (hC_lt_T : C < ⊤) :
    ∃ K : Subgroup T, K.Characteristic ∧
      IsElementaryAbelian p K ∧ Nat.card K = p ^ 2 :=
  char_elementaryAbelian_p_sq_of_index_p_sq_odd
    hp_odd h_idx hC_cyclic hZ_lt_C hC_lt_T

/-- **Lem 6.15 `p = 2` sub-lemma**: a finite abelian 2-group with a cyclic subgroup of
index 2 that is itself not cyclic has a characteristic elementary abelian subgroup of order 4
(namely `{x | x² = 1}`).

mmd L3535-3536: "If A is abelian noncyclic and B ⊆ A is cyclic of index 2, then {a | a² = 1}
is characteristic elementary abelian of order 4 in A." -/
private theorem char_elementaryAbelian_4_of_noncyclic_abelian_2group
    {A : Type*} [Group A] [Finite A] (hAb : ∀ x y : A, x * y = y * x)
    (h_two : IsPGroup 2 A)
    {D : Subgroup A} (hD_cyc : IsCyclic D) (hD_idx : D.index = 2)
    (h_not_cyclic : ¬ IsCyclic A) :
    ∃ K : Subgroup A, K.Characteristic ∧
      IsElementaryAbelian 2 K ∧ Nat.card K = 4 := by
  classical
  -- Define K = {x : A | x^2 = 1} as a subgroup (uses abelianness).
  let K : Subgroup A := {
    carrier := {x : A | x ^ 2 = 1}
    one_mem' := by change (1 : A) ^ 2 = 1; exact one_pow 2
    inv_mem' := by
      intro x (hx : x ^ 2 = 1)
      change (x⁻¹) ^ 2 = 1
      rw [inv_pow, hx, inv_one]
    mul_mem' := by
      intro x y (hx : x ^ 2 = 1) (hy : y ^ 2 = 1)
      change (x * y) ^ 2 = 1
      have h : (x * y) ^ 2 = x ^ 2 * y ^ 2 := by
        rw [pow_two, pow_two, pow_two]
        rw [mul_assoc, ← mul_assoc y x y, hAb y x, mul_assoc, ← mul_assoc]
      rw [h, hx, hy, mul_one]
  }
  refine ⟨K, ?_, ?_, ?_⟩
  · -- K is characteristic
    refine ⟨fun φ => ?_⟩
    ext x
    rw [Subgroup.mem_comap]
    change (φ x) ^ 2 = 1 ↔ x ^ 2 = 1
    refine ⟨fun hpx => ?_, fun hpx => ?_⟩
    · rw [← map_pow] at hpx
      have : φ (x ^ 2) = φ 1 := by rw [hpx, map_one]
      exact φ.injective this
    · rw [← map_pow, hpx, map_one]
  · -- K is elementary abelian
    refine ⟨?_, ?_⟩
    · -- commute
      intro x y
      apply Subtype.ext
      change (x : A) * (y : A) = (y : A) * (x : A)
      exact hAb _ _
    · -- ∀ x : K, x^2 = 1
      intro x
      apply Subtype.ext
      change ((x : A) ^ 2 : A) = (1 : A)
      have h_mem : (x : A) ∈ K := x.2
      change (x : A) ^ 2 = 1 at h_mem
      exact h_mem
  · -- |K| = 4. Strategy:
    -- (a) D is normal in A (A abelian).
    -- (b) |D| is a 2-power ≥ 2.
    -- (c) |K ⊓ D| = 2: lower from involution z = d^(|D|/2); upper from cyclic K∩D / exponent 2.
    -- (d) D.relIndex K ∣ D.index = 2 (D normal).
    -- (e) For |K| ≥ 4: construct a' ∈ K \ D, then (K ⊓ D as sub of K) has index ≥ 2 in K.
    have hD_norm : D.Normal := by
      refine ⟨fun n hn g => ?_⟩
      have h_eq : g * n * g⁻¹ = n := by
        rw [hAb g n, mul_assoc, mul_inv_cancel, mul_one]
      rw [h_eq]; exact hn
    -- |D| is a 2-power.
    have hp2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hD_two : IsPGroup 2 (D : Subgroup A) := h_two.to_subgroup D
    obtain ⟨kD, hD_pow⟩ := (IsPGroup.iff_card (p := 2) (G := (D : Subgroup A))).mp hD_two
    -- |D| ≠ 1 (else |A| = 2 ⇒ cyclic).
    have hD_card_ne_one : Nat.card (D : Subgroup A) ≠ 1 := by
      intro h1
      have hA_card : Nat.card A = 2 := by
        have := D.card_mul_index
        rw [hD_idx, h1] at this; omega
      exact h_not_cyclic (isCyclic_of_prime_card hA_card)
    have hkD_pos : 1 ≤ kD := by
      by_contra hlt
      push Not at hlt
      interval_cases kD
      rw [pow_zero] at hD_pow
      exact hD_card_ne_one hD_pow
    -- |D| ≥ 2, |D| even.
    have hD_card_ge_two : 2 ≤ Nat.card (D : Subgroup A) := by
      rw [hD_pow]
      calc (2 : ℕ) = 2 ^ 1 := by ring
        _ ≤ 2 ^ kD := Nat.pow_le_pow_right (by norm_num) hkD_pos
    have hD_card_even : 2 ∣ Nat.card (D : Subgroup A) := by
      rw [hD_pow]; exact dvd_pow_self _ (by omega : kD ≠ 0)
    have hA_card_eq : Nat.card A = 2 * Nat.card (D : Subgroup A) := by
      have := D.index_mul_card
      rw [hD_idx] at this; omega
    set n := Nat.card (D : Subgroup A) with hn_def
    -- Generator of D (in ↥D).
    obtain ⟨d, hd_gen⟩ := IsCyclic.exists_generator (α := (D : Subgroup A))
    have hd_order : orderOf d = n := by
      rw [hn_def]; exact orderOf_eq_card_of_forall_mem_zpowers hd_gen
    -- Involution z := d^(n/2) (in A; via the coercion).
    set z : A := (d : A) ^ (n / 2) with hz_def
    have hz_in_D : z ∈ D := pow_mem d.2 _
    -- (d : A) ^ n = 1.
    have hd_pow_n_amb : (d : A) ^ n = 1 := by
      have h_in_D : (d : (D : Subgroup A)) ^ n = 1 := by
        rw [← hd_order]; exact pow_orderOf_eq_one d
      have : (((d : (D : Subgroup A)) ^ n : (D : Subgroup A)) : A) =
          ((1 : (D : Subgroup A)) : A) := by
        rw [h_in_D]
      simpa [SubmonoidClass.coe_pow] using this
    have hz_sq : z ^ 2 = 1 := by
      rw [hz_def, ← pow_mul]
      have h_mul : (n / 2) * 2 = n := by
        have := Nat.mul_div_cancel' hD_card_even
        omega
      rw [h_mul]; exact hd_pow_n_amb
    have hn_half_pos : 0 < n / 2 := by
      have : 2 ≤ n := hD_card_ge_two; omega
    have hn_half_lt : n / 2 < n := Nat.div_lt_self (by omega) (by norm_num)
    have hz_ne_one : z ≠ 1 := by
      intro h
      have hd_pow_half : (d : (D : Subgroup A)) ^ (n / 2) = 1 := by
        apply Subtype.ext
        change (((d : (D : Subgroup A)) ^ (n / 2) : (D : Subgroup A)) : A) = (1 : A)
        rw [SubmonoidClass.coe_pow]; exact h
      have hdvd : orderOf d ∣ (n / 2) := orderOf_dvd_of_pow_eq_one hd_pow_half
      rw [hd_order] at hdvd
      have := Nat.le_of_dvd hn_half_pos hdvd
      omega
    have hz_in_K : z ∈ K := hz_sq
    -- |K ⊓ D| ≥ 2.
    have h_inf_ge_two : 2 ≤ Nat.card (K ⊓ D : Subgroup A) := by
      have h1_in : (1 : A) ∈ (K ⊓ D : Subgroup A) := Subgroup.one_mem _
      have hz_in : z ∈ (K ⊓ D : Subgroup A) := Subgroup.mem_inf.mpr ⟨hz_in_K, hz_in_D⟩
      have h_ne : (⟨z, hz_in⟩ : (K ⊓ D : Subgroup A)) ≠ ⟨1, h1_in⟩ := by
        intro heq
        exact hz_ne_one (Subtype.mk_eq_mk.mp heq)
      have h_finset_card :
          ({⟨1, h1_in⟩, ⟨z, hz_in⟩} : Finset (K ⊓ D : Subgroup A)).card = 2 := by
        rw [Finset.card_insert_of_notMem, Finset.card_singleton]
        intro hmem
        rw [Finset.mem_singleton] at hmem
        exact h_ne hmem.symm
      have : Fintype (K ⊓ D : Subgroup A) := Fintype.ofFinite _
      have h_le_card : ({⟨1, h1_in⟩, ⟨z, hz_in⟩} : Finset (K ⊓ D : Subgroup A)).card
          ≤ Fintype.card (K ⊓ D : Subgroup A) := Finset.card_le_univ _
      rw [Nat.card_eq_fintype_card]
      omega
    -- |K ⊓ D| ≤ 2: K ⊓ D ≤ D cyclic, exponent dvd 2.
    have h_inf_le_two : Nat.card (K ⊓ D : Subgroup A) ≤ 2 := by
      have : IsCyclic ((K ⊓ D : Subgroup A) : Subgroup A) := by
        refine isCyclic_of_injective ((K ⊓ D : Subgroup A).inclusion
          (inf_le_right : K ⊓ D ≤ D)) ?_
        exact Subgroup.inclusion_injective _
      have h_exp_dvd : Monoid.exponent (K ⊓ D : Subgroup A) ∣ 2 := by
        rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
        intro x
        apply Subtype.ext
        change ((x : (K ⊓ D : Subgroup A)) : A) ^ 2 = (1 : A)
        have h_mem : (x : A) ∈ K := (Subgroup.mem_inf.mp x.2).1
        change (x : A) ^ 2 = 1 at h_mem
        exact h_mem
      have h_card_eq : Nat.card (K ⊓ D : Subgroup A) =
          Monoid.exponent (K ⊓ D : Subgroup A) :=
        (IsCyclic.exponent_eq_card (α := (K ⊓ D : Subgroup A))).symm
      rw [h_card_eq]
      exact Nat.le_of_dvd (by norm_num) h_exp_dvd
    have h_inf_eq_two : Nat.card (K ⊓ D : Subgroup A) = 2 :=
      le_antisymm h_inf_le_two h_inf_ge_two
    -- D.relIndex K ∣ 2 (D normal).
    have h_relIndex_dvd : D.relIndex K ∣ 2 := by
      rw [← hD_idx]
      exact Subgroup.relIndex_dvd_index_of_normal D K
    have h_card_subgroupOf : Nat.card (D.subgroupOf K) = Nat.card (K ⊓ D : Subgroup A) := by
      refine Nat.card_congr ?_
      refine {
        toFun := fun x => ⟨((x : K) : A), ?_⟩
        invFun := fun y => ⟨⟨(y : A), (Subgroup.mem_inf.mp y.2).1⟩, ?_⟩
        left_inv := ?_
        right_inv := ?_
      }
      · refine Subgroup.mem_inf.mpr ⟨(x : K).2, ?_⟩
        have := x.2
        rw [Subgroup.mem_subgroupOf] at this
        exact this
      · rw [Subgroup.mem_subgroupOf]
        exact (Subgroup.mem_inf.mp y.2).2
      · intro x; rfl
      · intro y; rfl
    have h_lag :
        (D.subgroupOf K).index * Nat.card (D.subgroupOf K) = Nat.card K :=
      Subgroup.index_mul_card _
    have h_relIndex_eq : D.relIndex K = (D.subgroupOf K).index := rfl
    rw [h_card_subgroupOf, h_inf_eq_two] at h_lag
    -- |K| ≤ 4 from D.relIndex K ≤ 2.
    have h_relIndex_le : D.relIndex K ≤ 2 := Nat.le_of_dvd (by norm_num) h_relIndex_dvd
    have h_K_le_4 : Nat.card K ≤ 4 := by
      rw [h_relIndex_eq] at h_relIndex_le
      have h_mul : (D.subgroupOf K).index * 2 ≤ 2 * 2 :=
        Nat.mul_le_mul_right 2 (by rw [← h_relIndex_eq]; exact h_relIndex_le)
      omega
    -- |K| ≥ 4. Use existence of a' ∈ K \ D.
    -- First, pick a ∈ A with a ∉ D.
    obtain ⟨a, ha_notmem, _ha_or⟩ :=
      (Subgroup.index_eq_two_iff_exists_notMem_and (H := D)).mp hD_idx
    have ha_sq : a ^ 2 ∈ D := Subgroup.sq_mem_of_index_two hD_idx a
    -- orderOf a < |A| (otherwise A cyclic).
    have ha_order_lt : orderOf a < Nat.card A := by
      by_contra hge
      push Not at hge
      have h_le : orderOf a ≤ Nat.card A := orderOf_le_card
      have ha_order_eq : orderOf a = Nat.card A := le_antisymm h_le hge
      apply h_not_cyclic
      refine ⟨⟨a, ?_⟩⟩
      intro x
      have hz_card : Nat.card (Subgroup.zpowers a) = Nat.card A := by
        rw [Nat.card_zpowers, ha_order_eq]
      have hz_top : Subgroup.zpowers a = ⊤ :=
        (Subgroup.card_eq_iff_eq_top (H := Subgroup.zpowers a)).mp hz_card
      have hxin : x ∈ Subgroup.zpowers a := by rw [hz_top]; trivial
      rw [Subgroup.mem_zpowers_iff] at hxin
      obtain ⟨k, hk⟩ := hxin
      exact ⟨k, hk⟩
    -- orderOf a is a 2-power.
    obtain ⟨ka, ha_order_pow_eq⟩ := (IsPGroup.iff_orderOf.mp h_two) a
    have hA_card_pow : Nat.card A = 2 ^ (kD + 1) := by
      rw [hA_card_eq, hD_pow, pow_succ]; ring
    have hka_le : ka ≤ kD := by
      have h1 : 2 ^ ka < 2 ^ (kD + 1) := by
        rw [← ha_order_pow_eq, ← hA_card_pow]; exact ha_order_lt
      have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h1
      omega
    have ha_order_dvd : orderOf a ∣ n := by
      rw [ha_order_pow_eq]
      have hn_pow : n = 2 ^ kD := by
        simpa [hn_def] using hD_pow
      rw [hn_pow]
      exact pow_dvd_pow _ hka_le
    have ha_pow_n : a ^ n = 1 := orderOf_dvd_iff_pow_eq_one.mp ha_order_dvd
    -- (a^2)^(n/2) = a^n = 1.
    have ha_sq_pow_half : (a ^ 2) ^ (n / 2) = 1 := by
      rw [← pow_mul]
      have h_mul : 2 * (n / 2) = n := Nat.mul_div_cancel' hD_card_even
      rw [h_mul]; exact ha_pow_n
    -- a^2 viewed in ↥D.
    let a2D : (D : Subgroup A) := ⟨a ^ 2, ha_sq⟩
    have ha2D_in_zpowers : a2D ∈ Subgroup.zpowers d := hd_gen a2D
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp ha2D_in_zpowers
    -- (a2D)^(n/2) = 1 in ↥D.
    have ha2D_pow_half : a2D ^ (n / 2) = 1 := by
      apply Subtype.ext
      change ((a2D ^ (n / 2) : (D : Subgroup A)) : A) = (1 : A)
      rw [SubmonoidClass.coe_pow]
      change (a ^ 2) ^ (n / 2) = 1
      exact ha_sq_pow_half
    -- d^(m * (n/2)) = (d^m)^(n/2) = (a2D)^(n/2) = 1, so orderOf d ∣ m * (n/2), i.e. n ∣ m*(n/2).
    have hm_two_dvd : (2 : ℤ) ∣ m := by
      have h1 : d ^ (m * ((n / 2 : ℕ) : ℤ)) = 1 := by
        rw [zpow_mul, hm, zpow_natCast]; exact ha2D_pow_half
      have h2 : (orderOf d : ℤ) ∣ m * ((n / 2 : ℕ) : ℤ) :=
        (orderOf_dvd_iff_zpow_eq_one (x := d)
          (i := m * ((n / 2 : ℕ) : ℤ))).mpr h1
      rw [hd_order] at h2
      have hn_eq_int : (n : ℤ) = 2 * ((n / 2 : ℕ) : ℤ) := by
        have hh := Nat.mul_div_cancel' hD_card_even
        have : (2 * (n / 2) : ℕ) = n := hh
        push_cast at this ⊢
        omega
      rw [hn_eq_int] at h2
      have h2' : 2 * ((n / 2 : ℕ) : ℤ) ∣ m * ((n / 2 : ℕ) : ℤ) := h2
      have hn_half_pos_int : (0 : ℤ) < ((n / 2 : ℕ) : ℤ) := by exact_mod_cast hn_half_pos
      -- 2 * (n/2) ∣ m * (n/2)
      obtain ⟨q, hq⟩ := h2'
      -- 2 * (n/2) * q = m * (n/2)
      have h_q : ((n / 2 : ℕ) : ℤ) * (2 * q) =
          ((n / 2 : ℕ) : ℤ) * m := by
        calc
          ((n / 2 : ℕ) : ℤ) * (2 * q) = (2 * ((n / 2 : ℕ) : ℤ)) * q := by ring
          _ = m * ((n / 2 : ℕ) : ℤ) := hq.symm
          _ = ((n / 2 : ℕ) : ℤ) * m := by ring
      have h_can : 2 * q = m := mul_left_cancel₀ hn_half_pos_int.ne' h_q
      exact ⟨q, h_can.symm⟩
    obtain ⟨m', hm'⟩ := hm_two_dvd
    -- Define a' := a * d^(-m').
    set a' : A := a * (d : A) ^ (-m') with ha'_def
    -- (a')^2 = a^2 · d^(-2m') = d^m · d^(-2m') = 1 (using abelianness).
    have ha2_eq_zpow : a ^ 2 = (d : A) ^ m := by
      have h := congrArg (fun (x : (D : Subgroup A)) => (x : A)) hm
      simp only [SubgroupClass.coe_zpow] at h
      exact h.symm
    have ha'_sq : a' ^ 2 = 1 := by
      have hab : ∀ u v : A, u * v = v * u := hAb
      have h_expand : a' * a' = a * a * ((d : A) ^ (-m') * (d : A) ^ (-m')) := by
        rw [ha'_def]
        rw [mul_assoc, ← mul_assoc ((d : A) ^ (-m')) a, hab ((d : A) ^ (-m')) a]
        rw [mul_assoc, ← mul_assoc]
      rw [pow_two, h_expand, ← pow_two, ← pow_two, ha2_eq_zpow]
      have h_neg_sq : ((d : A) ^ (-m')) ^ 2 =
          (d : A) ^ ((-m') * 2 : ℤ) := by
        rw [← zpow_natCast ((d : A) ^ (-m')) 2, ← zpow_mul]
        ring_nf
      rw [h_neg_sq]
      rw [← zpow_add]
      have h_exp : m + (-m') * 2 = 0 := by rw [hm']; ring
      rw [h_exp, zpow_zero]
    -- a' ∉ D.
    have ha'_notmem : a' ∉ D := by
      intro hin
      have h_d_inv : (d : A) ^ (-m') ∈ D := zpow_mem d.2 _
      have h_a : a ∈ D := by
        have : a = a' * ((d : A) ^ (-m'))⁻¹ := by
          rw [ha'_def, mul_assoc, mul_inv_cancel, mul_one]
        rw [this]
        exact Subgroup.mul_mem _ hin (Subgroup.inv_mem _ h_d_inv)
      exact ha_notmem h_a
    have ha'_in_K : a' ∈ K := ha'_sq
    -- K has at least 4 elements: 1, z, a', a'*z. Need them all distinct.
    -- 1 ≠ z ✓ (hz_ne_one). 1 ∈ D, z ∈ D, a' ∉ D, a'*z ∉ D (else a' = (a'*z)*z⁻¹ ∈ D).
    -- Also a' ≠ a'*z (else z = 1).
    have hz_K_in : z ∈ K := hz_in_K
    have ha'z_in_K : a' * z ∈ K := K.mul_mem ha'_in_K hz_K_in
    have ha'z_notmem : a' * z ∉ D := by
      intro hin
      have hz_in_D' : z ∈ D := hz_in_D
      have : a' ∈ D := by
        have heq : a' = (a' * z) * z⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
        rw [heq]
        exact Subgroup.mul_mem _ hin (Subgroup.inv_mem _ hz_in_D')
      exact ha'_notmem this
    -- Define the four elements as a Finset in K.
    have h_one_in_K : (1 : A) ∈ K := K.one_mem
    -- Now build the cardinality.
    have : Fintype K := Fintype.ofFinite _
    let S : Finset K :=
      {⟨1, h_one_in_K⟩, ⟨z, hz_K_in⟩, ⟨a', ha'_in_K⟩, ⟨a' * z, ha'z_in_K⟩}
    have hS_card : S.card = 4 := by
      dsimp [S]
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton]
      · -- ⟨a', ..⟩ ∉ {⟨a'*z, ..⟩}
        intro h
        rw [Finset.mem_singleton] at h
        have heq : a' = a' * z := congrArg Subtype.val h
        have hz_eq : z = 1 := by
          have : a' * 1 = a' * z := by rw [mul_one]; exact heq
          exact (mul_left_cancel this).symm
        exact hz_ne_one hz_eq
      · -- ⟨z, ..⟩ ∉ {⟨a', ..⟩, ⟨a'*z, ..⟩}
        intro h
        rw [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with h | h
        · have heq : z = a' := congrArg Subtype.val h
          have : a' ∈ D := heq ▸ hz_in_D
          exact ha'_notmem this
        · have heq : z = a' * z := congrArg Subtype.val h
          have : a' * z ∈ D := heq ▸ hz_in_D
          exact ha'z_notmem this
      · -- ⟨1, ..⟩ ∉ {⟨z, ..⟩, ⟨a', ..⟩, ⟨a'*z, ..⟩}
        intro h
        rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with h | h | h
        · have heq : (1 : A) = z := congrArg Subtype.val h
          exact hz_ne_one heq.symm
        · have heq : (1 : A) = a' := congrArg Subtype.val h
          have : a' ∈ D := heq ▸ D.one_mem
          exact ha'_notmem this
        · have heq : (1 : A) = a' * z := congrArg Subtype.val h
          have : a' * z ∈ D := heq ▸ D.one_mem
          exact ha'z_notmem this
    have h_K_ge_4 : 4 ≤ Nat.card K := by
      rw [Nat.card_eq_fintype_card]
      have := Finset.card_le_univ S
      omega
    omega

/-- **Isaacs Lemma 6.15** (`p = 2` abelian index-two branch).

If `A` is a finite abelian `2`-group with a cyclic subgroup of index `2`, and `A` is
not cyclic, then `A` contains a characteristic elementary abelian subgroup of order `4`.

This is the standalone `p = 2` sub-lemma used in the full Lemma 6.15 proof and in the
later `p`-group classification route toward Isaacs 6.11. -/
theorem exists_characteristic_isElementaryAbelian_four_of_noncyclic_abelian_two_group
    {A : Type*} [Group A] [Finite A] (hAb : ∀ x y : A, x * y = y * x)
    (h_two : IsPGroup 2 A)
    {D : Subgroup A} (hD_cyc : IsCyclic D) (hD_idx : D.index = 2)
    (h_not_cyclic : ¬ IsCyclic A) :
    ∃ K : Subgroup A, K.Characteristic ∧
      IsElementaryAbelian 2 K ∧ Nat.card K = 4 :=
  char_elementaryAbelian_4_of_noncyclic_abelian_2group
    hAb h_two hD_cyc hD_idx h_not_cyclic

/-- **Isaacs Lemma 6.15** (`p = 2` quotient lift setup).

Under the `p = 2` hypotheses through the first quotient step, applying the abelian index-two
branch to `T/T'` produces a characteristic subgroup upstairs whose image in `T/T'` is elementary
abelian of order `4`. -/
theorem exists_characteristic_lift_quotient_commutator_four_of_center_index_four
    {T : Type*} [Group T] [Finite T] (hT_two : IsPGroup 2 T)
    (h_idx : (Subgroup.center T).index = 2 ^ 2)
    {C : Subgroup T} (hC_cyclic : IsCyclic C)
    (hC_lt_T : C < ⊤) (hZ_lt_C : Subgroup.center T < C) :
    ∃ E : Subgroup T, E.Characteristic ∧
      _root_.commutator T ≤ E ∧
      IsElementaryAbelian 2 (E.map (QuotientGroup.mk' (_root_.commutator T))) ∧
      Nat.card (E.map (QuotientGroup.mk' (_root_.commutator T))) = 4 := by
  let D : Subgroup (T ⧸ _root_.commutator T) :=
    C.map (QuotientGroup.mk' (_root_.commutator T))
  have hD : IsCyclic D ∧ D.index = 2 := by
    simpa [D] using
      quotient_commutator_image_cyclic_index_two_of_center_index_four
        h_idx hC_cyclic hC_lt_T hZ_lt_C
  have hQ_ab : ∀ x y : T ⧸ _root_.commutator T, x * y = y * x :=
    quotient_commutator_commutative
  have hQ_two : IsPGroup 2 (T ⧸ _root_.commutator T) :=
    hT_two.to_quotient (_root_.commutator T)
  have hQ_not_cyclic : ¬ IsCyclic (T ⧸ _root_.commutator T) :=
    quotient_commutator_not_isCyclic_of_center_index_prime_sq h_idx
  obtain ⟨K, hK_char, hK_elem, hK_card⟩ :=
    exists_characteristic_isElementaryAbelian_four_of_noncyclic_abelian_two_group
      (A := T ⧸ _root_.commutator T) hQ_ab hQ_two
      (D := D) hD.1 hD.2 hQ_not_cyclic
  let E : Subgroup T := K.comap (QuotientGroup.mk' (_root_.commutator T))
  have hE_map :
      E.map (QuotientGroup.mk' (_root_.commutator T)) = K := by
    dsimp [E]
    exact Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective (_root_.commutator T)) K
  refine ⟨E, ?_, ?_, ?_, ?_⟩
  · dsimp [E]
    exact Subgroup.Characteristic.comap_quotient_mk hK_char
  · intro x hx
    dsimp [E]
    change (x : T ⧸ _root_.commutator T) ∈ K
    rw [show (x : T ⧸ _root_.commutator T) = 1 from
      (QuotientGroup.eq_one_iff x).mpr hx]
    exact K.one_mem
  · rwa [hE_map]
  · rwa [hE_map]

/-- **Isaacs Lemma 6.15** (`p = 2` lift cardinality).

If a subgroup `E` contains `T'` and its image in `T/T'` has order `4`, then in the
Lemma 6.15 `p = 2` setup `E` has order `8`. -/
theorem card_lift_quotient_commutator_eq_eight_of_center_index_four
    {T : Type*} [Group T] [Finite T]
    (h_idx : (Subgroup.center T).index = 2 ^ 2)
    {C E : Subgroup T} (hC_cyclic : IsCyclic C)
    (hC_lt_T : C < ⊤) (hZ_lt_C : Subgroup.center T < C)
    (hcomm_le_E : _root_.commutator T ≤ E)
    (hE_image_card :
      Nat.card (E.map (QuotientGroup.mk' (_root_.commutator T))) = 4) :
    Nat.card E = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : C.Normal :=
    normal_of_center_le_of_center_index_pow_two (p := 2) h_idx hZ_lt_C.le
  have hcomm_card : Nat.card (_root_.commutator T) = 2 :=
    card_commutator_eq_prime_of_lem_6_15
      (p := 2) h_idx hC_cyclic hC_lt_T hZ_lt_C
  have hquot_card :
      Nat.card (E ⧸ (_root_.commutator T).subgroupOf E) = 4 := by
    rw [Subgroup.nat_card_quotient_subgroupOf_eq_card_map
      (_root_.commutator T) E]
    exact hE_image_card
  have hsub_card :
      Nat.card ((_root_.commutator T).subgroupOf E) = 2 := by
    exact (Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe hcomm_le_E).toEquiv).trans hcomm_card
  have hsplit :
      Nat.card E =
        Nat.card (E ⧸ (_root_.commutator T).subgroupOf E) *
          Nat.card ((_root_.commutator T).subgroupOf E) :=
    ((_root_.commutator T).subgroupOf E).card_eq_card_quotient_mul_card_subgroup
  rw [hquot_card, hsub_card] at hsplit
  norm_num at hsplit
  exact hsplit

/-- **Isaacs Lemma 6.15** (`p = 2` first lifted subgroup).

The first application of the abelian index-two branch to `T/T'` yields a characteristic
subgroup `E ≤ T` whose quotient image is elementary abelian of order `4`, and whose own
order is `8`. -/
theorem exists_lift_quotient_commutator_order_eight_of_center_index_four
    {T : Type*} [Group T] [Finite T] (hT_two : IsPGroup 2 T)
    (h_idx : (Subgroup.center T).index = 2 ^ 2)
    {C : Subgroup T} (hC_cyclic : IsCyclic C)
    (hC_lt_T : C < ⊤) (hZ_lt_C : Subgroup.center T < C) :
    ∃ E : Subgroup T, E.Characteristic ∧
      _root_.commutator T ≤ E ∧
      IsElementaryAbelian 2 (E.map (QuotientGroup.mk' (_root_.commutator T))) ∧
      Nat.card (E.map (QuotientGroup.mk' (_root_.commutator T))) = 4 ∧
      Nat.card E = 8 := by
  obtain ⟨E, hE_char, hcomm_le_E, hE_elem, hE_image_card⟩ :=
    exists_characteristic_lift_quotient_commutator_four_of_center_index_four
      hT_two h_idx hC_cyclic hC_lt_T hZ_lt_C
  exact ⟨E, hE_char, hcomm_le_E, hE_elem, hE_image_card,
    card_lift_quotient_commutator_eq_eight_of_center_index_four
      h_idx hC_cyclic hC_lt_T hZ_lt_C hcomm_le_E hE_image_card⟩

/-- A finite elementary abelian `2`-group of order `4` is not cyclic. -/
private lemma not_isCyclic_of_isElementaryAbelian_two_card_four
    {A : Type*} [Group A] [Finite A]
    (hElem : IsElementaryAbelian 2 A) (hCard : Nat.card A = 4) :
    ¬ IsCyclic A := by
  exact hElem.not_isCyclic_of_card_prime_sq Nat.prime_two (by simpa using hCard)

/-- If a quotient image of `E` is elementary abelian of order `4`, then `E` is not cyclic. -/
private lemma not_isCyclic_of_quotient_commutator_image_four
    {T : Type*} [Group T] [Finite T] {E : Subgroup T}
    (hE_image_elem :
      IsElementaryAbelian 2 (E.map (QuotientGroup.mk' (_root_.commutator T))))
    (hE_image_card :
      Nat.card (E.map (QuotientGroup.mk' (_root_.commutator T))) = 4) :
    ¬ IsCyclic E := by
  have hImage_not :
      ¬ IsCyclic (E.map (QuotientGroup.mk' (_root_.commutator T))) :=
    not_isCyclic_of_isElementaryAbelian_two_card_four
      hE_image_elem hE_image_card
  intro hE_cyclic
  have : IsCyclic E := hE_cyclic
  exact hImage_not (isCyclic_of_surjective
    ((QuotientGroup.mk' (_root_.commutator T)).subgroupMap E)
    ((QuotientGroup.mk' (_root_.commutator T)).subgroupMap_surjective E))

/-- The intersection of a subgroup with a cyclic subgroup, viewed inside the former, is cyclic. -/
lemma subgroupOf_isCyclic_of_isCyclic
    {T : Type*} [Group T] {C E : Subgroup T} (hC_cyclic : IsCyclic C) :
    IsCyclic (C.subgroupOf E) := by
  have : IsCyclic C := hC_cyclic
  let f : C.subgroupOf E →* C := {
    toFun := fun x => ⟨((x : C.subgroupOf E) : E), by
      have hx : ((x : C.subgroupOf E) : E) ∈ C.subgroupOf E := x.2
      rwa [Subgroup.mem_subgroupOf] at hx⟩
    map_one' := by ext; rfl
    map_mul' := by intro x y; ext; rfl
  }
  exact isCyclic_of_injective f (by
    intro x y hxy
    apply Subtype.ext
    have hT :
        (((x : C.subgroupOf E) : E) : T) =
          (((y : C.subgroupOf E) : E) : T) := by
      simpa [f] using congrArg Subtype.val hxy
    exact Subtype.ext hT)

/-- If `C` has index `2` in `T` and `E` is not contained in `C`, then `C ∩ E` has
index `2` in `E`. -/
private lemma relIndex_eq_two_of_index_two_of_not_le
    {T : Type*} [Group T] {C E : Subgroup T}
    (hC_idx : C.index = 2) (hE_not_le_C : ¬ E ≤ C) :
    C.relIndex E = 2 := by
  rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and]
  rw [SetLike.le_def] at hE_not_le_C
  push Not at hE_not_le_C
  obtain ⟨a, haE, haC⟩ := hE_not_le_C
  refine ⟨a, haE, haC, ?_⟩
  intro b _hbE
  by_cases hbC : b ∈ C
  · exact Or.inr hbC
  · left
    rw [Subgroup.mul_mem_iff_of_index_two hC_idx]
    exact iff_of_false hbC haC

/-- If `C` has index `2`, then any subgroup properly between `C` and `⊤` is impossible. -/
private lemma not_ge_of_ne_of_ne_top_of_index_two
    {T : Type*} [Group T] [Finite T] {C E : Subgroup T}
    (hC_idx : C.index = 2) (hE_ne_C : E ≠ C) (hE_ne_top : E ≠ ⊤) :
    ¬ C ≤ E := by
  intro hC_le_E
  have hmul : C.relIndex E * E.index = 2 := by
    rw [Subgroup.relIndex_mul_index hC_le_E, hC_idx]
  have hrel_pos : 0 < C.relIndex E := by
    exact Nat.pos_of_ne_zero (by
      rw [Subgroup.relIndex]
      exact Subgroup.index_ne_zero_of_finite)
  have hidx_pos : 0 < E.index := by
    exact Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := E))
  have hcases : C.relIndex E = 1 ∨ E.index = 1 := by
    by_contra h
    push Not at h
    have hrel_ge_two : 2 ≤ C.relIndex E := by omega
    have hidx_ge_two : 2 ≤ E.index := by omega
    have hprod_ge : 4 ≤ C.relIndex E * E.index :=
      Nat.mul_le_mul hrel_ge_two hidx_ge_two
    omega
  rcases hcases with hrel | hidx
  · have hE_le_C : E ≤ C := Subgroup.relIndex_eq_one.mp hrel
    exact hE_ne_C (le_antisymm hE_le_C hC_le_E)
  · exact hE_ne_top (Subgroup.index_eq_one.mp hidx)

/-- Finite subgroup cardinality strictly drops for a proper subgroup. -/
private lemma subgroup_card_lt_of_lt_top
    {G : Type*} [Group G] [Finite G] {H : Subgroup G} (hH : H < ⊤) :
    Nat.card H < Nat.card G := by
  have h_dvd : Nat.card H ∣ Nat.card G :=
    ⟨H.index, by rw [mul_comm, H.index_mul_card]⟩
  have h_le : Nat.card H ≤ Nat.card G := Nat.le_of_dvd Nat.card_pos h_dvd
  have h_ne : Nat.card H ≠ Nat.card G := fun heq =>
    hH.ne (Subgroup.eq_top_of_card_eq _ heq)
  exact Nat.lt_of_le_of_ne h_le h_ne

/-- In a finite cyclic group, the subgroup cut out by `x ^ |K| = 1` is exactly `K`. -/
private lemma mem_of_pow_card_eq_one_of_isCyclic_subgroup
    {A : Type*} [Group A] [Finite A] (hA_cyclic : IsCyclic A)
    (K : Subgroup A) {x : A} (hx : x ^ Nat.card K = 1) :
    x ∈ K := by
  classical
  have : IsCyclic A := hA_cyclic
  have : Fintype A := Fintype.ofFinite A
  let : CommGroup A := IsCyclic.commGroup
  let P : Subgroup A := {
    carrier := {x | x ^ Nat.card K = 1}
    one_mem' := by simp
    mul_mem' := by
      intro x y hx hy
      change (x * y) ^ Nat.card K = 1
      rw [mul_pow, hx, hy, mul_one]
    inv_mem' := by
      intro x hx
      change x⁻¹ ^ Nat.card K = 1
      rw [inv_pow, hx, inv_one]
  }
  have hK_le_P : K ≤ P := by
    intro y hy
    dsimp [P]
    have h_sub :
        (⟨y, hy⟩ : K) ^ Nat.card K = 1 := pow_card_eq_one'
    exact congrArg Subtype.val h_sub
  have hP_card_le : Nat.card P ≤ Nat.card K := by
    have : Fintype P := Fintype.ofFinite P
    have hroot :=
      (IsCyclic.card_pow_eq_one_le (α := A) (n := Nat.card K) Nat.card_pos)
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    dsimp [P]
    rw [Fintype.card_subtype]
    simpa [Nat.card_eq_fintype_card] using hroot
  have hKP : K = P := Subgroup.eq_of_le_of_card_ge hK_le_P hP_card_le
  rw [hKP]
  exact hx

/-- In a finite cyclic `2`-group, every proper subgroup lies in any subgroup of index `2`. -/
private lemma le_index_two_subgroup_of_lt_top_of_cyclic_two_group
    {A : Type*} [Group A] [Finite A] (hA_two : IsPGroup 2 A) (hA_cyclic : IsCyclic A)
    {Z H : Subgroup A} (hZ_idx : Z.index = 2) (hH_lt_top : H < ⊤) :
    H ≤ Z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨kA, hA_card⟩ := (IsPGroup.iff_card (p := 2) (G := A)).mp hA_two
  obtain ⟨kH, hH_card⟩ := (IsPGroup.iff_card (p := 2) (G := H)).mp
    (hA_two.to_subgroup H)
  obtain ⟨kZ, hZ_card⟩ := (IsPGroup.iff_card (p := 2) (G := Z)).mp
    (hA_two.to_subgroup Z)
  have hZ_mul : 2 * Nat.card Z = Nat.card A := by
    simpa [hZ_idx] using Z.index_mul_card
  have hkA_eq : kA = kZ + 1 := by
    have hpow : 2 ^ (kZ + 1) = 2 ^ kA := by
      calc
        2 ^ (kZ + 1) = 2 * 2 ^ kZ := by
          rw [pow_succ']
        _ = 2 * Nat.card Z := by rw [hZ_card]
        _ = Nat.card A := hZ_mul
        _ = 2 ^ kA := hA_card
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) hpow.symm
  have hH_card_lt : Nat.card H < Nat.card A :=
    subgroup_card_lt_of_lt_top hH_lt_top
  have hkH_lt_A : kH < kA := by
    have hpow : 2 ^ kH < 2 ^ kA := by
      rw [← hH_card, ← hA_card]
      exact hH_card_lt
    exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hpow
  have hkH_le_Z : kH ≤ kZ := by omega
  have hH_dvd_Z : Nat.card H ∣ Nat.card Z := by
    rw [hH_card, hZ_card]
    exact pow_dvd_pow 2 hkH_le_Z
  intro x hx
  have hx_order_dvd_H : orderOf x ∣ Nat.card H :=
    H.orderOf_dvd_natCard hx
  have hx_order_dvd_Z : orderOf x ∣ Nat.card Z :=
    dvd_trans hx_order_dvd_H hH_dvd_Z
  exact mem_of_pow_card_eq_one_of_isCyclic_subgroup hA_cyclic Z
    (orderOf_dvd_iff_pow_eq_one.mp hx_order_dvd_Z)

/-- If a central subgroup has index `2`, then the ambient group is abelian. -/
private lemma commutative_of_central_index_two_subgroup
    {A : Type*} [Group A] {D : Subgroup A}
    (hD_le_center : D ≤ Subgroup.center A) (hD_idx : D.index = 2) :
    ∀ x y : A, x * y = y * x := by
  intro x y
  by_cases hxD : x ∈ D
  · have hx_center : x ∈ Subgroup.center A := hD_le_center hxD
    exact (Subgroup.mem_center_iff.mp hx_center y).symm
  by_cases hyD : y ∈ D
  · have hy_center : y ∈ Subgroup.center A := hD_le_center hyD
    exact Subgroup.mem_center_iff.mp hy_center x
  have hxyD : x * y ∈ D := by
    rw [Subgroup.mul_mem_iff_of_index_two hD_idx]
    exact iff_of_false hxD hyD
  have hxy_center : x * y ∈ Subgroup.center A := hD_le_center hxyD
  have hcomm := Subgroup.mem_center_iff.mp hxy_center x
  exact mul_left_cancel (a := x) (by
    calc
      x * (x * y) = x * y * x := hcomm
      _ = x * (y * x) := by rw [mul_assoc])

/-- Restrict an automorphism of `G` to a characteristic subgroup. -/
private def characteristicRestrictMulEquiv
    {G : Type*} [Group G] {H : Subgroup G} (hH : H.Characteristic)
    (φ : G ≃* G) : H ≃* H where
  toFun x := ⟨φ x, by
    have hx : (x : G) ∈ H.comap φ.toMonoidHom := by
      rw [hH.fixed φ]
      exact x.2
    exact hx⟩
  invFun x := ⟨φ.symm x, by
    have hx : (x : G) ∈ H.comap φ.symm.toMonoidHom := by
      rw [hH.fixed φ.symm]
      exact x.2
    exact hx⟩
  left_inv x := by
    apply Subtype.ext
    exact φ.symm_apply_apply (x : G)
  right_inv x := by
    apply Subtype.ext
    exact φ.apply_symm_apply (x : G)
  map_mul' x y := by
    apply Subtype.ext
    exact φ.map_mul (x : G) (y : G)

/-- A characteristic subgroup of a characteristic subgroup is characteristic upstairs. -/
private lemma characteristic_map_subtype_of_characteristic
    {G : Type*} [Group G] {H : Subgroup G} {K : Subgroup H}
    (hH : H.Characteristic) (hK : K.Characteristic) :
    (K.map H.subtype).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro φ y hy
  rw [Subgroup.mem_map] at hy ⊢
  obtain ⟨x, hxL, rfl⟩ := hy
  rw [Subgroup.mem_map] at hxL
  obtain ⟨k, hkK, rfl⟩ := hxL
  let φH : H ≃* H := characteristicRestrictMulEquiv hH φ
  have hk_image : φH k ∈ K := by
    have hmem_map : φH k ∈ K.map φH.toMonoidHom :=
      Subgroup.mem_map_of_mem φH.toMonoidHom hkK
    exact (Subgroup.characteristic_iff_map_le.mp hK φH) hmem_map
  refine ⟨φH k, hk_image, ?_⟩
  rfl

/-- Elementary abelian structure is transported across a multiplicative equivalence. -/
lemma isElementaryAbelian_of_mulEquiv
    {p : ℕ} {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : IsElementaryAbelian p A) :
    IsElementaryAbelian p B := by
  constructor
  · intro x y
    obtain ⟨x', rfl⟩ := e.surjective x
    obtain ⟨y', rfl⟩ := e.surjective y
    simpa using congrArg e (h.1 x' y')
  · intro x
    obtain ⟨x', rfl⟩ := e.surjective x
    simpa using congrArg e (h.2 x')

/-- **Isaacs Lemma 6.15** (`p = 2`, second-step setup).

The lifted subgroup `E` from `T/T'` is noncyclic and has order `8`; moreover
`C ∩ E`, viewed as a subgroup of `E`, is cyclic of index `2`. -/
theorem exists_lift_order_eight_noncyclic_cyclic_index_two_of_center_index_four
    {T : Type*} [Group T] [Finite T] (hT_two : IsPGroup 2 T)
    (hT_card_ne : Nat.card T ≠ 8)
    (h_idx : (Subgroup.center T).index = 2 ^ 2)
    {C : Subgroup T} (hC_cyclic : IsCyclic C)
    (hC_lt_T : C < ⊤) (hZ_lt_C : Subgroup.center T < C) :
    ∃ E : Subgroup T, E.Characteristic ∧
      _root_.commutator T ≤ E ∧
      IsElementaryAbelian 2 (E.map (QuotientGroup.mk' (_root_.commutator T))) ∧
      Nat.card (E.map (QuotientGroup.mk' (_root_.commutator T))) = 4 ∧
      Nat.card E = 8 ∧
      ¬ IsCyclic E ∧
      IsCyclic (C.subgroupOf E) ∧
      (C.subgroupOf E).index = 2 := by
  obtain ⟨E, hE_char, hcomm_le_E, hE_image_elem, hE_image_card, hE_card⟩ :=
    exists_lift_quotient_commutator_order_eight_of_center_index_four
      hT_two h_idx hC_cyclic hC_lt_T hZ_lt_C
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC_idx : C.index = 2 :=
    index_eq_prime_of_center_lt_of_center_index_pow_two
      (p := 2) h_idx hZ_lt_C hC_lt_T
  have hE_not_cyclic : ¬ IsCyclic E :=
    not_isCyclic_of_quotient_commutator_image_four
      hE_image_elem hE_image_card
  have hE_ne_C : E ≠ C := by
    intro hEq
    apply hE_not_cyclic
    rw [hEq]
    exact hC_cyclic
  have hE_ne_top : E ≠ ⊤ := by
    intro hEq
    apply hT_card_ne
    simpa [hEq] using hE_card
  have hC_not_le_E : ¬ C ≤ E :=
    not_ge_of_ne_of_ne_top_of_index_two hC_idx hE_ne_C hE_ne_top
  have hE_not_le_C : ¬ E ≤ C := by
    intro hE_le_C
    have : IsCyclic C := hC_cyclic
    exact hE_not_cyclic (Subgroup.isCyclic_of_le hE_le_C)
  have hCE_idx : (C.subgroupOf E).index = 2 := by
    simpa [Subgroup.relIndex] using
      relIndex_eq_two_of_index_two_of_not_le hC_idx hE_not_le_C
  exact ⟨E, hE_char, hcomm_le_E, hE_image_elem, hE_image_card, hE_card,
    hE_not_cyclic, subgroupOf_isCyclic_of_isCyclic hC_cyclic, hCE_idx⟩

/-- **Isaacs Lemma 6.15** (`p = 2`, lifted subgroup is abelian).

In the second `p = 2` step, the lifted subgroup `E` is noncyclic of order `8`, `C ∩ E`
has index `2` in `E`, and the cyclic `2`-group maximality argument forces `C ∩ E ≤ Z(E)`.
Thus `E` is abelian, matching the corresponding sentence in Isaacs Lemma 6.15. -/
theorem exists_lift_order_eight_noncyclic_abelian_cyclic_index_two_of_center_index_four
    {T : Type*} [Group T] [Finite T] (hT_two : IsPGroup 2 T)
    (hT_card_ne : Nat.card T ≠ 8)
    (h_idx : (Subgroup.center T).index = 2 ^ 2)
    {C : Subgroup T} (hC_cyclic : IsCyclic C)
    (hC_lt_T : C < ⊤) (hZ_lt_C : Subgroup.center T < C) :
    ∃ E : Subgroup T, E.Characteristic ∧
      _root_.commutator T ≤ E ∧
      IsElementaryAbelian 2 (E.map (QuotientGroup.mk' (_root_.commutator T))) ∧
      Nat.card (E.map (QuotientGroup.mk' (_root_.commutator T))) = 4 ∧
      Nat.card E = 8 ∧
      ¬ IsCyclic E ∧
      (∀ x y : E, x * y = y * x) ∧
      IsCyclic (C.subgroupOf E) ∧
      (C.subgroupOf E).index = 2 := by
  obtain ⟨E, hE_char, hcomm_le_E, hE_image_elem, hE_image_card, hE_card,
    hE_not_cyclic, hCE_cyclic, hCE_idx⟩ :=
    exists_lift_order_eight_noncyclic_cyclic_index_two_of_center_index_four
      hT_two hT_card_ne h_idx hC_cyclic hC_lt_T hZ_lt_C
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC_idx : C.index = 2 :=
    index_eq_prime_of_center_lt_of_center_index_pow_two
      (p := 2) h_idx hZ_lt_C hC_lt_T
  have hE_ne_C : E ≠ C := by
    intro hEq
    apply hE_not_cyclic
    rw [hEq]
    exact hC_cyclic
  have hE_ne_top : E ≠ ⊤ := by
    intro hEq
    apply hT_card_ne
    simpa [hEq] using hE_card
  have hC_not_le_E : ¬ C ≤ E :=
    not_ge_of_ne_of_ne_top_of_index_two hC_idx hE_ne_C hE_ne_top
  have hZ_rel : (Subgroup.center T).relIndex C = 2 := by
    have hmul :
        (Subgroup.center T).relIndex C * C.index = (Subgroup.center T).index := by
      rw [Subgroup.relIndex_mul_index hZ_lt_C.le]
    rw [hC_idx, h_idx] at hmul
    norm_num at hmul
    omega
  have hZC_idx : ((Subgroup.center T).subgroupOf C).index = 2 := by
    simpa [Subgroup.relIndex] using hZ_rel
  have hEC_lt_top : E.subgroupOf C < ⊤ := by
    refine lt_of_le_of_ne le_top ?_
    intro htop
    apply hC_not_le_E
    intro x hxC
    have hx_sub : (⟨x, hxC⟩ : C) ∈ E.subgroupOf C := by
      rw [htop]
      trivial
    rwa [Subgroup.mem_subgroupOf] at hx_sub
  have hEC_le_ZC : E.subgroupOf C ≤ (Subgroup.center T).subgroupOf C :=
    le_index_two_subgroup_of_lt_top_of_cyclic_two_group
      (A := C) (hT_two.to_subgroup C) hC_cyclic hZC_idx hEC_lt_top
  have hCE_le_centerE : C.subgroupOf E ≤ Subgroup.center E := by
    intro e he
    rw [Subgroup.mem_center_iff]
    intro y
    have heC : ((e : E) : T) ∈ C := by
      simpa [Subgroup.mem_subgroupOf] using he
    let eC : C := ⟨((e : E) : T), heC⟩
    have heC_in_EC : eC ∈ E.subgroupOf C := by
      rw [Subgroup.mem_subgroupOf]
      exact e.2
    have heC_in_ZC : eC ∈ (Subgroup.center T).subgroupOf C :=
      hEC_le_ZC heC_in_EC
    have he_center_T : ((e : E) : T) ∈ Subgroup.center T := by
      simpa [Subgroup.mem_subgroupOf, eC] using heC_in_ZC
    exact Subtype.ext (Subgroup.mem_center_iff.mp he_center_T ((y : E) : T))
  have hE_ab : ∀ x y : E, x * y = y * x :=
    commutative_of_central_index_two_subgroup hCE_le_centerE hCE_idx
  exact ⟨E, hE_char, hcomm_le_E, hE_image_elem, hE_image_card, hE_card,
    hE_not_cyclic, hE_ab, hCE_cyclic, hCE_idx⟩

/-- **Isaacs Lemma 6.15** (`p = 2` branch).

Let `T` be a finite `2`-group with `|T : Z(T)| = 4`, `|T| ≠ 8`, and a cyclic subgroup
`C` with `Z(T) < C < T`. Then `T` contains a characteristic elementary abelian subgroup
of order `4`. -/
theorem exists_characteristic_isElementaryAbelian_four_of_center_index_four
    {T : Type*} [Group T] [Finite T] (hT_two : IsPGroup 2 T)
    (hT_card_ne : Nat.card T ≠ 8)
    (h_idx : (Subgroup.center T).index = 2 ^ 2)
    {C : Subgroup T} (hC_cyclic : IsCyclic C)
    (hC_lt_T : C < ⊤) (hZ_lt_C : Subgroup.center T < C) :
    ∃ K : Subgroup T, K.Characteristic ∧
      IsElementaryAbelian 2 K ∧ Nat.card K = 4 := by
  obtain ⟨E, hE_char, _hcomm_le_E, _hE_image_elem, _hE_image_card, _hE_card,
    hE_not_cyclic, hE_ab, hCE_cyclic, hCE_idx⟩ :=
    exists_lift_order_eight_noncyclic_abelian_cyclic_index_two_of_center_index_four
      hT_two hT_card_ne h_idx hC_cyclic hC_lt_T hZ_lt_C
  obtain ⟨K, hK_char, hK_elem, hK_card⟩ :=
    exists_characteristic_isElementaryAbelian_four_of_noncyclic_abelian_two_group
      (A := E) hE_ab (hT_two.to_subgroup E)
      (D := C.subgroupOf E) hCE_cyclic hCE_idx hE_not_cyclic
  let L : Subgroup T := K.map E.subtype
  refine ⟨L, ?_, ?_, ?_⟩
  · dsimp [L]
    exact characteristic_map_subtype_of_characteristic hE_char hK_char
  · dsimp [L]
    exact isElementaryAbelian_of_mulEquiv
      (Subgroup.equivMapOfInjective K E.subtype E.subtype_injective) hK_elem
  · dsimp [L]
    rw [Subgroup.card_subtype, hK_card]

end OddOrder.Isaacs.Ch06


