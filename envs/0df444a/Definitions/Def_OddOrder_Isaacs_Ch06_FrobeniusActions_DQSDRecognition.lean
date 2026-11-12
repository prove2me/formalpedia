-- Prove2me | Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_DQSDRecognition
-- name    : OddOrder_Isaacs_Ch06_FrobeniusActions_DQSDRecognition
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:40:11.959946+00:00
-- url     : https://prove2.me/theorems/b7628996-5856-4264-9930-4f73935cbea1
-- title:
--   Isaacs Lemmas 6.13/6.14: dihedral, quaternion, semidihedral recognition
-- statement:
--   Formalizes Lemma 6.13/6.14 of Isaacs, *Finite Group Theory*, on recognizing dihedral, quaternion and semidihedral groups, together with the first enlargement step of Thm 6.12 (pp. 192–193).
--
--   Main definitions: `dihedralIsoOfInverting` (dihedral recognition in the inverting case) and the semidihedral recognition helpers `semiDihedralIsoOfTwistNormalized` (normalized twist case), `semiDihedralIsoOfTwistInvolution` and `semiDihedralIsoOfTwistSquareInvolution`.
--
--   The bundle also proves 17 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch06_FrobeniusActions/DQSDRecognition.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch06_FrobeniusActions/DQSDRecognition.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_QuaternionRecognition
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_FrobeniusGroup
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_SelfCentralizingEnlargement

namespace OddOrder.Isaacs.Ch06

open OddOrder.GroupTheory

/-- **Dihedral recognition helper** (used in Lem 6.13 inverting case): given a finite group `P`
with `c, a ∈ P` such that `⟨c⟩` has index `2`, `a ∉ ⟨c⟩`, `a² = 1`, and `a c a⁻¹ = c⁻¹`, then
`P ≃* DihedralGroup (orderOf c)`. -/
private noncomputable def dihedralIsoOfInverting
    {P : Type*} [Group P] [Finite P]
    (c a : P) (h_idx : (Subgroup.zpowers c).index = 2)
    (h_a_notmem : a ∉ Subgroup.zpowers c)
    (h_a_sq : a ^ 2 = 1) (h_conj : a * c * a⁻¹ = c⁻¹) :
    P ≃* DihedralGroup (orderOf c) := by
  classical
  set N := orderOf c with hN_def
  haveI : Fintype P := Fintype.ofFinite P
  -- N > 0 since `P` is finite.
  have hc_fin : IsOfFinOrder c := isOfFinOrder_of_finite c
  have hN_pos : 0 < N := hc_fin.orderOf_pos
  haveI : NeZero N := ⟨hN_pos.ne'⟩
  -- Conjugation by `a` inverts every power of `c`.
  have h_conj_zpow : ∀ k : ℤ, a * c ^ k * a⁻¹ = c ^ (-k) := fun k => by
    have step1 : a * c ^ k * a⁻¹ = (a * c * a⁻¹) ^ k := by
      have : Function.Bijective ((MulAut.conj a : P ≃* P) : P → P) :=
        (MulAut.conj a : P ≃* P).bijective
      simp
    rw [step1, h_conj, inv_zpow, ← zpow_neg]
  -- Cardinality computation: |P| = 2 * N.
  have hcard_P : Nat.card P = 2 * N := by
    have h := (Subgroup.zpowers c).index_mul_card
    rw [h_idx, Nat.card_zpowers] at h
    omega
  -- Forward map `DihedralGroup N → P`.
  let fwd : DihedralGroup N → P
    | DihedralGroup.r i => c ^ i.val
    | DihedralGroup.sr i => a * c ^ i.val
  -- Helper: `c ^ (i.val + j.val) = c ^ ((i + j).val)` for `i j : ZMod N`.
  have hc_addval : ∀ i j : ZMod N, c ^ ((i + j).val) = c ^ i.val * c ^ j.val := by
    intro i j
    rw [← pow_add]
    -- `c ^ k = c ^ (k % N)` via `pow_eq_pow_iff_modEq` (since `N = orderOf c`).
    rw [pow_eq_pow_iff_modEq, Nat.ModEq, ← hN_def]
    -- `(i + j).val % N = (i.val + j.val) % N` from `ZMod.val_add`.
    rw [ZMod.val_add, Nat.mod_mod]
  have hc_subval : ∀ i j : ZMod N, c ^ ((j - i).val) = c ^ j.val * (c ^ i.val)⁻¹ := by
    intro i j
    have h := hc_addval (j - i) i
    rw [sub_add_cancel] at h
    -- h : c ^ j.val = c ^ (j - i).val * c ^ i.val
    exact eq_mul_inv_iff_mul_eq.mpr h.symm
  -- `a⁻¹ = a` from `a² = 1`.
  have ha_inv : a⁻¹ = a := by
    have h1 : a * a = 1 := by rw [← sq, h_a_sq]
    exact (eq_inv_of_mul_eq_one_right h1).symm
  -- Commutation: `c ^ k * a = a * c ^ (-k)` for `k : ℤ`.
  have h_zpow_a : ∀ k : ℤ, c ^ k * a = a * c ^ (-k) := fun k => by
    have h := h_conj_zpow (-k)
    rw [neg_neg] at h
    -- h : a * c ^ (-k) * a⁻¹ = c ^ k
    -- Goal: c ^ k * a = a * c ^ (-k)
    rw [show (c ^ k : P) = a * c ^ (-k) * a⁻¹ from h.symm,
        mul_assoc (a * c ^ (-k)), inv_mul_cancel, mul_one]
  -- Bridge: `c ^ ((j - i).val) = c ^ j.val * (c ^ i.val)⁻¹` (already proved as `hc_subval`).
  -- For `h_sr_r`: `c ^ i.val * a * c ^ j.val = a * c ^ (j - i).val`. Use the conjugation
  -- relation, then bridge via `pow_eq_pow_iff_modEq` and ZMod-arithmetic.
  have h_sr_r : ∀ i j : ZMod N, c ^ i.val * a * c ^ j.val = a * c ^ (j - i).val := by
    intro i j
    -- LHS = c^i.val * (a * c^j.val) = c^i.val * a * c^j.val (associativity)
    -- Use h_zpow_a (i.val : ℤ): c^(i.val : ℤ) * a = a * c^(-(i.val : ℤ))
    -- Then combine c^(-(i.val : ℤ)) * c^(j.val : ℤ) = c^(j.val - i.val : ℤ).
    -- Finally show c^(j.val - i.val : ℤ) = c^((j - i).val : ℕ) via mod N.
    have step1 : c ^ i.val * a = a * c ^ (-(i.val : ℤ)) := by
      have := h_zpow_a (i.val : ℤ)
      rw [zpow_natCast] at this; exact this
    rw [step1, mul_assoc, ← zpow_natCast c j.val, ← zpow_add]
    -- Goal: a * c ^ (-(i.val : ℤ) + (j.val : ℤ)) = a * c ^ (j - i).val
    congr 1
    rw [show (c ^ (j - i).val : P) = c ^ ((j - i).val : ℤ) from (zpow_natCast c _).symm,
        zpow_eq_zpow_iff_modEq, ← hN_def]
    -- Bridge `(-i.val + j.val : ℤ) ≡ ((j - i).val : ℤ) [ZMOD (N : ℤ)]` via ZMod equality.
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    ring
  -- Injectivity: `fwd` does not collapse `c^i.val` and `a * c^j.val` (since `a ∉ ⟨c⟩`),
  -- and is injective on each branch by `orderOf c = N`.
  have hfwd_inj : Function.Injective fwd := by
    rintro (i | i) (j | j) h <;> simp only [fwd] at h
    · -- `c^i.val = c^j.val` ⇒ `i = j` via `pow_eq_pow_iff_modEq`
      congr 1
      have hmod : i.val ≡ j.val [MOD N] := (pow_eq_pow_iff_modEq).mp h
      unfold Nat.ModEq at hmod
      rw [Nat.mod_eq_of_lt (ZMod.val_lt i), Nat.mod_eq_of_lt (ZMod.val_lt j)] at hmod
      exact ZMod.val_injective N hmod
    · -- `c^i.val = a * c^j.val` ⇒ `a ∈ ⟨c⟩`, contradiction
      exfalso
      apply h_a_notmem
      have : a = c ^ i.val * (c ^ j.val)⁻¹ := by
        rw [h]; group
      rw [this]
      exact Subgroup.mul_mem _
        (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) _)
        (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) _))
    · -- `a * c^i.val = c^j.val` ⇒ `a ∈ ⟨c⟩`, contradiction
      exfalso
      apply h_a_notmem
      have : a = c ^ j.val * (c ^ i.val)⁻¹ := by
        rw [← h]; group
      rw [this]
      exact Subgroup.mul_mem _
        (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) _)
        (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) _))
    · -- `a * c^i.val = a * c^j.val` ⇒ `i = j`
      congr 1
      have heq : c ^ i.val = c ^ j.val := mul_left_cancel h
      have hmod : i.val ≡ j.val [MOD N] := (pow_eq_pow_iff_modEq).mp heq
      unfold Nat.ModEq at hmod
      rw [Nat.mod_eq_of_lt (ZMod.val_lt i), Nat.mod_eq_of_lt (ZMod.val_lt j)] at hmod
      exact ZMod.val_injective N hmod
  -- Cardinality equality.
  have hcard_eq : Nat.card (DihedralGroup N) = Nat.card P := by
    rw [DihedralGroup.nat_card, hcard_P]
  -- Build the Equiv via bijectivity.
  have hbij : Function.Bijective fwd := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hfwd_inj, ?_⟩
    rw [DihedralGroup.card]
    rw [← Nat.card_eq_fintype_card, hcard_P]
  -- Build map_mul (4 cases).
  have hfwd_mul : ∀ x y : DihedralGroup N, fwd (x * y) = fwd x * fwd y := by
    rintro (i | i) (j | j) <;> simp only [fwd]
    · -- r i * r j = r (i+j)
      change c ^ (i + j).val = c ^ i.val * c ^ j.val
      exact hc_addval i j
    · -- r i * sr j = sr (j - i)
      change a * c ^ (j - i).val = c ^ i.val * (a * c ^ j.val)
      rw [← mul_assoc]
      exact (h_sr_r i j).symm
    · -- sr i * r j = sr (i + j)
      change a * c ^ (i + j).val = a * c ^ i.val * c ^ j.val
      rw [mul_assoc, ← hc_addval]
    · -- sr i * sr j = r (j - i)
      change c ^ (j - i).val = a * c ^ i.val * (a * c ^ j.val)
      rw [mul_assoc, ← mul_assoc (c ^ i.val), h_sr_r, ← mul_assoc]
      rw [show a * a = 1 from by rw [← sq, h_a_sq], one_mul]
  -- Assemble.
  let setEquiv : DihedralGroup N ≃ P := Equiv.ofBijective fwd hbij
  exact (MulEquiv.mk' setEquiv hfwd_mul).symm

theorem dihedralOrQuaternion_of_invertingConjugation
    {P : Type*} [Group P] [Finite P] (_hP : IsPGroup 2 P)
    (c a : P) (h_idx : (Subgroup.zpowers c).index = 2)
    (h_a_notmem : a ∉ Subgroup.zpowers c)
    (h_conj : a * c * a⁻¹ = c⁻¹) :
    Nonempty (P ≃* DihedralGroup (orderOf c)) ∨
      Nonempty (P ≃* QuaternionGroup (orderOf c / 2)) := by
  classical
  by_cases h_a_sq_one : a ^ 2 = 1
  · left
    exact ⟨dihedralIsoOfInverting c a h_idx h_a_notmem h_a_sq_one h_conj⟩
  · right
    have h_a_sq_mem : a ^ 2 ∈ Subgroup.zpowers c :=
      Subgroup.sq_mem_of_index_two h_idx a
    have h_conj_zpow : ∀ k : ℤ, a * c ^ k * a⁻¹ = c ^ (-k) := fun k => by
      have step1 : a * c ^ k * a⁻¹ = (a * c * a⁻¹) ^ k := by
        have : Function.Bijective ((MulAut.conj a : P ≃* P) : P → P) :=
          (MulAut.conj a : P ≃* P).bijective
        simp
      rw [step1, h_conj, inv_zpow, ← zpow_neg]
    have h_a_sq_sq : (a ^ 2) ^ 2 = 1 := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h_a_sq_mem
      have h_fixed : a * (c ^ k) * a⁻¹ = c ^ k := by
        rw [hk]
        group
      have h_inv : c ^ k = c ^ (-k) := by
        rw [← h_fixed]
        exact h_conj_zpow k
      calc (a ^ 2) ^ 2 = c ^ k * c ^ k := by rw [← hk, pow_two]
        _ = c ^ k * c ^ (-k) := congrArg (fun t => c ^ k * t) h_inv
        _ = 1 := by rw [← zpow_add, add_neg_cancel, zpow_zero]
    obtain ⟨h_a_sq_half, h_order, h_half_pos⟩ :=
      eq_pow_half_orderOf_of_mem_zpowers_sq_eq_one c (a ^ 2)
        h_a_sq_mem h_a_sq_sq h_a_sq_one
    exact ⟨quaternionIsoOfInverting c a (orderOf c / 2)
      h_half_pos h_order h_idx h_a_notmem h_a_sq_half h_conj⟩

/-- **Semidihedral recognition helper** (normalised twist case): given a finite group `P`
with `c, a ∈ P` such that `⟨c⟩` has index `2`, `a ∉ ⟨c⟩`, `a² = 1`,
`orderOf c = 2^k`, and conjugation by `a` sends `c` to the semidihedral twist
`c ^ (SemiDihedralGroup.twist k).val`, then `P ≃* SemiDihedralGroup k`. -/
private noncomputable def semiDihedralIsoOfTwistNormalized
    {P : Type*} [Group P] [Finite P]
    (c a : P) (k : ℕ) (h_order : orderOf c = 2 ^ k)
    (h_idx : (Subgroup.zpowers c).index = 2)
    (h_a_notmem : a ∉ Subgroup.zpowers c)
    (h_a_sq : a ^ 2 = 1)
    (h_conj : a * c * a⁻¹ = c ^ (SemiDihedralGroup.twist k).val) :
    P ≃* SemiDihedralGroup k := by
  classical
  haveI : Fintype P := Fintype.ofFinite P
  have hN_pos : 0 < 2 ^ k := Nat.two_pow_pos k
  haveI : NeZero (2 ^ k) := ⟨hN_pos.ne'⟩
  set r : ZMod (2 ^ k) := SemiDihedralGroup.twist k with hr_def
  have hcard_P : Nat.card P = 2 * 2 ^ k := by
    have h := (Subgroup.zpowers c).index_mul_card
    rw [h_idx, Nat.card_zpowers, h_order] at h
    omega
  let fwd : SemiDihedralGroup k → P
    | SemiDihedralGroup.c i => c ^ i.val
    | SemiDihedralGroup.ca i => a * c ^ i.val
  have hc_addval : ∀ i j : ZMod (2 ^ k), c ^ ((i + j).val) = c ^ i.val * c ^ j.val := by
    intro i j
    rw [← pow_add, pow_eq_pow_iff_modEq, Nat.ModEq, h_order, ZMod.val_add, Nat.mod_mod]
  have h_conj_pow :
      ∀ i : ZMod (2 ^ k), a * c ^ i.val * a⁻¹ = c ^ (r * i).val := by
    intro i
    have h_map : a * c ^ i.val * a⁻¹ = (a * c * a⁻¹) ^ i.val := by
      simp
    rw [h_map, h_conj, ← pow_mul]
    rw [pow_eq_pow_iff_modEq, Nat.ModEq, h_order]
    rw [ZMod.val_mul, Nat.mod_mod]
  have ha_inv : a⁻¹ = a := by
    have h1 : a * a = 1 := by rw [← sq, h_a_sq]
    exact (eq_inv_of_mul_eq_one_right h1).symm
  have h_pow_a : ∀ i : ZMod (2 ^ k), c ^ i.val * a = a * c ^ (r * i).val := by
    intro i
    have h := h_conj_pow i
    rw [ha_inv] at h
    calc c ^ i.val * a
        = (a * a) * c ^ i.val * a := by rw [show a * a = 1 from by rw [← sq, h_a_sq], one_mul]
      _ = a * (a * c ^ i.val * a) := by group
      _ = a * c ^ (r * i).val := by rw [h]
  have hfwd_inj : Function.Injective fwd := by
    rintro (i | i) (j | j) h <;> simp only [fwd] at h
    · congr 1
      have hmod : i.val ≡ j.val [MOD 2 ^ k] := by
        have hmod0 : i.val ≡ j.val [MOD orderOf c] := (pow_eq_pow_iff_modEq).mp h
        rwa [h_order] at hmod0
      unfold Nat.ModEq at hmod
      rw [Nat.mod_eq_of_lt (ZMod.val_lt i), Nat.mod_eq_of_lt (ZMod.val_lt j)] at hmod
      exact ZMod.val_injective (2 ^ k) hmod
    · exfalso; apply h_a_notmem
      have : a = c ^ i.val * (c ^ j.val)⁻¹ := by rw [h]; group
      rw [this]
      exact Subgroup.mul_mem _
        (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) _)
        (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) _))
    · exfalso; apply h_a_notmem
      have : a = c ^ j.val * (c ^ i.val)⁻¹ := by rw [← h]; group
      rw [this]
      exact Subgroup.mul_mem _
        (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) _)
        (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) _))
    · congr 1
      have heq : c ^ i.val = c ^ j.val := mul_left_cancel h
      have hmod : i.val ≡ j.val [MOD 2 ^ k] := by
        have hmod0 : i.val ≡ j.val [MOD orderOf c] := (pow_eq_pow_iff_modEq).mp heq
        rwa [h_order] at hmod0
      unfold Nat.ModEq at hmod
      rw [Nat.mod_eq_of_lt (ZMod.val_lt i), Nat.mod_eq_of_lt (ZMod.val_lt j)] at hmod
      exact ZMod.val_injective (2 ^ k) hmod
  have hbij : Function.Bijective fwd := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hfwd_inj, ?_⟩
    rw [SemiDihedralGroup.card, ← Nat.card_eq_fintype_card, hcard_P]
    rw [pow_succ, mul_comm]
  have hfwd_mul : ∀ x y : SemiDihedralGroup k, fwd (x * y) = fwd x * fwd y := by
    rintro (i | i) (j | j) <;> simp only [fwd, SemiDihedralGroup.c_mul_c,
      SemiDihedralGroup.c_mul_ca, SemiDihedralGroup.ca_mul_c, SemiDihedralGroup.ca_mul_ca,
      ← hr_def]
    · exact hc_addval i j
    · rw [← mul_assoc, h_pow_a, mul_assoc, ← hc_addval]
    · rw [mul_assoc, ← hc_addval]
    · calc c ^ (r * i + j).val
          = c ^ (r * i).val * c ^ j.val := hc_addval (r * i) j
        _ = (a * a) * c ^ (r * i).val * c ^ j.val := by
          rw [show a * a = 1 from by rw [← sq, h_a_sq], one_mul]
        _ = a * (a * c ^ (r * i).val) * c ^ j.val := by group
        _ = a * (c ^ i.val * a) * c ^ j.val := by rw [h_pow_a]
        _ = a * c ^ i.val * (a * c ^ j.val) := by group
  let setEquiv : SemiDihedralGroup k ≃ P := Equiv.ofBijective fwd hbij
  exact (MulEquiv.mk' setEquiv hfwd_mul).symm

private lemma pow_twist_eq_pow_half_mul_inv
    {P : Type*} [Group P] [Finite P] (c : P) {k : ℕ}
    (hk : 2 ≤ k) (h_order : orderOf c = 2 ^ k) :
    c ^ (SemiDihedralGroup.twist k).val = c ^ (2 ^ (k - 1)) * c⁻¹ := by
  rw [← zpow_natCast]
  have hrhs : c ^ (2 ^ (k - 1)) * c⁻¹ =
      c ^ (((2 : ℕ) ^ (k - 1) : ℤ) - 1) := by
    simpa [div_eq_mul_inv] using (zpow_natCast_sub_one c (2 ^ (k - 1))).symm
  rw [hrhs, zpow_eq_zpow_iff_modEq, h_order]
  rw [← ZMod.intCast_eq_intCast_iff]
  push_cast
  rw [ZMod.natCast_zmod_val]
  rcases k with _ | _ | n
  · omega
  · omega
  · simp [SemiDihedralGroup.twist]

private lemma twist_conj_zmod_pow
    {P : Type*} [Group P] [Finite P]
    (c a z : P) {k : ℕ} (hk : 2 ≤ k) (h_order : orderOf c = 2 ^ k)
    (h_z_pow : z = c ^ (2 ^ (k - 1)))
    (h_conj : a * c * a⁻¹ = z * c⁻¹) :
    ∀ i : ZMod (2 ^ k),
      a * c ^ i.val * a⁻¹ = c ^ (SemiDihedralGroup.twist k * i).val := by
  intro i
  have h_conj_twist : a * c * a⁻¹ = c ^ (SemiDihedralGroup.twist k).val := by
    rw [h_conj, h_z_pow, ← pow_twist_eq_pow_half_mul_inv c hk h_order]
  have h_map : a * c ^ i.val * a⁻¹ = (a * c * a⁻¹) ^ i.val := by
    simp
  rw [h_map, h_conj_twist, ← pow_mul]
  rw [pow_eq_pow_iff_modEq, Nat.ModEq, h_order]
  rw [ZMod.val_mul, Nat.mod_mod]

private lemma two_mul_eq_zero_of_twist_fixed
    {k : ℕ} (hk : 3 ≤ k) {i : ZMod (2 ^ k)}
    (hfix : SemiDihedralGroup.twist k * i = i) :
    (2 : ZMod (2 ^ k)) * i = 0 := by
  rcases k with _ | _ | _ | n
  · omega
  · omega
  · omega
  · change (2 : ZMod (2 ^ (n + 3))) * i = 0
    change ((2 ^ (n + 2) : ZMod (2 ^ (n + 3))) - 1) * i = i at hfix
    have hzero : (((2 ^ (n + 2) : ZMod (2 ^ (n + 3))) - 2) * i = 0) := by
      have hcalc : (((2 ^ (n + 2) : ZMod (2 ^ (n + 3))) - 2) * i) =
          (((2 ^ (n + 2) : ZMod (2 ^ (n + 3))) - 1) * i - i) := by
        ring
      rw [hcalc, hfix]
      ring
    have hfactor :
        ((2 ^ (n + 2) : ZMod (2 ^ (n + 3))) - 2) =
          (2 : ZMod (2 ^ (n + 3))) *
            ((2 ^ (n + 1) - 1 : ℕ) : ZMod (2 ^ (n + 3))) := by
      rw [Nat.cast_sub (by exact Nat.one_le_two_pow)]
      push_cast
      rw [pow_succ']
      ring
    rw [hfactor] at hzero
    have hodd : Odd (2 ^ (n + 1) - 1) := by
      have h_even : Even (2 ^ (n + 1)) :=
        even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))
      exact Nat.Even.sub_odd Nat.one_le_two_pow h_even odd_one
    have hcop : Nat.Coprime (2 ^ (n + 1) - 1) (2 ^ (n + 3)) := by
      rw [Nat.coprime_pow_right_iff (by omega), Nat.coprime_two_right]
      exact hodd
    let u := ZMod.unitOfCoprime (2 ^ (n + 1) - 1) hcop
    have hu : (u : ZMod (2 ^ (n + 3))) =
        ((2 ^ (n + 1) - 1 : ℕ) : ZMod (2 ^ (n + 3))) :=
      ZMod.coe_unitOfCoprime _ _
    have hzero' : (u : ZMod (2 ^ (n + 3))) * ((2 : ZMod (2 ^ (n + 3))) * i) = 0 := by
      calc (u : ZMod (2 ^ (n + 3))) * ((2 : ZMod (2 ^ (n + 3))) * i)
          = ((2 : ZMod (2 ^ (n + 3))) *
              ((2 ^ (n + 1) - 1 : ℕ) : ZMod (2 ^ (n + 3)))) * i := by
            rw [hu]
            ring
        _ = 0 := hzero
    exact (Units.mul_right_eq_zero u).mp hzero'

private lemma sq_eq_one_of_mem_zpowers_fixed_by_twist
    {P : Type*} [Group P] [Finite P]
    (c a z y : P) {k : ℕ} (hk_three : 3 ≤ k)
    (h_order : orderOf c = 2 ^ k)
    (h_z_pow : z = c ^ (2 ^ (k - 1)))
    (h_conj : a * c * a⁻¹ = z * c⁻¹)
    (hy_mem : y ∈ Subgroup.zpowers c)
    (hy_fixed : a * y * a⁻¹ = y) :
    y ^ 2 = 1 := by
  classical
  have hk_two : 2 ≤ k := by omega
  have hy_range : y ∈ (Finset.range (orderOf c)).image (fun n : ℕ => c ^ n) :=
    (mem_zpowers_iff_mem_range_orderOf (x := c) (y := y)).mp hy_mem
  rcases Finset.mem_image.mp hy_range with ⟨m, hm_range, hm_eq⟩
  have hm_lt : m < 2 ^ k := by
    have := Finset.mem_range.mp hm_range
    rwa [h_order] at this
  let i : ZMod (2 ^ k) := m
  have hi_val : i.val = m := by
    rw [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt hm_lt
  have hfix_pow : c ^ (SemiDihedralGroup.twist k * i).val = c ^ i.val := by
    calc c ^ (SemiDihedralGroup.twist k * i).val
        = a * c ^ i.val * a⁻¹ :=
          (twist_conj_zmod_pow c a z hk_two h_order h_z_pow h_conj i).symm
      _ = a * c ^ m * a⁻¹ := by rw [hi_val]
      _ = a * y * a⁻¹ := by rw [hm_eq]
      _ = y := hy_fixed
      _ = c ^ m := hm_eq.symm
      _ = c ^ i.val := by rw [hi_val]
  have hfix : SemiDihedralGroup.twist k * i = i := by
    have hmod : (SemiDihedralGroup.twist k * i).val ≡ i.val [MOD 2 ^ k] := by
      have hmod0 : (SemiDihedralGroup.twist k * i).val ≡ i.val [MOD orderOf c] :=
        (pow_eq_pow_iff_modEq).mp hfix_pow
      rwa [h_order] at hmod0
    unfold Nat.ModEq at hmod
    rw [Nat.mod_eq_of_lt (ZMod.val_lt _), Nat.mod_eq_of_lt (ZMod.val_lt _)] at hmod
    exact ZMod.val_injective (2 ^ k) hmod
  have htwo : (2 : ZMod (2 ^ k)) * i = 0 :=
    two_mul_eq_zero_of_twist_fixed hk_three hfix
  have hii : i + i = 0 := by
    simpa [two_mul] using htwo
  have hc_addval : c ^ (i + i).val = c ^ i.val * c ^ i.val := by
    rw [← pow_add, pow_eq_pow_iff_modEq, Nat.ModEq, h_order, ZMod.val_add, Nat.mod_mod]
  calc y ^ 2
      = c ^ i.val * c ^ i.val := by rw [← hm_eq, hi_val, pow_two]
    _ = c ^ (i + i).val := hc_addval.symm
    _ = 1 := by rw [hii, ZMod.val_zero, pow_zero]

lemma zpowers_involution_eq_pow_pred_of_order_two_pow
    {P : Type*} [Group P] [Finite P] (c z : P) {k : ℕ}
    (hk_pos : 0 < k) (h_order : orderOf c = 2 ^ k)
    (h_z_mem : z ∈ Subgroup.zpowers c) (h_z_sq : z ^ 2 = 1) (h_z_ne : z ≠ 1) :
    z = c ^ (2 ^ (k - 1)) := by
  obtain ⟨h_z_half, _h_order_even, _h_half_pos⟩ :=
    eq_pow_half_orderOf_of_mem_zpowers_sq_eq_one c z h_z_mem h_z_sq h_z_ne
  have hhalf : 2 ^ k / 2 = 2 ^ (k - 1) := by
    rcases k with _ | k
    · omega
    · simp [pow_succ]
  rw [h_z_half, h_order, hhalf]

/-- In a finite cyclic `2`-group of order larger than `2`, the nontrivial involution is a
square.

This is the cyclic-quotient square-root step in Isaacs Thm 6.12: if the cyclic quotient
`P/C` has order larger than `2`, then its unique involution coset is a square. -/
theorem exists_sq_eq_of_isCyclic_two_group_involution_of_card_ne_two
    {Q : Type*} [Group Q] [Finite Q] (hQ : IsPGroup 2 Q) [IsCyclic Q]
    {x : Q} (hx_ne : x ≠ 1) (hx_sq : x ^ 2 = 1) (hcard_ne_two : Nat.card Q ≠ 2) :
    ∃ y : Q, y ^ 2 = x := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg_gen⟩ := IsCyclic.exists_generator (α := Q)
  obtain ⟨k, hcard⟩ := (IsPGroup.iff_card (p := 2) (G := Q)).mp hQ
  have hcard_ne_one : Nat.card Q ≠ 1 := by
    intro hcard_one
    have : Subsingleton Q := (Nat.card_eq_one_iff_unique.mp hcard_one).1
    exact hx_ne (Subsingleton.elim x 1)
  have hk_pos : 0 < k := by
    by_contra hk_not
    have hk_zero : k = 0 := Nat.eq_zero_of_not_pos hk_not
    apply hcard_ne_one
    rw [hcard, hk_zero, pow_zero]
  have hk_ne_one : k ≠ 1 := by
    intro hk_one
    apply hcard_ne_two
    rw [hcard, hk_one, pow_one]
  have hk_two : 2 ≤ k := by omega
  have hg_order : orderOf g = 2 ^ k := by
    rw [← hcard]
    exact orderOf_eq_card_of_forall_mem_zpowers hg_gen
  have hx_mem : x ∈ Subgroup.zpowers g := hg_gen x
  have hx_eq : x = g ^ (2 ^ (k - 1)) :=
    zpowers_involution_eq_pow_pred_of_order_two_pow g x hk_pos hg_order hx_mem hx_sq hx_ne
  refine ⟨g ^ (2 ^ (k - 2)), ?_⟩
  rw [hx_eq, ← pow_mul]
  congr 1
  rw [show k - 1 = k - 2 + 1 by omega, pow_succ]

private lemma square_eq_one_or_unique_involution_of_square_sq_one
    {P : Type*} [Group P] (c a z : P)
    (h_idx : (Subgroup.zpowers c).index = 2)
    (h_z_unique : ∀ y ∈ Subgroup.zpowers c, y ^ 2 = 1 → y ≠ 1 → y = z)
    (h_a_sq_sq : (a ^ 2) ^ 2 = 1) :
    a ^ 2 = 1 ∨ a ^ 2 = z := by
  by_cases h_a_sq_one : a ^ 2 = 1
  · exact Or.inl h_a_sq_one
  · exact Or.inr (h_z_unique (a ^ 2)
      (Subgroup.sq_mem_of_index_two h_idx a) h_a_sq_sq h_a_sq_one)

private lemma two_le_exponent_of_nonabelian_index_two
    {P : Type*} [Group P] [Finite P] (c : P) {k : ℕ}
    (h_nonab : ∃ x y : P, x * y ≠ y * x)
    (h_idx : (Subgroup.zpowers c).index = 2)
    (h_order : orderOf c = 2 ^ k)
    (hk_pos : 0 < k) :
    2 ≤ k := by
  by_contra hk_not
  have hk_eq : k = 1 := by omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card P = 2 ^ 2 := by
    have h := (Subgroup.zpowers c).index_mul_card
    rw [h_idx, Nat.card_zpowers, h_order, hk_eq] at h
    omega
  obtain ⟨x, y, hxy⟩ := h_nonab
  exact hxy ((isMulCommutative_iff.mp
    (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hcard)) x y)

private lemma commutative_of_index_two_zpowers_of_commute_generator
    {P : Type*} [Group P] (c a : P)
    (h_idx : (Subgroup.zpowers c).index = 2)
    (h_a_notmem : a ∉ Subgroup.zpowers c)
    (h_comm : Commute a c) :
    ∀ x y : P, x * y = y * x := by
  let C := Subgroup.zpowers c
  have h_a_inv_notmem : a⁻¹ ∉ C := by
    intro ha
    exact h_a_notmem (C.inv_mem_iff.mp ha)
  have h_repr : ∀ x : P, (∃ m : ℤ, c ^ m = x) ∨ ∃ m : ℤ, x = a * c ^ m := by
    intro x
    by_cases hx : x ∈ C
    · left
      exact Subgroup.mem_zpowers_iff.mp hx
    · right
      have hax : a⁻¹ * x ∈ C := by
        rw [Subgroup.mul_mem_iff_of_index_two h_idx]
        exact iff_of_false h_a_inv_notmem hx
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hax
      exact ⟨m, by
        calc x = a * (a⁻¹ * x) := by group
          _ = a * c ^ m := by rw [← hm]⟩
  intro x y
  rcases h_repr x with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rcases h_repr y with ⟨n, rfl⟩ | ⟨n, rfl⟩
    · exact (Commute.zpow_zpow_self c m n).eq
    · have hcm_a : Commute (c ^ m) a := h_comm.symm.zpow_left m
      calc c ^ m * (a * c ^ n)
          = a * (c ^ m * c ^ n) := hcm_a.left_comm (c ^ n)
        _ = a * (c ^ n * c ^ m) := by rw [(Commute.zpow_zpow_self c m n).eq]
        _ = a * c ^ n * c ^ m := by group
  · rcases h_repr y with ⟨n, rfl⟩ | ⟨n, rfl⟩
    · have hcn_a : Commute (c ^ n) a := h_comm.symm.zpow_left n
      calc (a * c ^ m) * c ^ n
          = a * (c ^ m * c ^ n) := by group
        _ = a * (c ^ n * c ^ m) := by rw [(Commute.zpow_zpow_self c m n).eq]
        _ = c ^ n * (a * c ^ m) := by rw [hcn_a.left_comm]
    · have ham : Commute a (c ^ m) := h_comm.zpow_right m
      have han : Commute a (c ^ n) := h_comm.zpow_right n
      calc (a * c ^ m) * (a * c ^ n)
          = a * a * (c ^ m * c ^ n) := by
            rw [mul_assoc, ham.symm.left_comm]
            group
        _ = a * a * (c ^ n * c ^ m) := by rw [(Commute.zpow_zpow_self c m n).eq]
        _ = a * (a * c ^ n) * c ^ m := by group
        _ = a * (c ^ n * a) * c ^ m := by rw [han.eq]
        _ = (a * c ^ n) * (a * c ^ m) := by
            group

private lemma three_le_exponent_of_nonabelian_twist
    {P : Type*} [Group P] [Finite P] (c a z : P) {k : ℕ}
    (h_nonab : ∃ x y : P, x * y ≠ y * x)
    (h_idx : (Subgroup.zpowers c).index = 2)
    (h_a_notmem : a ∉ Subgroup.zpowers c)
    (hk : 2 ≤ k)
    (h_z_pow : z = c ^ (2 ^ (k - 1)))
    (h_conj : a * c * a⁻¹ = z * c⁻¹) :
    3 ≤ k := by
  by_contra hk_not
  have hk_eq : k = 2 := by omega
  have h_conj_c : a * c * a⁻¹ = c := by
    rw [h_conj, h_z_pow, hk_eq]
    norm_num
    group
  have h_comm : Commute a c := by
    change a * c = c * a
    calc a * c = (a * c * a⁻¹) * a := by group
      _ = c * a := by rw [h_conj_c]
  obtain ⟨x, y, hxy⟩ := h_nonab
  exact hxy (commutative_of_index_two_zpowers_of_commute_generator c a
    h_idx h_a_notmem h_comm x y)

private noncomputable def semiDihedralIsoOfTwistInvolution
    {P : Type*} [Group P] [Finite P]
    (c a z : P) (k : ℕ) (hk : 2 ≤ k) (h_order : orderOf c = 2 ^ k)
    (h_idx : (Subgroup.zpowers c).index = 2)
    (h_a_notmem : a ∉ Subgroup.zpowers c)
    (h_z_pow : z = c ^ (2 ^ (k - 1)))
    (h_a_sq : a ^ 2 = 1)
    (h_conj : a * c * a⁻¹ = z * c⁻¹) :
    P ≃* SemiDihedralGroup k := by
  refine semiDihedralIsoOfTwistNormalized c a k h_order h_idx h_a_notmem h_a_sq ?_
  rw [h_conj, h_z_pow, ← pow_twist_eq_pow_half_mul_inv c hk h_order]

private noncomputable def semiDihedralIsoOfTwistSquareInvolution
    {P : Type*} [Group P] [Finite P]
    (c a z : P) (k : ℕ) (hk : 2 ≤ k) (h_order : orderOf c = 2 ^ k)
    (h_idx : (Subgroup.zpowers c).index = 2)
    (h_a_notmem : a ∉ Subgroup.zpowers c)
    (h_z_mem : z ∈ Subgroup.zpowers c)
    (h_z_pow : z = c ^ (2 ^ (k - 1)))
    (h_z_sq : z ^ 2 = 1)
    (h_a_sq : a ^ 2 = z)
    (h_conj : a * c * a⁻¹ = z * c⁻¹) :
    P ≃* SemiDihedralGroup k := by
  classical
  have hz_comm : Commute z c := by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h_z_mem
    rw [← hm]
    exact Commute.zpow_self c m
  have h_ca_notmem : c * a ∉ Subgroup.zpowers c := by
    intro hca
    apply h_a_notmem
    have ha : a = c⁻¹ * (c * a) := by group
    rw [ha]
    exact Subgroup.mul_mem _
      (Subgroup.inv_mem _ (Subgroup.mem_zpowers c))
      hca
  have h_ca_sq : (c * a) ^ 2 = 1 := by
    calc (c * a) ^ 2
        = (c * a) * (c * a) := by rw [pow_two]
      _ = c * (a * c * a⁻¹) * a ^ 2 := by group
      _ = c * (z * c⁻¹) * z := by rw [h_conj, h_a_sq]
      _ = (c * z * c⁻¹) * z := by group
      _ = z * z := by rw [hz_comm.symm.mul_inv_cancel]
      _ = 1 := by rw [← pow_two, h_z_sq]
  have h_ca_conj : (c * a) * c * (c * a)⁻¹ = z * c⁻¹ := by
    calc (c * a) * c * (c * a)⁻¹
        = c * (a * c * a⁻¹) * c⁻¹ := by group
      _ = c * (z * c⁻¹) * c⁻¹ := by rw [h_conj]
      _ = (c * z * c⁻¹) * c⁻¹ := by group
      _ = z * c⁻¹ := by rw [hz_comm.symm.mul_inv_cancel]
  exact semiDihedralIsoOfTwistInvolution c (c * a) z k hk h_order h_idx
    h_ca_notmem h_z_pow h_ca_sq h_ca_conj

/-- **Isaacs Lemma 6.13 (twist case)**: Let `P` be a finite nonabelian 2-group with a cyclic
subgroup `C = ⟨c⟩` of index `2`, and `a ∈ P − C` with `a * c * a⁻¹ = z * c⁻¹` where `z` is
the unique involution in `C`. Then `P ≃* SemiDihedralGroup k` where `2 ^ k = orderOf c`. -/
theorem semiDihedral_of_twistConjugation
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (h_nonab : ∃ x y : P, x * y ≠ y * x)
    (c a z : P) (h_idx : (Subgroup.zpowers c).index = 2)
    (h_a_notmem : a ∉ Subgroup.zpowers c)
    (h_z_mem : z ∈ Subgroup.zpowers c) (h_z_sq : z ^ 2 = 1) (h_z_ne : z ≠ 1)
    (h_z_unique : ∀ y ∈ Subgroup.zpowers c, y ^ 2 = 1 → y ≠ 1 → y = z)
    (h_conj : a * c * a⁻¹ = z * c⁻¹) :
    ∃ k : ℕ, 2 ^ k = orderOf c ∧ Nonempty (P ≃* SemiDihedralGroup k) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, h_order⟩ := (IsPGroup.iff_orderOf.mp hP) c
  have hk_pos : 0 < k := by
    obtain ⟨_h_z_half, _h_order_even, h_half_pos⟩ :=
      eq_pow_half_orderOf_of_mem_zpowers_sq_eq_one c z h_z_mem h_z_sq h_z_ne
    by_contra hk_not
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk_not
    rw [h_order, hk0] at h_half_pos
    norm_num at h_half_pos
  have hk_two : 2 ≤ k :=
    two_le_exponent_of_nonabelian_index_two c h_nonab h_idx h_order hk_pos
  have h_z_pow : z = c ^ (2 ^ (k - 1)) :=
    zpowers_involution_eq_pow_pred_of_order_two_pow c z hk_pos h_order
      h_z_mem h_z_sq h_z_ne
  have hk_three : 3 ≤ k :=
    three_le_exponent_of_nonabelian_twist c a z h_nonab h_idx h_a_notmem
      hk_two h_z_pow h_conj
  have h_a_sq_sq : (a ^ 2) ^ 2 = 1 := by
    exact sq_eq_one_of_mem_zpowers_fixed_by_twist c a z (a ^ 2)
      hk_three h_order h_z_pow h_conj
      (Subgroup.sq_mem_of_index_two h_idx a)
      (by group)
  refine ⟨k, h_order.symm, ?_⟩
  rcases square_eq_one_or_unique_involution_of_square_sq_one c a z
      h_idx h_z_unique h_a_sq_sq with h_a_sq | h_a_sq
  · exact ⟨semiDihedralIsoOfTwistInvolution c a z k hk_two h_order h_idx
      h_a_notmem h_z_pow h_a_sq h_conj⟩
  · exact ⟨semiDihedralIsoOfTwistSquareInvolution c a z k hk_two h_order h_idx
      h_a_notmem h_z_mem h_z_pow h_z_sq h_a_sq h_conj⟩

private lemma exists_sq_ne_one_of_nonabelian
    {P : Type*} [Group P] (h_nonab : ∃ x y : P, x * y ≠ y * x) :
    ∃ c : P, c ^ 2 ≠ 1 := by
  by_contra h
  push Not at h
  obtain ⟨x, y, hxy⟩ := h_nonab
  have hx_inv : x⁻¹ = x := by
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_two, h x])
  have hy_inv : y⁻¹ = y := by
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_two, h y])
  have hxy_inv : (x * y)⁻¹ = x * y := by
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_two, h (x * y)])
  apply hxy
  calc x * y
      = (x * y)⁻¹ := hxy_inv.symm
    _ = y⁻¹ * x⁻¹ := by rw [mul_inv_rev]
    _ = y * x := by rw [hy_inv, hx_inv]

private lemma exists_orderOf_eq_four_of_card_eight_nonabelian
    {P : Type*} [Group P] [Finite P]
    (h_card : Nat.card P = 8) (h_nonab : ∃ x y : P, x * y ≠ y * x) :
    ∃ c : P, orderOf c = 4 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 P := IsPGroup.of_card (p := 2) (n := 3) (by
    rw [h_card]
    norm_num)
  obtain ⟨c, hc_sq_ne⟩ := exists_sq_ne_one_of_nonabelian h_nonab
  obtain ⟨k, h_order⟩ := (IsPGroup.iff_orderOf.mp hP) c
  have hk_le : k ≤ 3 := by
    have hdvd : 2 ^ k ∣ 2 ^ 3 := by
      have hdvd0 : orderOf c ∣ 8 := by
        rw [← h_card]
        exact orderOf_dvd_natCard c
      rw [h_order] at hdvd0
      simpa using hdvd0
    exact (Nat.pow_dvd_pow_iff_le_right one_lt_two).mp hdvd
  have hk_two : 2 ≤ k := by
    by_contra hk_not
    have hk_cases : k = 0 ∨ k = 1 := by omega
    rcases hk_cases with rfl | rfl
    · rw [pow_zero] at h_order
      have hc_one : c = 1 := orderOf_eq_one_iff.mp h_order
      exact hc_sq_ne (by rw [hc_one, one_pow])
    · rw [pow_one] at h_order
      exact hc_sq_ne (orderOf_dvd_iff_pow_eq_one.mp (by rw [h_order]))
  have hk_ne_three : k ≠ 3 := by
    intro hk3
    have hcyc : IsCyclic P := isCyclic_of_orderOf_eq_card c (by
      rw [h_order, hk3, h_card]
      norm_num)
    obtain ⟨x, y, hxy⟩ := h_nonab
    have : IsCyclic P := hcyc
    exact hxy (Std.Commutative.comm x y)
  have hk_eq : k = 2 := by omega
  exact ⟨c, by rw [h_order, hk_eq]; norm_num⟩

private lemma mem_zpowers_orderOf_four_eq_self_or_inv
    {P : Type*} [Group P] [Finite P] {c y : P}
    (h_order : orderOf c = 4)
    (hy_mem : y ∈ Subgroup.zpowers c)
    (hy_order : orderOf y = 4) :
    y = c ∨ y = c⁻¹ := by
  classical
  have hy_range : y ∈ (Finset.range (orderOf c)).image (fun n : ℕ => c ^ n) :=
    (mem_zpowers_iff_mem_range_orderOf (x := c) (y := y)).mp hy_mem
  rcases Finset.mem_image.mp hy_range with ⟨m, hm_range, hm_eq⟩
  have hm_lt : m < 4 := by
    have := Finset.mem_range.mp hm_range
    rwa [h_order] at this
  have hm_cases : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by omega
  rcases hm_cases with rfl | rfl | rfl | rfl
  · rw [pow_zero] at hm_eq
    rw [← hm_eq, orderOf_one] at hy_order
    norm_num at hy_order
  · left
    simpa using hm_eq.symm
  · have hy_sq : y ^ 2 = 1 := by
      rw [← hm_eq, ← pow_mul]
      change c ^ 4 = 1
      rw [← h_order, pow_orderOf_eq_one]
    have hdvd : 4 ∣ 2 := by
      rw [← hy_order]
      exact orderOf_dvd_of_pow_eq_one hy_sq
    norm_num at hdvd
  · right
    rw [← hm_eq]
    have hmul : c ^ 3 * c = 1 := by
      rw [← pow_succ]
      change c ^ 4 = 1
      rw [← h_order, pow_orderOf_eq_one]
    exact eq_inv_of_mul_eq_one_left hmul

/-- **Isaacs Corollary 6.14**: A nonabelian group of order `8` is isomorphic to `D_8` or `Q_8`
(i.e., `DihedralGroup 4` or `QuaternionGroup 2` in mathlib indexing). -/
theorem dihedralOrQuaternion_of_card_eight
    {P : Type*} [Group P] [Finite P]
    (h_card : Nat.card P = 8) (h_nonab : ∃ x y : P, x * y ≠ y * x) :
    Nonempty (P ≃* DihedralGroup 4) ∨ Nonempty (P ≃* QuaternionGroup 2) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 P := IsPGroup.of_card (p := 2) (n := 3) (by
    rw [h_card]
    norm_num)
  obtain ⟨c, h_order4⟩ :=
    exists_orderOf_eq_four_of_card_eight_nonabelian h_card h_nonab
  have h_idx : (Subgroup.zpowers c).index = 2 := by
    have h := (Subgroup.zpowers c).index_mul_card
    rw [Nat.card_zpowers, h_order4, h_card] at h
    omega
  obtain ⟨a, h_a_notmem, _h_cover⟩ :=
    (Subgroup.index_eq_two_iff_exists_notMem_and.mp h_idx)
  have h_a_inv_notmem : a⁻¹ ∉ Subgroup.zpowers c := by
    intro ha
    exact h_a_notmem ((Subgroup.zpowers c).inv_mem_iff.mp ha)
  have h_ac_notmem : a * c ∉ Subgroup.zpowers c := by
    rw [Subgroup.mul_mem_iff_of_index_two h_idx]
    intro hiff
    exact h_a_notmem (hiff.mpr (Subgroup.mem_zpowers c))
  have hy_mem : a * c * a⁻¹ ∈ Subgroup.zpowers c := by
    rw [Subgroup.mul_mem_iff_of_index_two h_idx]
    exact iff_of_false h_ac_notmem h_a_inv_notmem
  have hy_order : orderOf (a * c * a⁻¹) = 4 := by
    have hsemi : SemiconjBy a c (a * c * a⁻¹) := by
      change a * c = (a * c * a⁻¹) * a
      group
    exact (SemiconjBy.orderOf_eq a hsemi).symm.trans h_order4
  rcases mem_zpowers_orderOf_four_eq_self_or_inv h_order4 hy_mem hy_order with h_conj_fixed | h_conj
  · exfalso
    have h_comm : Commute a c := by
      change a * c = c * a
      calc a * c = (a * c * a⁻¹) * a := by group
        _ = c * a := by rw [h_conj_fixed]
    obtain ⟨x, y, hxy⟩ := h_nonab
    exact hxy (commutative_of_index_two_zpowers_of_commute_generator c a
      h_idx h_a_notmem h_comm x y)
  · rcases dihedralOrQuaternion_of_invertingConjugation hP c a h_idx h_a_notmem h_conj
      with hD | hQ
    · left
      rw [h_order4] at hD
      exact hD
    · right
      have h_half : orderOf c / 2 = 2 := by
        rw [h_order4]
      rw [h_half] at hQ
      exact hQ

/-- **Isaacs Thm 6.12, `|C| = 4` branch**: a self-centralizing normal cyclic subgroup
of order `4` in a nonabelian finite group forces the ambient group to have order `8`, so
Corollary 6.14 applies. -/
theorem dihedralOrQuaternion_of_self_centralizing_cyclic_card_four
    {P : Type*} [Group P] [Finite P]
    {C : Subgroup P} [C.Normal]
    (hC_cyclic : IsCyclic C)
    (hCent : Subgroup.centralizer (C : Set P) = C)
    (hC_card : Nat.card C = 4)
    (h_nonab : ∃ x y : P, x * y ≠ y * x) :
    Nonempty (P ≃* DihedralGroup 4) ∨ Nonempty (P ≃* QuaternionGroup 2) := by
  classical
  have hquot_le : Nat.card (P ⧸ C) ≤ Nat.card (MulAut C) :=
    quotient_card_le_mulAut_of_self_centralizing hCent
  have hmulAut_card : Nat.card (MulAut C) = 2 := by
    have : IsCyclic C := hC_cyclic
    rw [IsCyclic.card_mulAut, hC_card]
    decide
  have hquot_le_two : Nat.card (P ⧸ C) ≤ 2 := by
    rwa [hmulAut_card] at hquot_le
  have hC_ne_top : C ≠ ⊤ := by
    intro hC_top
    have hP_cyclic : IsCyclic P := by
      rw [← Subgroup.topEquiv.isCyclic]
      rwa [← hC_top]
    obtain ⟨x, y, hxy⟩ := h_nonab
    have : IsCyclic P := hP_cyclic
    exact hxy (Std.Commutative.comm x y)
  have hquot_gt_one : 1 < Nat.card (P ⧸ C) :=
    Finite.one_lt_card_iff_nontrivial.mpr
      (Subgroup.nontrivial_quotient_of_ne_top hC_ne_top)
  have hquot_card : Nat.card (P ⧸ C) = 2 := by omega
  have hP_card : Nat.card P = 8 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup C, hquot_card, hC_card]
  exact dihedralOrQuaternion_of_card_eight hP_card h_nonab

end OddOrder.Isaacs.Ch06


