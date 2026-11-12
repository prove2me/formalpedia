-- Prove2me | Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_InvolutionRecognition
-- name    : OddOrder_Isaacs_Ch06_FrobeniusActions_InvolutionRecognition
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:34:44.627268+00:00
-- url     : https://prove2.me/theorems/7488cd6c-9961-4242-b8a4-65a6638a6bf1
-- title:
--   Isaacs Ch. 6: involution recognition helpers for Lemma 6.13
-- statement:
--   Helpers for Isaacs, *Finite Group Theory*, Lemma 6.13 (pp. 192–193): involution counting and cyclicity criteria in finite 2-groups. A nontrivial 2-subgroup contains an involution; a commutative 2-group with a unique involution (or whose involutions invert a generator) is cyclic; and contradiction lemmas for the dihedral and semidihedral alternatives of Thm 6.12 and 6.11.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 3 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch06_FrobeniusActions/InvolutionRecognition.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch06_FrobeniusActions/InvolutionRecognition.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_FrobeniusGroup

namespace OddOrder.Isaacs.Ch06

open OddOrder.GroupTheory

/-- A finite commutative `2`-group with a unique nontrivial involution is cyclic.

This is the element-level version needed in Isaacs Thm 6.12: it adapts the textbook
“unique involution” hypothesis to the subgroup-level uniqueness used by the finite abelian
`p`-group structure bridge from Thm 6.11. -/
theorem isCyclic_of_comm_two_group_unique_involution
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hcomm : ∀ x y : P, x * y = y * x)
    (hUnique : ∀ x y : P, x ≠ 1 → x ^ 2 = 1 → y ≠ 1 → y ^ 2 = 1 → x = y) :
    IsCyclic P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsMulCommutative P := ⟨⟨hcomm⟩⟩
  refine hP.isCyclic_of_subgroups_card_prime_unique ?_
  intro K L hK_card hL_card
  have hK_two_dvd : 2 ∣ Nat.card K := by rw [hK_card]
  have hL_two_dvd : 2 ∣ Nat.card L := by rw [hL_card]
  obtain ⟨x, hx_order⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 hK_two_dvd
  obtain ⟨y, hy_order⟩ := exists_prime_orderOf_dvd_card' (G := L) 2 hL_two_dvd
  have hx_sq : (x : P) ^ 2 = 1 := by
    have hx_sq_sub : x ^ 2 = 1 := by
      rw [← hx_order, pow_orderOf_eq_one]
    exact congrArg Subtype.val hx_sq_sub
  have hy_sq : (y : P) ^ 2 = 1 := by
    have hy_sq_sub : y ^ 2 = 1 := by
      rw [← hy_order, pow_orderOf_eq_one]
    exact congrArg Subtype.val hy_sq_sub
  have hx_ne : (x : P) ≠ 1 := by
    intro hx_eq_one
    have hx_eq_one' : x = 1 := Subtype.ext hx_eq_one
    have : orderOf x = 1 := by rw [hx_eq_one', orderOf_one]
    exact Nat.prime_two.ne_one (hx_order.symm.trans this)
  have hy_ne : (y : P) ≠ 1 := by
    intro hy_eq_one
    have hy_eq_one' : y = 1 := Subtype.ext hy_eq_one
    have : orderOf y = 1 := by rw [hy_eq_one', orderOf_one]
    exact Nat.prime_two.ne_one (hy_order.symm.trans this)
  have hxy : (x : P) = (y : P) :=
    hUnique (x : P) (y : P) hx_ne hx_sq hy_ne hy_sq
  have hx_order_P : orderOf (x : P) = 2 := orderOf_eq_prime (p := 2) hx_sq hx_ne
  have hy_order_P : orderOf (y : P) = 2 := orderOf_eq_prime (p := 2) hy_sq hy_ne
  have hK_zpowers : Subgroup.zpowers (x : P) = K := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr x.2)
    rw [hK_card, Nat.card_zpowers, hx_order_P]
  have hL_zpowers : Subgroup.zpowers (y : P) = L := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr y.2)
    rw [hL_card, Nat.card_zpowers, hy_order_P]
  rw [← hK_zpowers, ← hL_zpowers, hxy]

/-- If every nontrivial involution in a commutative actor inverts a fixed element whose square
is nontrivial, then that actor has a unique nontrivial involution.

This is the action-theoretic core of the Isaacs 6.12 quotient argument: two distinct
involutions would have a product that fixes the element, while the hypothesis says that the
product must invert it. -/
theorem unique_involution_of_comm_of_involutions_invert_element
    {A N : Type*} [Group A] [Group N] [MulDistribMulAction A N]
    (hcomm : ∀ a b : A, a * b = b * a) {n : N} (hn_sq_ne : n ^ 2 ≠ 1)
    (hinv : ∀ a : A, a ≠ 1 → a ^ 2 = 1 → a • n = n⁻¹) :
    ∀ a b : A, a ≠ 1 → a ^ 2 = 1 → b ≠ 1 → b ^ 2 = 1 → a = b := by
  intro a b ha_ne ha_sq hb_ne hb_sq
  by_contra hab
  have hb_inv : b⁻¹ = b := by
    rw [inv_eq_iff_mul_eq_one, ← sq, hb_sq]
  have hab_prod_ne : a * b ≠ 1 := by
    intro hprod
    apply hab
    calc a = a * 1 := by rw [mul_one]
      _ = a * (b * b⁻¹) := by rw [mul_inv_cancel]
      _ = (a * b) * b⁻¹ := by group
      _ = b := by rw [hprod, one_mul, hb_inv]
  have hab_prod_sq : (a * b) ^ 2 = 1 := by
    calc (a * b) ^ 2 = a * b * (a * b) := by rw [pow_two]
      _ = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hcomm b a]
      _ = a ^ 2 * b ^ 2 := by
        simp [pow_two, mul_assoc]
      _ = 1 := by rw [ha_sq, hb_sq, one_mul]
  have ha_inv : a • n = n⁻¹ := hinv a ha_ne ha_sq
  have hb_inv_n : b • n = n⁻¹ := hinv b hb_ne hb_sq
  have hab_prod_inv : (a * b) • n = n⁻¹ :=
    hinv (a * b) hab_prod_ne hab_prod_sq
  have hab_prod_fix : (a * b) • n = n := by
    rw [mul_smul, hb_inv_n, smul_inv', ha_inv, inv_inv]
  have hn_eq_inv : n = n⁻¹ := hab_prod_fix.symm.trans hab_prod_inv
  apply hn_sq_ne
  rw [pow_two]
  nth_rewrite 1 [hn_eq_inv]
  exact inv_mul_cancel n

/-- A finite commutative `2`-group acting with all involutions inverting a fixed element of
square not equal to `1` is cyclic.

This packages the two Isaacs 6.12 quotient steps: inversion of `c²` gives uniqueness of the
quotient involution, and a commutative finite `2`-group with a unique involution is cyclic. -/
theorem isCyclic_of_comm_two_group_involutions_invert_element
    {A N : Type*} [Group A] [Finite A] [Group N] [MulDistribMulAction A N]
    (hA : IsPGroup 2 A) (hcomm : ∀ a b : A, a * b = b * a)
    {n : N} (hn_sq_ne : n ^ 2 ≠ 1)
    (hinv : ∀ a : A, a ≠ 1 → a ^ 2 = 1 → a • n = n⁻¹) :
    IsCyclic A :=
  isCyclic_of_comm_two_group_unique_involution hA hcomm
    (unique_involution_of_comm_of_involutions_invert_element hcomm hn_sq_ne hinv)

end OddOrder.Isaacs.Ch06


