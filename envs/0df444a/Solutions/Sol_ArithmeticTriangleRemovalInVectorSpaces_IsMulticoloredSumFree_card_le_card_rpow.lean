-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.IsMulticoloredSumFree.card_le_card_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:17:00.170905+00:00
-- url     : https://prove2.me/submissions/599b985d-d847-42fc-a3bc-a62dc18f02db

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Basic
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Exponent
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_SliceRank
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_TensorPower
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_le_of_forall_pow_le_mul_pow
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_IsMulticoloredSumFree_card_le_three_mul_card
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_IsMulticoloredSumFree_map
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_IsMulticoloredSumFree_pi
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_card_lowDegreeExponents_le
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_le_rpow_one_sub_c
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_three_div_two_le_rpow_mul_sum

section
public section
open Finset Module
namespace ArithmeticTriangleRemovalInVectorSpaces
variable {p : ℕ} [Fact p.Prime] {G ι : Type*} [AddCommGroup G] [Module (ZMod p) G] [Fintype ι]
  {x y z : ι → G}
private lemma IsMulticoloredSumFree.card_le_three_mul_pow [Finite G]
    (h : IsMulticoloredSumFree x y z) {t : ℝ} (ht₀ : 0 < t) (ht₁ : t ≤ 1) :
    Fintype.card ι ≤
      3 * (t ^ (-((p : ℝ) - 1) / 3) * ∑ j ∈ range p, t ^ j) ^ finrank (ZMod p) G := by
  let e := (Module.finBasis (ZMod p) G).equivFun
  grw [← card_lowDegreeExponents_le (Fact.out : p.Prime).one_lt.le _ ht₀ ht₁]
  exact_mod_cast (h.map e.toLinearMap.toAddMonoidHom e.injective).card_le_three_mul_card
private lemma IsMulticoloredSumFree.card_le_pow [Finite G] (h : IsMulticoloredSumFree x y z) {t : ℝ}
    (ht₀ : 0 < t) (ht₁ : t < 1) :
    Fintype.card ι ≤ (t ^ (-((p : ℝ) - 1) / 3) * ∑ j ∈ range p, t ^ j) ^ finrank (ZMod p) G := by
  refine le_of_forall_pow_le_mul_pow (M := 3) (pow_pos ?_ _) ?_
  · linarith [three_div_two_le_rpow_mul_sum (Fact.out : p.Prime).two_le ht₀ ht₁]
  · intro k
    have := (h.pi (Fin k)).card_le_three_mul_pow (p := p) ht₀ ht₁.le
    rw [finrank_pi_fintype, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, pow_mul',
      Fintype.card_fun, Fintype.card_fin] at this
    exact_mod_cast this
end ArithmeticTriangleRemovalInVectorSpaces
end
end

set_option autoImplicit true
@[expose] public section
public section
open Finset Module
open ArithmeticTriangleRemovalInVectorSpaces
variable {p : ℕ} [Fact p.Prime] {G ι : Type*} [AddCommGroup G] [Module (ZMod p) G] [Fintype ι]
  {x y z : ι → G}
namespace ArithmeticTriangleRemovalInVectorSpaces
namespace IsMulticoloredSumFree
theorem _root_.solution [Fintype G] (h : IsMulticoloredSumFree x y z) :
    (Fintype.card ι : ℝ) ≤ Fintype.card G ^ (1 - c p) := by
  have hp := (Fact.out : p.Prime).two_le
  rw [card_eq_pow_finrank (K := ZMod p) (V := G), ZMod.card, Nat.cast_pow, ← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity), mul_comm, Real.rpow_mul (by positivity), Real.rpow_natCast]
  rcases Nat.eq_zero_or_pos (finrank (ZMod p) G) with hd | hd
  · simpa [hd] using h.card_le_pow (p := p) (t := 1 / 2) (by norm_num) (by norm_num)
  rw [← Real.rpow_inv_natCast_pow (Nat.cast_nonneg (Fintype.card ι)) hd.ne']
  gcongr
  apply le_rpow_one_sub_c hp
  intro t ht₀ ht₁
  rw [Real.rpow_inv_le_iff_of_pos (by positivity)
    (by linarith [three_div_two_le_rpow_mul_sum hp ht₀ ht₁]) (by positivity), Real.rpow_natCast]
  exact h.card_le_pow ht₀ ht₁
end IsMulticoloredSumFree
end ArithmeticTriangleRemovalInVectorSpaces
