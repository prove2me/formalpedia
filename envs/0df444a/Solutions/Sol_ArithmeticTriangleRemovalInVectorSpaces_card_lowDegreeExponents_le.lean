-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.card_lowDegreeExponents_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:14:49.323238+00:00
-- url     : https://prove2.me/submissions/aed1efde-90f0-4644-864d-3d47a6b3711e

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Monomials

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ArithmeticTriangleRemovalInVectorSpaces
namespace ArithmeticTriangleRemovalInVectorSpaces
theorem _root_.solution {p : ℕ} (hp : 1 ≤ p) (d : ℕ) {x : ℝ} (hx₀ : 0 < x)
    (hx₁ : x ≤ 1) :
    #(lowDegreeExponents p d) ≤ (x ^ (-((p : ℝ) - 1) / 3) * ∑ j ∈ range p, x ^ j) ^ d := by
  calc (#(lowDegreeExponents p d) : ℝ)
      = ∑ α ∈ lowDegreeExponents p d, 1 := by simp
    _ ≤ ∑ α ∈ lowDegreeExponents p d, x ^ ((∑ t, α t : ℕ) - ((p : ℝ) - 1) * d / 3) := by
      gcongr with α hα
      refine Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx₀ hx₁ ?_
      obtain ⟨-, h⟩ := mem_filter.1 hα
      rw [← Nat.cast_le (α := ℝ)] at h
      push_cast [Nat.cast_sub hp] at h ⊢
      linarith
    _ ≤ ∑ α ∈ Fintype.piFinset fun _ : Fin d ↦ range p,
          x ^ ((∑ t, α t : ℕ) - ((p : ℝ) - 1) * d / 3) := by
      apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      intros
      positivity
    _ = x ^ (-(((p : ℝ) - 1) * d / 3)) * ∏ _t : Fin d, ∑ j ∈ range p, x ^ j := by
      rw [prod_univ_sum, mul_sum]
      congr with α
      rw [Real.rpow_sub hx₀, Real.rpow_natCast, ← prod_pow_eq_pow_sum, div_eq_mul_inv,
        Real.rpow_neg hx₀.le, mul_comm]
    _ = _ := by
      rw [prod_const, card_univ, Fintype.card_fin, mul_pow, ← Real.rpow_mul_natCast hx₀.le]
      ring_nf
end ArithmeticTriangleRemovalInVectorSpaces
