-- Prove2me | solution 1 for Auto.holder_three_halves
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:51:33.933564+00:00
-- url     : https://prove2.me/submissions/c96f6061-6b0f-4bfb-9924-f021a8f55f85

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
open Auto
noncomputable section
namespace Auto
theorem _root_.solution {κ : Type*} (s : Finset κ) (μ a : κ → ℝ) (hμ : ∀ k, 0 ≤ μ k)
    (ha : ∀ k, 0 ≤ a k) :
    (∑ k ∈ s, μ k * a k) ^ (3 / 2 : ℝ) ≤ (∑ k ∈ s, μ k) ^ (1 / 2 : ℝ) * ∑ k ∈ s, μ k * a k ^ (3
      / 2 : ℝ) := by
  have h := Real.inner_le_weight_mul_Lp_of_nonneg s (p := 3 / 2) (by norm_num) μ a hμ ha
  have hX : 0 ≤ ∑ k ∈ s, μ k * a k := Finset.sum_nonneg fun k _ => mul_nonneg (hμ k) (ha k)
  have hQ : 0 ≤ ∑ k ∈ s, μ k := Finset.sum_nonneg fun k _ => hμ k
  have hY : 0 ≤ ∑ k ∈ s, μ k * a k ^ (3 / 2 : ℝ) :=
    Finset.sum_nonneg fun k _ => mul_nonneg (hμ k) (Real.rpow_nonneg (ha k) _)
  have := Real.rpow_le_rpow hX h (by norm_num : (0 : ℝ) ≤ 3 / 2)
  rw [Real.mul_rpow (Real.rpow_nonneg hQ _) (Real.rpow_nonneg hY _), ← Real.rpow_mul hQ,
    ← Real.rpow_mul hY] at this
  norm_num at this
  exact this
end Auto
