-- Prove2me | solution 1 for Auto.trace_cyclic_diag
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:33:23.619733+00:00
-- url     : https://prove2.me/submissions/8f86c155-7469-4d99-87c1-3d65a2983543

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_trace_mul_three

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
open Auto
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace Auto
theorem _root_.solution (x₀ x₁ x₂ r₀ r₁ r₂ : ι → ℝ) (B₀ B₁ B₂ : Matrix ι ι ℂ) :
    (rdiag x₀ * (rdiag r₀ * B₀ * rdiag r₁) * rdiag x₁ * (rdiag r₁ * B₁ * rdiag r₂) * rdiag x₂ *
      (rdiag r₂ * B₂ * rdiag r₀)).trace = ∑ i, ∑ j, ∑ k, B₀ i j * B₁ j k * B₂ k i * ((x₀ i * r₀ i
      ^ 2 : ℝ) * (x₁ j * r₁ j ^ 2 : ℝ) * (x₂ k * r₂ k ^ 2 : ℝ) : ℝ) := by
  have e : rdiag x₀ * (rdiag r₀ * B₀ * rdiag r₁) * rdiag x₁ * (rdiag r₁ * B₁ * rdiag r₂) *
      rdiag x₂ * (rdiag r₂ * B₂ * rdiag r₀) =
      (rdiag x₀ * (rdiag r₀ * B₀ * rdiag r₁)) * (rdiag x₁ * (rdiag r₁ * B₁ * rdiag r₂)) *
        (rdiag x₂ * (rdiag r₂ * B₂ * rdiag r₀)) := by
    simp only [Matrix.mul_assoc]
  rw [e, trace_mul_three]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => ?_
  simp only [rdiag, Matrix.diagonal_mul, Matrix.mul_diagonal]
  push_cast; ring
end Auto
