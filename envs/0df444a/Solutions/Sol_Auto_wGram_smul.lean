-- Prove2me | solution 1 for Auto.wGram_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:31:35.679606+00:00
-- url     : https://prove2.me/submissions/a0c48e1e-f91b-43dc-aad2-f347c45bfc65

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
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
omit [DecidableEq κ] [Fintype κ]
namespace Auto
theorem _root_.solution (B : Matrix ι κ ℂ) (c : ℝ) (f : ι → ℝ) :
    wGram B (c • f) = (c : ℂ) • wGram B f := by
  simp only [wGram, rdiag, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  rw [show (diagonal fun i => (c : ℂ) * (f i : ℂ)) = (c : ℂ) • diagonal fun i => (f i : ℂ) by
    ext i j; by_cases h : i = j <;> simp [h]]
  rw [Matrix.mul_smul, Matrix.smul_mul]
end Auto
