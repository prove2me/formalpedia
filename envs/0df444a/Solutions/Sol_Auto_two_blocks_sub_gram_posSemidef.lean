-- Prove2me | solution 1 for Auto.two_blocks_sub_gram_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:18:57.502889+00:00
-- url     : https://prove2.me/submissions/710d0242-7fb6-413d-947f-65d7a9e6f521

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_rowMat_gram
public import Theorems.Thm_P2M_Auto_fromBlocks_sub__68b4b78d801e

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace Auto
theorem _root_.solution (A V : Matrix ι ι ℂ) {η : ℝ} (hη : 0 ≤ η) :
    (((2 : ℝ) : ℂ) • Matrix.fromBlocks (Aᴴ * A + (η : ℂ) • 1) 0 0 (V * Vᴴ + (η : ℂ) • 1) -
      ((rowMat A V)ᴴ * rowMat A V + (η : ℂ) • 1)).PosSemidef := by
  have heq : ((2 : ℝ) : ℂ) • Matrix.fromBlocks (Aᴴ * A + (η : ℂ) • 1) 0 0 (V * Vᴴ + (η : ℂ) • 1) -
      ((rowMat A V)ᴴ * rowMat A V + (η : ℂ) • 1) = (rowMat A (-V))ᴴ * rowMat A (-V) + (η : ℂ) • 1 :=
      by
    rw [rowMat_gram, rowMat_gram, ← Matrix.fromBlocks_one]
    simp only [Matrix.fromBlocks_smul, Matrix.fromBlocks_add, fromBlocks_sub']
    congr 1 <;>
      simp only [Matrix.conjTranspose_neg, Matrix.mul_neg, Matrix.neg_mul, neg_neg, smul_zero,
        add_zero, zero_sub, Complex.ofReal_ofNat] <;> module
  rw [heq]
  exact (Matrix.posSemidef_conjTranspose_mul_self _).add (Matrix.PosSemidef.one.smul (by
      exact_mod_cast hη))
end Auto
