-- Prove2me | solution 1 for Auto.rowMat_cost_unitary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:13:49.674008+00:00
-- url     : https://prove2.me/submissions/b35d0e62-34f1-4141-8e09-4b6eddffa62f

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_matCost_isometry

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
open Auto
noncomputable section
attribute [local instance] Auto._p2m_local_instance_5846efa9ac_1611
attribute [local instance] Auto._p2m_local_instance_5846efa9ac_1612
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (W0 W1 W2 D0 D1 D2 : Matrix ι ι ℂ)
namespace Auto
theorem _root_.solution (R : Matrix ι (ι ⊕ ι) ℂ) (Uu : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)
    (hU : Uu * Uuᴴ = 1) (Dv : Matrix ι ι ℂ) :
    matCost ((R * Uu)ᴴ * (R * Uu)) ((R * Uu)ᴴ * Dv * (R * Uu)) = matCost (Rᴴ * R) (Rᴴ * Dv * R) :=
        by
  have hE : (Uuᴴ)ᴴ * Uuᴴ = 1 := by rw [Matrix.conjTranspose_conjTranspose]; exact hU
  have h1 : (R * Uu)ᴴ * (R * Uu) = Uuᴴ * (Rᴴ * R) * (Uuᴴ)ᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]; simp only [Matrix.mul_assoc]
  have h2 : (R * Uu)ᴴ * Dv * (R * Uu) = Uuᴴ * (Rᴴ * Dv * R) * (Uuᴴ)ᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]; simp only [Matrix.mul_assoc]
  rw [h1, h2]
  exact matCost_isometry Uuᴴ hE (Matrix.posSemidef_conjTranspose_mul_self R) _
end Auto
