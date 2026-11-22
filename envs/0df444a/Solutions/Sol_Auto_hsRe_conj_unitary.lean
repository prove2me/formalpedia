-- Prove2me | solution 1 for Auto.hsRe_conj_unitary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:04:35.543361+00:00
-- url     : https://prove2.me/submissions/3db0284f-0041-46d8-87cd-388684c9d0c1

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
open Auto
noncomputable section
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
omit [Fintype m] [DecidableEq m]
namespace Auto
theorem _root_.solution (U : Matrix.unitaryGroup n ℂ) (X Y : Matrix n n ℂ) :
    hsRe (star (U : Matrix n n ℂ) * X * (U : Matrix n n ℂ)) (star (U : Matrix n n ℂ) * Y * (U :
      Matrix n n ℂ)) = hsRe X Y := by
  unfold hsRe
  congr 1
  simp only [Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose]
  have hU : (U : Matrix n n ℂ) * (U : Matrix n n ℂ)ᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Unitary.coe_mul_star_self U
  have hU2 : ∀ Z : Matrix n n ℂ, (U : Matrix n n ℂ) * ((U : Matrix n n ℂ)ᴴ * Z) = Z := by
    intro Z; rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
  simp only [Matrix.mul_assoc, hU2]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc, hU, Matrix.mul_one]
end Auto
