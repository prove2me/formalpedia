-- Prove2me | solution 1 for Auto.sqrt_add_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:31:36.92449+00:00
-- url     : https://prove2.me/submissions/5dea00b6-2029-41f2-9eac-b084641219fa

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
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
open Auto
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]
namespace Auto
theorem _root_.solution {P : Matrix n n ℂ} (hP : P.PosSemidef) {η : ℝ} (hη : 0 ≤ η) :
    CFC.sqrt (P + (η : ℂ) • 1) = (hP.1.eigenvectorUnitary : Matrix n n ℂ) * diagonal (fun i =>
      ((√(hP.1.eigenvalues i + η) : ℝ) : ℂ)) * star (hP.1.eigenvectorUnitary : Matrix n n ℂ) := by
  set U : Matrix n n ℂ := (hP.1.eigenvectorUnitary : Matrix n n ℂ)
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self _
  have hspec : P = U * diagonal (fun i => ((hP.1.eigenvalues i : ℝ) : ℂ)) * star U := by
    have := hP.1.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  refine CFC.sqrt_unique ?_ ?_
  · have hd : diagonal (fun i => ((√(hP.1.eigenvalues i + η) : ℝ) : ℂ)) *
        diagonal (fun i => ((√(hP.1.eigenvalues i + η) : ℝ) : ℂ)) =
        diagonal (fun i => ((hP.1.eigenvalues i : ℝ) : ℂ)) + (η : ℂ) • 1 := by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one, ← Matrix.diagonal_smul,
        Matrix.diagonal_add]
      congr 1; funext i
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by
        linarith [hP.eigenvalues_nonneg i])]
      simp
    calc U * diagonal (fun i => ((√(hP.1.eigenvalues i + η) : ℝ) : ℂ)) * star U *
          (U * diagonal (fun i => ((√(hP.1.eigenvalues i + η) : ℝ) : ℂ)) * star U)
        = U * (diagonal (fun i => ((√(hP.1.eigenvalues i + η) : ℝ) : ℂ)) *
            diagonal (fun i => ((√(hP.1.eigenvalues i + η) : ℝ) : ℂ))) * star U := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (star U) U, hUU, Matrix.one_mul]
      _ = P + (η : ℂ) • 1 := by
          rw [hd, Matrix.mul_add, Matrix.add_mul, ← hspec, Matrix.mul_smul, Matrix.mul_one,
            Matrix.smul_mul, hUU']
  · refine (Matrix.PosSemidef.mul_mul_conjTranspose_same ?_ U).nonneg
    rw [Matrix.posSemidef_diagonal_iff]
    intro i
    exact_mod_cast Real.sqrt_nonneg _
end Auto
