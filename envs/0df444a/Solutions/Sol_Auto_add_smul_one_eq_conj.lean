-- Prove2me | solution 1 for Auto.add_smul_one_eq_conj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:41:08.329038+00:00
-- url     : https://prove2.me/submissions/e0ccae4f-36c6-4998-9f1b-ba194e98bf0f

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
variable {n : Type*} [Fintype n] [DecidableEq n]
namespace Auto
theorem _root_.solution {P : Matrix n n ℂ} (hP : P.IsHermitian) (c : ℝ) :
    P + (c : ℂ) • 1 = (hP.eigenvectorUnitary : Matrix n n ℂ) * diagonal (fun i =>
      ((hP.eigenvalues i + c : ℝ) : ℂ)) * star (hP.eigenvectorUnitary : Matrix n n ℂ) := by
  have hUU : (hP.eigenvectorUnitary : Matrix n n ℂ) *
      star (hP.eigenvectorUnitary : Matrix n n ℂ) = 1 := Unitary.coe_mul_star_self _
  conv_lhs => rw [hP.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rw [show diagonal (fun i => ((hP.eigenvalues i + c : ℝ) : ℂ)) =
    diagonal (RCLike.ofReal ∘ hP.eigenvalues) + (c : ℂ) • 1 by
      ext i j; by_cases h : i = j <;> simp [h]]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hUU]
end Auto
