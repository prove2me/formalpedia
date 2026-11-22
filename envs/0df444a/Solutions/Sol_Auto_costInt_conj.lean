-- Prove2me | solution 1 for Auto.costInt_conj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:06:53.544291+00:00
-- url     : https://prove2.me/submissions/60aa2846-348f-4ced-b6b2-aa8fb85507d5

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_hsRe_conj_unitary
public import Theorems.Thm_Auto_hsRe_diagonal_mul
public import Theorems.Thm_Auto_hsRe_mul_diagonal

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
theorem _root_.solution (U : Matrix.unitaryGroup n ℂ) (a : n → ℝ) {A : Matrix n n ℂ}
    (hA : A = (U : Matrix n n ℂ) * diagonal (fun i => (a i : ℂ)) * star (U : Matrix n n ℂ))
    (K X : Matrix n n ℂ) :
    costInt A K X = ∑ i, ∑ j, (2 * ((starRingEnd ℂ) ((star (U : Matrix n n ℂ) * K * (U : Matrix
      n n ℂ)) i j) * (star (U : Matrix n n ℂ) * X * (U : Matrix n n ℂ)) i j).re - (a i + a j) *
      ‖(star (U : Matrix n n ℂ) * X * (U : Matrix n n ℂ)) i j‖ ^ 2) := by
  set D : Matrix n n ℂ := diagonal fun i => (a i : ℂ)
  set Xt := star (U : Matrix n n ℂ) * X * U
  set Kt := star (U : Matrix n n ℂ) * K * U
  have hUU : star (U : Matrix n n ℂ) * U = 1 := Unitary.coe_star_mul_self U
  have e1 : star (U : Matrix n n ℂ) * (A * X) * U = D * Xt := by
    rw [hA]
    simp only [Xt, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
  have e2 : star (U : Matrix n n ℂ) * (X * A) * U = Xt * D := by
    rw [hA]
    simp only [Xt, Matrix.mul_assoc, hUU, Matrix.mul_one]
  have h1 : hsRe K X = hsRe Kt Xt := (hsRe_conj_unitary U K X).symm
  have h2 : hsRe X (A * X) = hsRe Xt (D * Xt) := by
    rw [← hsRe_conj_unitary U X (A * X), e1]
  have h3 : hsRe X (X * A) = hsRe Xt (Xt * D) := by
    rw [← hsRe_conj_unitary U X (X * A), e2]
  rw [costInt, h1, h2, h3, hsRe_diagonal_mul, hsRe_mul_diagonal, hsRe_eq_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring
end Auto
