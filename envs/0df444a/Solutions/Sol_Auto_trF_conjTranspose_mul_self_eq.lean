-- Prove2me | solution 1 for Auto.trF_conjTranspose_mul_self_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:04:58.547976+00:00
-- url     : https://prove2.me/submissions/c2e985ad-70bc-49ef-9480-addee5a2d3f8

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_trF_eq_sum
public import Theorems.Thm_Auto_sum_eigenvalues_eq_roots

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
open Auto
noncomputable section
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
namespace Auto
theorem _root_.solution (f : ℝ → ℝ) (hf : f 0 = 0) (R : Matrix m n ℂ) :
    trF f (Rᴴ * R) = trF f (R * Rᴴ) := by
  have h1 : (Rᴴ * R).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self R
  have h2 : (R * Rᴴ).IsHermitian := Matrix.isHermitian_mul_conjTranspose_self R
  rw [trF_eq_sum f h1, trF_eq_sum f h2]
  set g : ℂ → ℝ := fun z => f z.re
  have e1 : ∑ i, f (h1.eigenvalues i) = ∑ i, g (h1.eigenvalues i) := by simp [g]
  have e2 : ∑ i, f (h2.eigenvalues i) = ∑ i, g (h2.eigenvalues i) := by simp [g]
  rw [e1, e2, sum_eigenvalues_eq_roots g h1, sum_eigenvalues_eq_roots g h2]
  have hc := Matrix.charpoly_mul_comm' R Rᴴ
  have hroots := congrArg Polynomial.roots hc
  rw [Polynomial.roots_mul (by
      exact mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (Matrix.charpoly_monic _).ne_zero),
    Polynomial.roots_mul (by
      exact mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (Matrix.charpoly_monic _).ne_zero),
    Polynomial.roots_X_pow, Polynomial.roots_X_pow] at hroots
  have hm := congrArg (fun s => (s.map g).sum) hroots
  simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_nsmul, Multiset.sum_nsmul,
    Multiset.map_singleton, Multiset.sum_singleton, g, Complex.zero_re, hf, smul_zero,
    zero_add] at hm
  exact hm.symm
end Auto
