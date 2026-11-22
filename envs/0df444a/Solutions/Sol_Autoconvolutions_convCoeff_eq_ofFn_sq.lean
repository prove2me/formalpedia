-- Prove2me | solution 1 for Autoconvolutions.convCoeff_eq_ofFn_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:53:42.716792+00:00
-- url     : https://prove2.me/submissions/60b79afa-f963-4ad9-9c8c-a90f3041e2bd

module
public import Definitions.Def_Autoconvolutions_Interpolation
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Definitions.Def_Autoconvolutions_PolyStep

set_option autoImplicit true
@[expose] public section
public section
open Finset Polynomial
noncomputable section
open Autoconvolutions
namespace Autoconvolutions
theorem _root_.solution (d : ℕ) (p : Fin (d+1) → ℝ) (k : ℕ) :
    convCoeff d p (k : ℤ) = (Polynomial.ofFn (d+1) p ^ 2).coeff k := by
  classical
  simp only [convCoeff, pow_two, Polynomial.ofFn_eq_sum_monomial,
    Finset.sum_mul, Finset.mul_sum, Polynomial.finsetSum_coeff,
    Polynomial.monomial_mul_monomial, Polynomial.coeff_monomial]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  norm_cast
  rw [Nat.add_comm i.val j.val, mul_comm (p i) (p j)]
end Autoconvolutions
