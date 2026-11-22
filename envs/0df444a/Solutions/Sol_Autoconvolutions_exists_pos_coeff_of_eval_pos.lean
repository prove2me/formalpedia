-- Prove2me | solution 1 for Autoconvolutions.exists_pos_coeff_of_eval_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:52:09.947322+00:00
-- url     : https://prove2.me/submissions/b6aacad5-5cae-4c63-b901-5c5db9b340a7

module
public import Definitions.Def_Autoconvolutions_Interpolation
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Definitions.Def_Autoconvolutions_PolyStep
public import Theorems.Thm_Autoconvolutions_poly_sum_eq_eval_one

set_option autoImplicit true
@[expose] public section
public section
open Finset Polynomial
noncomputable section
open Autoconvolutions
namespace Autoconvolutions
theorem _root_.solution (F : Polynomial ℝ) (hF : 0 < F.eval 1) :
    ∃ i : Fin (F.natDegree+1), 0 < Polynomial.toFn (F.natDegree+1) F i := by
  by_contra! h
  rw [← poly_sum_eq_eval_one] at hF
  exact (not_lt_of_ge (Finset.sum_nonpos (fun i _ => h i))) hF
end Autoconvolutions
