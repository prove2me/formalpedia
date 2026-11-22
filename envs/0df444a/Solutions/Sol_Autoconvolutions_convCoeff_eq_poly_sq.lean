-- Prove2me | solution 1 for Autoconvolutions.convCoeff_eq_poly_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:54:19.603058+00:00
-- url     : https://prove2.me/submissions/75f9cfb2-e084-444b-92fe-4bc47f7640ba

module
public import Definitions.Def_Autoconvolutions_Interpolation
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Definitions.Def_Autoconvolutions_PolyStep
public import Theorems.Thm_Autoconvolutions_convCoeff_eq_ofFn_sq

set_option autoImplicit true
@[expose] public section
public section
open Finset Polynomial
noncomputable section
open Autoconvolutions
namespace Autoconvolutions
theorem _root_.solution (F : Polynomial ℝ) (k : ℕ) :
    convCoeff F.natDegree (Polynomial.toFn (F.natDegree + 1) F) (k : ℤ) = (F^2).coeff k := by
  rw [convCoeff_eq_ofFn_sq, Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)]
end Autoconvolutions
