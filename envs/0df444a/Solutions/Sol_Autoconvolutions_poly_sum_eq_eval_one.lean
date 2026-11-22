-- Prove2me | solution 1 for Autoconvolutions.poly_sum_eq_eval_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:51:21.933805+00:00
-- url     : https://prove2.me/submissions/8e004797-1eb6-47d7-950b-1aadb9778408

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
theorem _root_.solution (F : Polynomial ℝ) :
    (∑ i : Fin (F.natDegree+1), Polynomial.toFn (F.natDegree+1) F i) = F.eval 1 := by
  rw [Polynomial.eval_eq_sum_range, Finset.sum_range]
  simp [Polynomial.toFn]
end Autoconvolutions
