-- Prove2me | solution 1 for Autoconvolutions.Flat.P_eval_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:53:12.920997+00:00
-- url     : https://prove2.me/submissions/5738513c-9840-4deb-8479-121b2044bb1b

module
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Definitions.Def_Autoconvolutions_Flat
public import Theorems.Thm_Autoconvolutions_Flat_weight_convolution
public import Theorems.Thm_Autoconvolutions_Flat_P_formula

set_option autoImplicit true
@[expose] public section
public section
open Finset Polynomial
open Autoconvolutions Autoconvolutions.Flat
noncomputable section
namespace Autoconvolutions.Flat
theorem _root_.solution (i : ℕ) : (P i).eval 1 = 1 := by
  rw [P_formula, Polynomial.eval_finsetSum]
  simpa using (Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => weight a * weight b) i).symm.trans (weight_convolution i)
end Autoconvolutions.Flat
