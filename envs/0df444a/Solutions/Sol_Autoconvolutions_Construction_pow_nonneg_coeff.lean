-- Prove2me | solution 1 for Autoconvolutions.Construction.pow_nonneg_coeff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:52:58.725171+00:00
-- url     : https://prove2.me/submissions/9a342f27-7ba2-418a-a402-e19951589b0b

module
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.Real.Basic
public import Definitions.Def_Autoconvolutions_Levels
public import Theorems.Thm_Autoconvolutions_Construction_mul_nonneg_coeff

set_option autoImplicit true
@[expose] public section
public section
open Finset Polynomial
open scoped BigOperators
open Autoconvolutions Autoconvolutions.Construction
namespace Autoconvolutions.Construction
theorem _root_.solution {U : Polynomial ℝ} (hU : ∀ k, 0 ≤ U.coeff k) (n k : ℕ) :
    0 ≤ (U ^ n).coeff k := by
  induction n generalizing k with
  | zero => simp only [pow_zero, coeff_one]; split <;> simp
  | succ n ih => rw [pow_succ]; exact mul_nonneg_coeff ih hU k
end Autoconvolutions.Construction
