-- Prove2me | solution 1 for Autoconvolutions.Construction.eval_family_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:52:52.604957+00:00
-- url     : https://prove2.me/submissions/4f2619b9-bf38-467d-b166-90ce80ffd570

module
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.Real.Basic
public import Definitions.Def_Autoconvolutions_Levels
public import Theorems.Thm_Autoconvolutions_Construction_weight_eq

set_option autoImplicit true
@[expose] public section
public section
open Finset Polynomial
open scoped BigOperators
open Autoconvolutions Autoconvolutions.Construction
namespace Autoconvolutions.Construction
theorem _root_.solution (P : ℕ → Polynomial ℝ) (U V : Polynomial ℝ) {n K : ℕ}
    (hK : K ≤ n) (hP : ∀ i, (P i).eval 1 = 1) (hU : U.eval 1 ≠ 0) :
    (family P U V n K).eval 1 =
      (U.eval 1 * V.eval 1) ^ n * ∑ i ∈ range (K + 1), (V.eval 1 / U.eval 1) ^ i := by
  classical
  simp only [family, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_pow,
    hP, mul_one, Finset.mul_sum]
  apply sum_congr rfl
  intro i hi
  apply weight_eq _ _ hU
  exact Nat.le_trans (Nat.le_of_lt_succ (mem_range.mp hi)) hK
end Autoconvolutions.Construction
