-- Prove2me | solution 1 for Autoconvolutions.Construction.family_nonneg_coeff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:53:38.193924+00:00
-- url     : https://prove2.me/submissions/29fd20c6-8945-47e8-86d0-1025e3b3a3b0

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
public import Theorems.Thm_Autoconvolutions_Construction_pow_nonneg_coeff

set_option autoImplicit true
@[expose] public section
public section
open Finset Polynomial
open scoped BigOperators
open Autoconvolutions Autoconvolutions.Construction
namespace Autoconvolutions.Construction
theorem _root_.solution (P : ℕ → Polynomial ℝ) {U V : Polynomial ℝ}
    (hP : ∀ i k, 0 ≤ (P i).coeff k) (hU : ∀ k, 0 ≤ U.coeff k)
    (hV : ∀ k, 0 ≤ V.coeff k) (n K k : ℕ) : 0 ≤ (family P U V n K).coeff k := by
  rw [family, finsetSum_coeff]
  apply sum_nonneg
  intro i _
  exact mul_nonneg_coeff (mul_nonneg_coeff (pow_nonneg_coeff hU _) (pow_nonneg_coeff hV _)) (hP i) k
end Autoconvolutions.Construction
