-- Prove2me | solution 1 for Autoconvolutions.Construction.weight_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:50:29.276602+00:00
-- url     : https://prove2.me/submissions/3b595fff-a12b-42f6-b929-21af221f5e0a

module
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.Real.Basic
public import Definitions.Def_Autoconvolutions_Levels

set_option autoImplicit true
@[expose] public section
public section
open Finset Polynomial
open scoped BigOperators
open Autoconvolutions Autoconvolutions.Construction
namespace Autoconvolutions.Construction
theorem _root_.solution (r b : ℝ) (hr : r ≠ 0) {m i : ℕ} (hi : i ≤ m) :
    r ^ (m - i) * b ^ (m + i) = (r * b) ^ m * (b / r) ^ i := by
  rw [div_pow, mul_pow, pow_add]
  field_simp
  have hpow : r ^ (m - i) * r ^ i = r ^ m := by rw [← pow_add, Nat.sub_add_cancel hi]
  linear_combination b ^ m * b ^ i * hpow
end Autoconvolutions.Construction
