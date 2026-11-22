-- Prove2me | solution 1 for Autoconvolutions.Construction.mul_nonneg_coeff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:50:30.240806+00:00
-- url     : https://prove2.me/submissions/f7186051-002f-4e08-9354-9ab4ecf1745b

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
theorem _root_.solution {U V : Polynomial ℝ}
    (hU : ∀ k, 0 ≤ U.coeff k) (hV : ∀ k, 0 ≤ V.coeff k) (k : ℕ) :
    0 ≤ (U * V).coeff k := by
  rw [coeff_mul]
  exact sum_nonneg fun ij _ => mul_nonneg (hU ij.1) (hV ij.2)
end Autoconvolutions.Construction
