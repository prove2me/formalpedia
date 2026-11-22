-- Prove2me | solution 1 for Autoconvolutions.Flat.P_coeff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:53:24.606264+00:00
-- url     : https://prove2.me/submissions/0bde933b-9cf9-48c2-a1b7-39d77e46ba39

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
public import Theorems.Thm_Autoconvolutions_Flat_P_formula

set_option autoImplicit true
@[expose] public section
public section
open Finset Polynomial
open Autoconvolutions Autoconvolutions.Flat
noncomputable section
namespace Autoconvolutions.Flat
theorem _root_.solution (i h : ℕ) :
    (P i).coeff h = if h ≤ i then weight h * weight (i-h) else 0 := by
  rw [P_formula, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range, Nat.lt_succ_iff]
end Autoconvolutions.Flat
