-- Prove2me | solution 1 for Autoconvolutions.Flat.P_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:50:58.477891+00:00
-- url     : https://prove2.me/submissions/b6baac8f-4b6a-459e-a6a8-568ff8dba2f7

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

set_option autoImplicit true
@[expose] public section
public section
open Finset Polynomial
open Autoconvolutions Autoconvolutions.Flat
noncomputable section
namespace Autoconvolutions.Flat
theorem _root_.solution (i : ℕ) :
    P i = ∑ h ∈ range (i+1), C (weight h * weight (i-h)) * X ^ h := by
  rw [P, PowerSeries.coeff_mul]
  simp only [rootSeries, PowerSeries.coeff_mk, one_pow, mul_one]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => C (weight a) * X ^ a * C (weight b)) i]
  apply Finset.sum_congr rfl
  intro h _
  rw [map_mul]
  ring
end Autoconvolutions.Flat
