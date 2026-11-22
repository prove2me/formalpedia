-- Prove2me | solution 1 for Autoconvolutions.Flat.P_coeff_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:54:03.261037+00:00
-- url     : https://prove2.me/submissions/f14cf0ff-28c3-43e2-bbee-d94db89ad53a

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
public import Theorems.Thm_Autoconvolutions_Flat_weight_pos
public import Theorems.Thm_Autoconvolutions_Flat_P_coeff

set_option autoImplicit true
@[expose] public section
public section
open Finset Polynomial
open Autoconvolutions Autoconvolutions.Flat
noncomputable section
namespace Autoconvolutions.Flat
theorem _root_.solution (i h : ℕ) : 0 ≤ (P i).coeff h := by
  rw [P_coeff]
  split
  · exact (mul_pos (weight_pos _) (weight_pos _)).le
  · exact le_rfl
end Autoconvolutions.Flat
