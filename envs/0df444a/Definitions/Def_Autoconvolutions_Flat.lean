-- Prove2me | Definitions.Def_Autoconvolutions_Flat
-- name    : Autoconvolutions_Flat
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:47:44.787014+00:00
-- url     : https://prove2.me/theorems/9cd9ca1e-61f9-423b-9f84-fd945cec74dd
-- title:
--   Flat
-- statement:
--   Definitions and structural lemmas for Flat, from Vjekoslav Kovač's pinned Sharpness for autoconvolutions development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Flat.lean

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
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset Polynomial
namespace Autoconvolutions.Flat
noncomputable section
def weight (n : ℕ) : ℝ := n.centralBinom / (4 : ℝ) ^ n
def rootSeries (x : Polynomial ℝ) : PowerSeries (Polynomial ℝ) :=
  PowerSeries.mk (fun n => C (weight n) * x ^ n)
def P (i : ℕ) : Polynomial ℝ :=
  PowerSeries.coeff i (rootSeries X * rootSeries 1)
def B (K s : ℕ) : Polynomial ℝ :=
  ∑ p ∈ (antidiagonal s).filter (fun p => p.1 ≤ K ∧ p.2 ≤ K), P p.1 * P p.2
end
end Autoconvolutions.Flat


