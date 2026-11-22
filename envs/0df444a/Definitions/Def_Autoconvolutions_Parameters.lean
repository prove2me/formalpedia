-- Prove2me | Definitions.Def_Autoconvolutions_Parameters
-- name    : Autoconvolutions_Parameters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:47:46.501803+00:00
-- url     : https://prove2.me/theorems/53d2828f-2d6f-42b8-aeaa-79540967e24b
-- title:
--   Parameters
-- statement:
--   Definitions and structural lemmas for Parameters, from Vjekoslav Kovač's pinned Sharpness for autoconvolutions development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Parameters.lean

module
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset
namespace Autoconvolutions.Parameters
noncomputable def factorialRatio (N j : ℕ) : ℝ :=
  (N.factorial : ℝ) ^ 2 / (((N-j).factorial : ℝ) * ((N+j).factorial : ℝ))
noncomputable def geomRatio (q : ℝ) (K : ℕ) : ℝ :=
  (∑ s ∈ range (K+1), (s : ℝ)*q^s) / (∑ s ∈ range (K+1), q^s)^2
end Autoconvolutions.Parameters


