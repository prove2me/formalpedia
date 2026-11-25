-- Prove2me | Definitions.Def_LeanPool_BeckFialaMatrix_Basic
-- name    : LeanPool_BeckFialaMatrix_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T10:50:09.621519+00:00
-- url     : https://prove2.me/theorems/77bf9061-14b3-459c-ad05-52283429d8d2
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Juan Pablo Traverso Gianini (jtraverso/beck-fiala; see pinned Apache-2.0 LICENSE and source headers)'s pinned The Beck-Fiala integer-making theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/beck-fiala/blob/52f1a12a140b0589ac39619dfd07807d98fdbaf5/LeanPool/BeckFialaMatrix/Basic.lean

module
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset
namespace BeckFialaMatrix
variable {m N : ℕ}
def floatingCoordinates (x : Fin N → ℚ) : Finset (Fin N) :=
  univ.filter (fun i => 0 < x i ∧ x i < 1)
def floatingDegree (A : Fin m → Fin N → ℤ) (x : Fin N → ℚ) (j : Fin m) : ℕ :=
  ((floatingCoordinates x).filter (fun i => A j i = 1)).card
end BeckFialaMatrix


