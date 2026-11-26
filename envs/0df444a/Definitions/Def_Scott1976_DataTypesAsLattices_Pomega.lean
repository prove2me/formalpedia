-- Prove2me | Definitions.Def_Scott1976_DataTypesAsLattices_Pomega
-- name    : Scott1976_DataTypesAsLattices_Pomega
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T03:52:26.520433+00:00
-- url     : https://prove2.me/theorems/8ee64b92-d803-432e-8700-3f1b63c731df
-- title:
--   Pomega
-- statement:
--   Definitions and structural lemmas for Pomega, from Lars Warren Ericson (catskillsresearch/scott1976; original Lean code Apache-2.0; non-Lean reference PDF excluded per NOTICE)'s pinned Dana Scott's Data Types as Lattices (1976): Pomega, continuous functions, fixed points, and lambda models development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Pomega.lean

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
set_option autoImplicit true
namespace Scott1976.DataTypesAsLattices
abbrev Pomega := Set ℕ
def botElem : Pomega := ∅
def topElem : Pomega := Set.univ
def e (n : ℕ) : Pomega := {k | n.testBit k}
def eBelow (x : Pomega) (n : ℕ) : Pomega :=
  {k | e n ⊆ x ∧ k ∈ e n}
def pair (n m : ℕ) : ℕ := (n + m) * (n + m + 1) / 2 + m
def triangle (w : ℕ) : ℕ := w * (w + 1) / 2
end Scott1976.DataTypesAsLattices


