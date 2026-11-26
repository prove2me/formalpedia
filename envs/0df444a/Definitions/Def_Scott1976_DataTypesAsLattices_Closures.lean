-- Prove2me | Definitions.Def_Scott1976_DataTypesAsLattices_Closures
-- name    : Scott1976_DataTypesAsLattices_Closures
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T03:55:04.300912+00:00
-- url     : https://prove2.me/theorems/a389bf91-dc17-48f6-b86d-a8cef1545e3d
-- title:
--   Closures
-- statement:
--   Definitions and structural lemmas for Closures, from Lars Warren Ericson (catskillsresearch/scott1976; original Lean code Apache-2.0; non-Lean reference PDF excluded per NOTICE)'s pinned Dana Scott's Data Types as Lattices (1976): Pomega, continuous functions, fixed points, and lambda models development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Closures.lean

import Mathlib.Algebra.Ring.Parity
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
set_option autoImplicit true
namespace Scott1976.DataTypesAsLattices
def IsClosure (a : Pomega) : Prop :=
  Icomb ⊆ a ∧ IsRetract a
def IsIsolated (x : Pomega) : Prop :=
  ∃ n, x = e n
def squarePair (x y : Pomega) : Pomega :=
  {k | (∃ n ∈ x, k = 2 * n) ∨ (∃ m ∈ y, k = 2 * m + 1)}
def squareFst (u : Pomega) : Pomega :=
  {n | 2 * n ∈ u}
def squareSnd (u : Pomega) : Pomega :=
  {m | 2 * m + 1 ∈ u}
def boxTensor (a b : Pomega) : Pomega :=
  graph (fun u => squarePair (funOf a (squareFst u)) (funOf b (squareSnd u)))
def boxShift (a : Pomega) : Pomega :=
  graph (fun x => ofNat 0 ∪ succSet (funOf a (predSet x)))
def boxPlus (a b : Pomega) : Pomega :=
  graph (fun u =>
    condSet (squareFst u)
      (squarePair (ofNat 0) (funOf (boxShift a) (squareSnd u)))
      (squarePair (ofNat 1) (funOf (boxShift b) (squareSnd u))))
def Vapply (a x : Pomega) : Pomega :=
  ⋂₀ {y | x ⊆ y ∧ funOf a y ⊆ y}
def representClosure (d : ℕ → Pomega) (x : Pomega) : Pomega :=
  {m | d m ⊆ ⋃ n ∈ x, d n}
def boool : Pomega :=
  graph (fun u => condSet u (ofNat 0) (succSet topElem))
end Scott1976.DataTypesAsLattices


