-- Prove2me | Definitions.Def_Scott1976_DataTypesAsLattices_Classification
-- name    : Scott1976_DataTypesAsLattices_Classification
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T03:55:06.82385+00:00
-- url     : https://prove2.me/theorems/ee56d263-6483-4f6d-8feb-87f402710489
-- title:
--   Classification
-- statement:
--   Definitions and structural lemmas for Classification, from Lars Warren Ericson (catskillsresearch/scott1976; original Lean code Apache-2.0; non-Lean reference PDF excluded per NOTICE)'s pinned Dana Scott's Data Types as Lattices (1976): Pomega, continuous functions, fixed points, and lambda models development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Classification.lean

import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
set_option autoImplicit true
namespace Scott1976.DataTypesAsLattices
def charOpen (U : Set Pomega) (x : Pomega) : Pomega :=
  {k | k = 0 ∧ ∃ n, e n ⊆ x ∧ e n ∈ U}
def typicalG : Set Pomega := {x | 0 ∈ x}
def typicalF : Set Pomega := {botElem}
def typicalGdelta : Set Pomega := {topElem}
def typicalFcapG : Set Pomega := {ofNat 0}
def typicalFcapGdelta : Set Pomega := {succSet topElem}
def typicalBdelta : Set Pomega :=
  {u | funOf u (ofNat 0) = funOf u (ofNat 1)}
def typicalSigma11 : Set Pomega :=
  {u | ∃ y, funOf u (ofNat 0) ⬝ y = funOf u (ofNat 1) ⬝ y}
def typicalPi11 : Set Pomega :=
  {u | ∀ y, ∃ z, funOf (funOf u y) z = ofNat 0}
end Scott1976.DataTypesAsLattices


