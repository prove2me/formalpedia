-- Prove2me | Definitions.Def_PetersenLib_Petersen
-- name    : PetersenLib_Petersen
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T12:07:51.204915+00:00
-- url     : https://prove2.me/theorems/f7599f28-f8bc-4b02-82ec-9d69c03e950b
-- title:
--   Petersen
-- statement:
--   Definitions and structural lemmas for Petersen, from Juan Pablo Traverso Gianini (jtraverso/petersen-matching; see pinned Apache-2.0 LICENSE and source headers)'s pinned Petersen's theorem on perfect matchings in bridgeless cubic graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/petersen-matching/blob/77630d6771d3f5a3da2185db2ff451f6c6ed5190/PetersenLib/Petersen.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph
namespace PetersenTheorem
variable {V : Type*}
section Counting
variable [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
def outDarts (C : Finset V) : ℕ := ∑ x ∈ C, (G.neighborFinset x \ C).card
def innDarts (C : Finset V) : ℕ := ∑ x ∈ C, (G.neighborFinset x ∩ C).card
end Counting
end PetersenTheorem


