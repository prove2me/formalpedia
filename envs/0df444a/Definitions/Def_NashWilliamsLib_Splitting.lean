-- Prove2me | Definitions.Def_NashWilliamsLib_Splitting
-- name    : NashWilliamsLib_Splitting
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T17:49:52.316459+00:00
-- url     : https://prove2.me/theorems/3827b8c4-a092-418d-af09-f8b3896e9561
-- title:
--   Splitting
-- statement:
--   Definitions and structural lemmas for Splitting, from Juan Pablo Traverso Gianini (jtraverso/nash-williams-orientation; see pinned Apache-2.0 LICENSE and source headers)'s pinned Nash-Williams' weak orientation theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Splitting.lean

module
public import Definitions.Def_NashWilliamsLib_Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset
namespace NashWilliams
variable {V ι : Type*} [DecidableEq V]
def Joins (s u : V) (p : V × V) : Prop := (p = (s, u) ∨ p = (u, s)) ∧ u ≠ s
def oth (s : V) (p : V × V) : V := if p.1 = s then p.2 else p.1
def dsF (s : V) (ends : ι → V × V) (F : Finset ι) (X : Finset V) : ℕ :=
  (F.filter fun l => ((ends l).1 = s ∧ (ends l).2 ∈ X) ∨ ((ends l).2 = s ∧ (ends l).1 ∈ X)).card
def jn (s : V) (p : V × V) (X : Finset V) : ℕ :=
  if (p.1 = s ∧ p.2 ∈ X) ∨ (p.2 = s ∧ p.1 ∈ X) then 1 else 0
end NashWilliams


