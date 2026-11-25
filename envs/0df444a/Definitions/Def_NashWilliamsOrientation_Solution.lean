-- Prove2me | Definitions.Def_NashWilliamsOrientation_Solution
-- name    : NashWilliamsOrientation_Solution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T18:06:16.835787+00:00
-- url     : https://prove2.me/theorems/1eae87a4-28aa-46ba-9da2-e34e4fe049a6
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from Juan Pablo Traverso Gianini (jtraverso/nash-williams-orientation; see pinned Apache-2.0 LICENSE and source headers)'s pinned Nash-Williams' weak orientation theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/Solution.lean

module
public import Mathlib
public import Definitions.Def_NashWilliamsLib_Defs
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace NashWilliamsOrientation
section Multigraph
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
def cut (ends : ι → V × V) (S : Finset V) : ℕ :=
  (Finset.univ.filter fun i => ((ends i).1 ∈ S) ≠ ((ends i).2 ∈ S)).card
def outCut (ends : ι → V × V) (o : ι → Bool) (S : Finset V) : ℕ :=
  (Finset.univ.filter fun i =>
    if o i then (ends i).1 ∈ S ∧ (ends i).2 ∉ S else (ends i).2 ∈ S ∧ (ends i).1 ∉ S).card
end Multigraph
end NashWilliamsOrientation


