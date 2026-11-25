-- Prove2me | Definitions.Def_NashWilliamsLib_Defs
-- name    : NashWilliamsLib_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T17:59:50.842823+00:00
-- url     : https://prove2.me/theorems/34a52069-4cf1-47fb-813b-063993056dd6
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Juan Pablo Traverso Gianini (jtraverso/nash-williams-orientation; see pinned Apache-2.0 LICENSE and source headers)'s pinned Nash-Williams' weak orientation theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Defs.lean

module
public import Mathlib
public import Definitions.Def_NashWilliamsLib_Orientation
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset
namespace NashWilliams
section Multigraph
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
def cut (ends : ι → V × V) (S : Finset V) : ℕ :=
  (Finset.univ.filter fun i => ((ends i).1 ∈ S) ≠ ((ends i).2 ∈ S)).card
def outCut (ends : ι → V × V) (o : ι → Bool) (S : Finset V) : ℕ :=
  (Finset.univ.filter fun i =>
    if o i then (ends i).1 ∈ S ∧ (ends i).2 ∉ S else (ends i).2 ∈ S ∧ (ends i).1 ∉ S).card
end Multigraph
section Simple
variable {V : Type*} (G : SimpleGraph V)
noncomputable def edgeEnds (e : G.edgeSet) : V × V := Quot.out (e : Sym2 V)
def toDigraph (o : G.edgeSet → Bool) : Digraph V where
  Adj a b := ∃ e : G.edgeSet, if o e then edgeEnds G e = (a, b) else edgeEnds G e = (b, a)
end Simple
end NashWilliams


