-- Prove2me | Definitions.Def_Erdos1007_Combinatorics_SimpleGraph_SixVertices
-- name    : Erdos1007_Combinatorics_SimpleGraph_SixVertices
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T06:53:27.010396+00:00
-- url     : https://prove2.me/theorems/66bf1c68-fe2c-4fb7-9036-c8da562580fe
-- title:
--   Six Vertices
-- statement:
--   Definitions and structural lemmas for Six Vertices, from Dishant Shah (Dishah3241/Erdos1007; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Unit-distance graphs of dimension four with nine edges (Erdos Problem 1007 extremal half) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Dishah3241/Erdos1007/blob/43f89415a6663848a1445effbda8b3abe77b052b/Erdos1007/Combinatorics/SimpleGraph/SixVertices.lean

module
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Definitions.Def_Erdos1007_Combinatorics_SimpleGraph_TwoRegularSix
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Sum
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Order.BooleanAlgebra.Basic
set_option autoImplicit false
@[expose] public section
namespace Erdos1007
open SimpleGraph
def isoOfComplIso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : Gᶜ ≃g H) : G ≃g Hᶜ where
  toEquiv := e.toEquiv
  map_rel_iff' {a b} := by
    rw [compl_adj, e.toEquiv.injective.ne_iff, not_congr e.map_rel_iff', ← compl_adj,
      compl_compl]
def isoOfEq {V : Type*} {G H : SimpleGraph V} (h : G = H) : G ≃g H where
  toEquiv := Equiv.refl V
  map_rel_iff' := by
    subst h
    intro a b
    rfl
@[expose] public section
end
end Erdos1007


