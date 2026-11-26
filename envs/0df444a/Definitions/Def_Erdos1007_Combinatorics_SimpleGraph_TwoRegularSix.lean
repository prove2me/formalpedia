-- Prove2me | Definitions.Def_Erdos1007_Combinatorics_SimpleGraph_TwoRegularSix
-- name    : Erdos1007_Combinatorics_SimpleGraph_TwoRegularSix
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T06:52:59.5845+00:00
-- url     : https://prove2.me/theorems/82535230-7b9f-5195-bc88-b54ce92f22f5
-- title:
--   Two Regular Six
-- statement:
--   Definitions and structural lemmas for Two Regular Six, from Dishant Shah (Dishah3241/Erdos1007; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Unit-distance graphs of dimension four with nine edges (Erdos Problem 1007 extremal half) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Dishah3241/Erdos1007/blob/43f89415a6663848a1445effbda8b3abe77b052b/Erdos1007/Combinatorics/SimpleGraph/TwoRegularSix.lean

module
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.Sort
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SimpleGraph.Sum
set_option autoImplicit false
@[expose] public section
@[expose] public section
namespace Erdos1007
open SimpleGraph
variable {G : SimpleGraph (Fin 6)} [DecidableRel G.Adj]
end Erdos1007


