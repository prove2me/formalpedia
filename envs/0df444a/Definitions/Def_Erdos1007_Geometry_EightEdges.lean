-- Prove2me | Definitions.Def_Erdos1007_Geometry_EightEdges
-- name    : Erdos1007_Geometry_EightEdges
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T06:53:16.537622+00:00
-- url     : https://prove2.me/theorems/22000d0e-bf5f-57ef-9827-df858a89b1f5
-- title:
--   Eight Edges
-- statement:
--   Definitions and structural lemmas for Eight Edges, from Dishant Shah (Dishah3241/Erdos1007; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Unit-distance graphs of dimension four with nine edges (Erdos Problem 1007 extremal half) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Dishah3241/Erdos1007/blob/43f89415a6663848a1445effbda8b3abe77b052b/Erdos1007/Geometry/EightEdges.lean

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Definitions.Def_Erdos1007_Geometry_CompleteMinusEdge
public import Definitions.Def_Erdos1007_Geometry_Reattach
public import Definitions.Def_Erdos1007_Geometry_UnitDistanceComap
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Fin.Embedding
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Tactic.Linarith
set_option autoImplicit false
@[expose] public section
namespace Erdos1007
universe u
open SimpleGraph Metric
@[expose] public section
end
end Erdos1007


