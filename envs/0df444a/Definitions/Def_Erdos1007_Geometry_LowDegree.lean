-- Prove2me | Definitions.Def_Erdos1007_Geometry_LowDegree
-- name    : Erdos1007_Geometry_LowDegree
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T06:53:38.60314+00:00
-- url     : https://prove2.me/theorems/dd70678b-10c6-465a-b45a-52406203d293
-- title:
--   Low Degree
-- statement:
--   Definitions and structural lemmas for Low Degree, from Dishant Shah (Dishah3241/Erdos1007; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Unit-distance graphs of dimension four with nine edges (Erdos Problem 1007 extremal half) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Dishah3241/Erdos1007/blob/43f89415a6663848a1445effbda8b3abe77b052b/Erdos1007/Geometry/LowDegree.lean

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Definitions.Def_Erdos1007_Geometry_EightEdges
public import Definitions.Def_Erdos1007_Geometry_Reattach
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Maps
set_option autoImplicit false
@[expose] public section
namespace Erdos1007
open SimpleGraph Metric
@[expose] public section
end
end Erdos1007


