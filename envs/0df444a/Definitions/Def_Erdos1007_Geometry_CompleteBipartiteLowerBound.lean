-- Prove2me | Definitions.Def_Erdos1007_Geometry_CompleteBipartiteLowerBound
-- name    : Erdos1007_Geometry_CompleteBipartiteLowerBound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T06:52:54.358102+00:00
-- url     : https://prove2.me/theorems/2960b045-f87a-54ec-a370-e364a43e447f
-- title:
--   Complete Bipartite Lower Bound
-- statement:
--   Definitions and structural lemmas for Complete Bipartite Lower Bound, from Dishant Shah (Dishah3241/Erdos1007; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Unit-distance graphs of dimension four with nine edges (Erdos Problem 1007 extremal half) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Dishah3241/Erdos1007/blob/43f89415a6663848a1445effbda8b3abe77b052b/Erdos1007/Geometry/CompleteBipartiteLowerBound.lean

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Algebra.Torsor.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Geometry.Euclidean.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
set_option autoImplicit false
@[expose] public section
namespace Erdos1007
open Module Submodule AffineSubspace EuclideanGeometry
open scoped RealInnerProductSpace
@[expose] public section
end
end Erdos1007


