-- Prove2me | Definitions.Def_Erdos1007_Geometry_Reattach
-- name    : Erdos1007_Geometry_Reattach
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T06:52:57.106095+00:00
-- url     : https://prove2.me/theorems/addd17b2-97b7-50f5-875f-d3ab0bbd027c
-- title:
--   Reattach
-- statement:
--   Definitions and structural lemmas for Reattach, from Dishant Shah (Dishah3241/Erdos1007; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Unit-distance graphs of dimension four with nine edges (Erdos Problem 1007 extremal half) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Dishah3241/Erdos1007/blob/43f89415a6663848a1445effbda8b3abe77b052b/Erdos1007/Geometry/Reattach.lean

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.LinearAlgebra.AffineSpace.Midpoint
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
set_option autoImplicit false
@[expose] public section
namespace Erdos1007
open SimpleGraph Metric
open scoped RealInnerProductSpace
@[expose] public section
end
end Erdos1007


