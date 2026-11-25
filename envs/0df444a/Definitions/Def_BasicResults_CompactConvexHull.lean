-- Prove2me | Definitions.Def_BasicResults_CompactConvexHull
-- name    : BasicResults_CompactConvexHull
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:27:01.943174+00:00
-- url     : https://prove2.me/theorems/29030280-223f-479d-abd9-0b1a3ab32fbb
-- title:
--   Compact Convex Hull
-- statement:
--   Definitions and structural lemmas for Compact Convex Hull, from Mario Ullrich (mario-ullrich/Lean-SNumbers; see pinned Apache-2.0 LICENSE and source headers)'s pinned Pietsch axiomatic theory of s-numbers and maximal difference bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/CompactConvexHull.lean

module
public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
set_option autoImplicit true
@[expose] public section
@[expose] public section
section CompactConvexHull
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
end CompactConvexHull


