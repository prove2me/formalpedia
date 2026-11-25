-- Prove2me | Definitions.Def_SpectralGraphBounds_Solution
-- name    : SpectralGraphBounds_Solution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T12:18:49.955026+00:00
-- url     : https://prove2.me/theorems/c23e021a-ce88-5d87-be3c-b4dfd261af55
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from Juan Pablo Traverso Gianini (jtraverso/spectral-graph-bounds; see pinned Apache-2.0 LICENSE and source headers)'s pinned Spectral bounds on the chromatic and independence numbers (Wilf and Hoffman) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/spectral-graph-bounds/blob/8d8b4ce17e56165b5f1ad3b285fb141666804e1c/Solution.lean

module
public import Mathlib
public import Definitions.Def_SpectralLib_SpectralBounds
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset SimpleGraph
namespace AdjacencySpectrum
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V)
  [DecidableRel G.Adj] (hA : (G.adjMatrix ℝ).IsHermitian)
end AdjacencySpectrum


