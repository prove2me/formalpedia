-- Prove2me | Definitions.Def_NearLinearRSP_TwoResources_Digraph
-- name    : NearLinearRSP_TwoResources_Digraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:19:51.373416+00:00
-- url     : https://prove2.me/theorems/9b78ab2e-8e82-4480-97c5-933a84cec58d
-- title:
--   Finite directed graphs with an ordered edge enumeration
-- statement:
--   A finite directed graph has a natural number $n$ of vertices and a fixed enumeration $E$ of distinct directed edges. Its vertices and edges satisfy
--   $$
--   V=\{0,\ldots,n-1\},\qquad E\subseteq V\times V.
--   $$
--   Self-loops and directed cycles are allowed; no acyclicity, connectivity, positivity or resource data is bundled into this general graph object. The enumeration fixes deterministic tie-breaking without changing the set of admissible graphs. An empty graph is allowed at this layer; choosing a source in a resource instance entails that its vertex set is nonempty.
--
--   This graph definition is separate from the restricted-shortest-path instance, so other finite directed-graph developments can reuse it.
-- source:
--   Vikrant Ashvinkumar, STOC 2027 submission #289 (October 2026), p.4, Section 2 (Graphs)

import Mathlib

set_option autoImplicit false

namespace NearLinearRSP.TwoResources

/-- Finite directed graph, with an input ordering of its distinct arcs. -/
structure Digraph where
  n : ℕ
  edges : List (ℕ × ℕ)
  distinct : edges.Nodup
  endpoints : ∀ e ∈ edges, e.1 < n ∧ e.2 < n

end NearLinearRSP.TwoResources


