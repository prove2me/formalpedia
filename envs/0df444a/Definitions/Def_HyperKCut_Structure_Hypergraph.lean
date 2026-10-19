-- Prove2me | Definitions.Def_HyperKCut_Structure_Hypergraph
-- name    : HyperKCut_Structure_Hypergraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:16:42.907127+00:00
-- url     : https://prove2.me/theorems/3c5e49ce-2293-4a24-bb1a-ee1eceb64ca3
-- title:
--   §1.1 — finite unit-cost multihypergraph
-- statement:
--   A finite unit-cost hypergraph $G=(V,E)$ has a finite vertex set $V$ and finitely many hyperedges, each a subset of $V$. Parallel copies of the same vertex set are permitted and counted separately. Empty and singleton edges are permitted, but they never cross a cut.
--
--   This general hypergraph object is reused by all the cut and partition definitions of the mission.
--
--   **Formalization Note** The edge collection is a multiset of finite vertex sets, so a repeated hyperedge has its own unit cost.
-- source:
--   Chandrasekaran & Chekuri, Hypergraph k-cut for fixed k in deterministic polynomial time, arXiv:2009.12442v1, p. 3 (PDF 4), §1.1 (unit-cost convention and parallel edges); p. 1 (PDF 2), hypergraph definition

import Mathlib

namespace HyperKCut.Structure

/-- A finite unit-cost hypergraph. The multiset records parallel copies of an edge. -/
structure Hypergraph (V : Type) [Fintype V] where
  edges : Multiset (Finset V)

end HyperKCut.Structure


