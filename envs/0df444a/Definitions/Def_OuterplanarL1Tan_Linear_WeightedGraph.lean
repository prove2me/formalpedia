-- Prove2me | Definitions.Def_OuterplanarL1Tan_Linear_WeightedGraph
-- name    : OuterplanarL1Tan_Linear_WeightedGraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:01:31.351061+00:00
-- url     : https://prove2.me/theorems/fec261ec-a1f6-439d-a30b-e24c0b927c0d
-- title:
--   Undirected real edge lengths and finite shortest-path distances
-- statement:
--   An undirected weighted graph consists of a simple graph $G$ on a vertex set $V$ and real edge lengths $w(u,v)=w(v,u)\ge0$ on adjacent vertices. An actual finite walk has length equal to the sum of the lengths of its successive edges. The published shortest-path distance is reused:
--
--   $$d_G(x,y)=\inf\{\operatorname{length}(P):P\text{ is an actual walk from }x\text{ to }y\}.$$
--
--   The separate finite-distance condition requires an actual walk for every pair. Together with nonnegative edge lengths this makes the infimum nonempty and bounded below; on a finite graph a shortest walk is attained after deleting cycles. This general object does not contain any drawing, layers, embedding map, or distortion conclusion.
--
--   **Formalization Note** The underlying graph is Mathlib's `SimpleGraph`; the infimum and walk length are imported from `PlanarL1`. Finiteness is imposed by theorem binders. Arbitrary finite vertex types include empty and singleton types. Zero edge lengths are allowed, so distinct vertices may have zero distance. Nonedges can be assigned length zero. Nonnegative loops can be deleted and each finite parallel-edge family reduced to a minimum-length edge, preserving distances; deleting the other drawn edges can only decrease peeling depth.
-- source:
--   Zihan Tan, Improved Embedding of k-Outerplanar Metrics into ℓ₁, STOC 2027 submission #262 (October 2026), p. 1–2, Theorem 1 and §1.2 (PDF p. 2–3); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/262.pdf; SHA256 0ec64e77e85f536fdf7dc42bb8fdeedaf8861f751861d02b2d5edbdef75ee0ab

import Definitions.Def_PlanarL1

namespace OuterplanarL1Tan.Linear

/-- Finite undirected weighted graphs are obtained by putting a `Fintype` on `V`.
Lengths are independent of a drawing. Only lengths on edges matter. Zero edges
are allowed; no separation axiom is imposed on the resulting distance. -/
structure WeightedGraph (V : Type) where
  graph : SimpleGraph V
  length : V → V → ℝ
  symmetric : ∀ u v, length u v = length v u
  nonnegative : ∀ u v, graph.Adj u v → 0 ≤ length u v

/-- All pair distances are finite: there is an actual walk between each pair.
Unlike `Connected`, this condition also permits the empty vertex type. -/
def WeightedGraph.FiniteDistances {V : Type} (W : WeightedGraph V) : Prop :=
  ∀ u v, Nonempty (W.graph.Walk u v)

/-- A notation wrapper for the published infimum of actual walk lengths.
In all statements using this as a distance, nonnegativity and reachability
make its defining set nonempty and bounded below. -/
noncomputable abbrev WeightedGraph.distance {V : Type} (W : WeightedGraph V)
    (u v : V) : ℝ :=
  OAI.PlanarL1.graphDistance W.graph W.length u v

end OuterplanarL1Tan.Linear


