-- Prove2me | Definitions.Def_WeightedRainbowCycle_Weighted_Model
-- name    : WeightedRainbowCycle_Weighted_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:05:24.36185+00:00
-- url     : https://prove2.me/theorems/58ca544e-57f1-4e35-8100-a474dc9a2bd4
-- title:
--   Weighted loopless list graphs, degrees and boundary mass
-- statement:
--   Let $V$ and $E$ be finite vertex and edge sets, and let $C$ be any color set. A model consists of a loopless undirected Mathlib multigraph with exactly these vertices and edges, an arbitrary weight $w(e)\ge0$ for each edge, and a nonempty finite set $L(e)\subseteq C$ for each edge. Parallel edges are retained as distinct identities. Define the weighted average degree and weighted color-degree by
--
--   $$d(G)=\frac{2\sum_{e\in E}w(e)}{|V|},\qquad \deg_c(u)=\sum_{e\ni u,\ c\in L(e)}w(e).$$
--
--   The structural admissibility predicate for an integer $\ell$ and real $\Delta$ means $|L(e)|\le\ell$ on every edge and $\deg_c(u)\le\Delta$ for every vertex and color. For $S\subseteq V$, the boundary mass is the sum of weights of edges with exactly one endpoint in $S$. The finite active color set is $\bigcup_{e\in E}L(e)$; it does not restrict the ambient set $C$.
--
--   These definitions supply the actual graph quantities in the theorem and derivative bound. They impose no proper coloring, connectivity, density, integrality, or positive lower weight bound.
--
--   **Formalization Note** All vertices and edges of the Mathlib graph are used. Weights remain real and may be zero. The average degree on an empty vertex type is totalized to zero; the goal only uses sufficiently large vertex sets. Incidence counts an edge once. The graph representation allows parallel edges, extending the usual simple graph setting.
-- source:
--   Andrew D. Lin, STOC 2027 submission #545 (October 2026), Theorem 1.1, pp. 2 and 8; boundary notation in Lemmas 4.1–4.2, p. 8; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/545.pdf

import Mathlib

set_option autoImplicit false
noncomputable section

namespace WeightedRainbowCycle.Weighted

/-- Theorem 1.1, pp. 2, 8: loopless weighted list graph, on the existing Mathlib multigraph. -/
structure Model (V E C : Type*) where
  graph : Graph V E
  allVertices : graph.vertexSet = Set.univ
  allEdges : graph.edgeSet = Set.univ
  loopless : ∀ (e : E) (u : V), ¬ graph.IsLink e u u
  weight : E → ℝ
  weight_nonneg : ∀ e, 0 ≤ weight e
  colors : E → Finset C
  colors_nonempty : ∀ e, (colors e).Nonempty

variable {V E C : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  [DecidableEq C]

/-- Weighted average degree of the whole input graph; totalized as zero on no vertices. -/
def Model.degree (G : Model V E C) : ℝ :=
  2 * (∑ e, G.weight e) / Fintype.card V

/-- Sum each incident edge once, whenever its full color list contains c. -/
def Model.colorDegree (G : Model V E C) (u : V) (c : C) : ℝ := by
  classical
  exact ∑ e, if G.graph.Inc e u ∧ c ∈ G.colors e then G.weight e else 0

/-- The structural list bound and local weighted color-degree bound, with no density assumption. -/
def Model.Admissible (G : Model V E C) (ell : ℕ) (delta : ℝ) : Prop :=
  (∀ e, (G.colors e).card ≤ ell) ∧ ∀ u c, G.colorDegree u c ≤ delta

/-- Exactly one endpoint in S; no factor two in this boundary mass. -/
def Model.boundaryMass (G : Model V E C) (S : Finset V) : ℝ := by
  classical
  exact ∑ e, if ∃ u ∈ S, ∃ v, v ∉ S ∧ G.graph.IsLink e u v then G.weight e else 0

/-- All colors used by at least one edge; the ambient type C remains arbitrary. -/
def Model.activeColors (G : Model V E C) : Finset C :=
  Finset.univ.biUnion G.colors

end WeightedRainbowCycle.Weighted


