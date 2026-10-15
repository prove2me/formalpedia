-- Prove2me | Definitions.Def_DirectedSearch_Approx_Graphs
-- name    : DirectedSearch_Approx_Graphs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T09:03:31.692111+00:00
-- url     : https://prove2.me/theorems/48b961b4-9cad-4548-9535-ada104ba6c44
-- title:
--   Lemmas 4.6–4.7 — the support graph of β on Θ, unions of vertex-disjoint stars, edge weight
-- statement:
--   Let $\Theta=\mathcal M\sqcup\mathcal W$ be the set of types. For a matrix $\beta=(\beta_{mw})$, the **support graph** of $\beta$ is the bipartite simple graph on $\Theta$ with an edge $\{m,w\}$ exactly when $\beta_{mw}>0$.
--
--   A graph $H$ is a **union of vertex-disjoint star graphs** (trees of radius 1) when every edge of $H$ has an endpoint of degree 1 in $H$. For a graph $G$ on a finite vertex set and an edge weight $\mathrm{wt}$, its **weight** is
--   $$\mathrm{wt}(G)=\sum_{e\in E(G)}\mathrm{wt}(e).$$
--
--   The support graph carries the forest structure of Lemma 4.6; star forests and weights carry the halving step of Lemma 4.7.
--
--   **Formalization Note.** "Every edge has an endpoint of degree 1" is equivalent to "every component is a star $K_{1,k}$ or an isolated vertex": no path with three edges and no cycle can occur, since the middle edge of such a path, and every edge of a cycle, has both endpoints of degree at least 2. Degrees and edge sets use classical decidability.
-- source:
--   Immorlica, Lucier, Manshadi, Wei, Designing Approximately Optimal Search on Matching Platforms, arXiv:2102.09017v2, p. 23, Lemma 4.6 (graph on Θ with edge set {(m,w) : β*_mw > 0}), Lemma 4.7 (union of vertex-disjoint star graphs)

import Mathlib

namespace DirectedSearch.Approx

open Classical

/-- The support graph of `β` on the type set `Θ = M ⊕ W` (Lemma 4.6, p. 23): an edge joins
`m` and `w` exactly when `β_mw > 0` (`fromRel` symmetrises the relation); there are no
edges inside one side. -/
def supportGraph {M W : Type} (β : M → W → ℝ) : SimpleGraph (M ⊕ W) :=
  SimpleGraph.fromRel fun x y => ∃ m w, x = Sum.inl m ∧ y = Sum.inr w ∧ 0 < β m w

/-- A union of vertex-disjoint star graphs (trees of radius 1) (Lemma 4.7, p. 23): every edge
of `H` has an endpoint of degree 1 in `H`. -/
noncomputable def IsStarForest {V : Type} [Fintype V] (H : SimpleGraph V) : Prop :=
  ∀ u v, H.Adj u v → H.degree u = 1 ∨ H.degree v = 1

/-- The total edge weight `Σ_{e ∈ E(G)} wt(e)` of a graph on a finite vertex set. -/
noncomputable def graphWeight {V : Type} [Fintype V] (G : SimpleGraph V) (wt : Sym2 V → ℝ) : ℝ :=
  ∑ e ∈ G.edgeFinset, wt e

end DirectedSearch.Approx


