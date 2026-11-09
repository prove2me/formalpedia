-- Prove2me | Definitions.Def_WeightedRainbowCycle_Weighted_Subgraph
-- name    : WeightedRainbowCycle_Weighted_Subgraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:06:06.833928+00:00
-- url     : https://prove2.me/theorems/fc340aa2-0cd1-470e-916b-70657f6f8d7c
-- title:
--   Inherited weighted subgraphs and logarithmic-density maximality
-- statement:
--   Let $G$ be a weighted list graph. A subgraph $H$ selects vertex and edge subsets $W\subseteq V(G)$ and $F\subseteq E(G)$, with both endpoints of every selected edge in $W$. Weights and lists are inherited, and edges may be deleted. Put
--
--   $$d(H)=\frac{2\sum_{e\in F}w(e)}{|W|},\qquad |\partial_H S|_w=\sum_{e\in F:\ |e\cap S|=1}w(e).$$
--
--   A logarithmic-density maximizer has $|W|\ge2$ and satisfies
--
--   $$\frac{d(K)}{\log|V(K)|}\le\frac{d(H)}{\log|W|}\quad\text{for every subgraph }K\text{ of }G\text{ with }|V(K)|\ge2.$$
--
--   This is the input notion in Lemma 4.1. It ranges over all inherited subgraphs, including edge deletions, rather than assuming a particular induced optimizer or an expansion property.
--
--   **Formalization Note** Empty subgraphs have totalized degree zero. Optimization excludes cardinalities zero and one, where the displayed logarithmic quotient is undefined in ordinary mathematics. Both boundary mass and average degree use the selected edges, with a factor two only in the latter. The model's color labels play no role in maximality; any uncolored finite graph can be given singleton dummy labels.
-- source:
--   Andrew D. Lin, STOC 2027 submission #545 (October 2026), Lemma 4.1, p. 8; proof and induced-subgraph notation, p. 9; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/545.pdf

import Definitions.Def_WeightedRainbowCycle_Weighted_Model

set_option autoImplicit false
noncomputable section

namespace WeightedRainbowCycle.Weighted

variable {V E C : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  [DecidableEq C]

/-- A genuine subgraph, with inherited weights and lists. Edge deletion is permitted. -/
structure Subgraph (G : Model V E C) where
  verts : Finset V
  edges : Finset E
  incident_mem : ∀ e ∈ edges, ∀ u, G.graph.Inc e u → u ∈ verts

/-- Weighted average degree on the selected vertices and edges. -/
def Subgraph.degree {G : Model V E C} (H : Subgraph G) : ℝ :=
  2 * (∑ e ∈ H.edges, G.weight e) / H.verts.card

/-- Weighted edge boundary inside H. -/
def Subgraph.boundaryMass {G : Model V E C} (H : Subgraph G) (S : Finset V) : ℝ := by
  classical
  exact ∑ e ∈ H.edges,
    if ∃ u ∈ S, ∃ v, v ∉ S ∧ G.graph.IsLink e u v then G.weight e else 0

/-- Maximize only over subgraphs on at least two vertices, where log cardinality is positive. -/
def Subgraph.IsDensityMax {G : Model V E C} (H : Subgraph G) : Prop :=
  2 ≤ H.verts.card ∧ ∀ K : Subgraph G, 2 ≤ K.verts.card →
    K.degree / Real.log K.verts.card ≤ H.degree / Real.log H.verts.card

end WeightedRainbowCycle.Weighted


