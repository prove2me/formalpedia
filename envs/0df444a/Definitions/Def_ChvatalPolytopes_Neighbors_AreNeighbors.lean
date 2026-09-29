-- Prove2me | Definitions.Def_ChvatalPolytopes_Neighbors_AreNeighbors
-- name    : ChvatalPolytopes_Neighbors_AreNeighbors
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T20:20:51.603542+00:00
-- url     : https://prove2.me/theorems/bcca2577-337a-48c0-84ad-82c018f3ba1d
-- title:
--   Neighbours in the stable set polytope $P(G)$ (§6)
-- statement:
--   Let $G=(V,E)$ be a finite graph and $S(G)$ the set of incidence vectors of its stable sets. For an integer-valued vector $c=(c_u:u\in V)$ and $x\in\mathbb R^V$ write $cx=\sum_{u\in V}c_ux_u$.
--
--   Two vectors $y,z$ are **neighbours in $P(G)$** if there is an integer-valued vector $c$ such that $y$ and $z$ are the only two vectors which maximize $cx$ over $S(G)$; that is, $y\ne z$ and
--   $$\Big\{x\in S(G) : cx'\le cx \text{ for all } x'\in S(G)\Big\}=\{y,z\}.$$
--
--   Geometrically, this says that the segment joining $y$ and $z$ is an edge of the polytope $P(G)=\operatorname{conv}S(G)$; this is the notion of adjacency on which Theorem 6.2 gives a purely graph-theoretic criterion.
--
--   **Formalization Note** This is the definition stated in the first sentence of the proof of Theorem 6.2, not the face-lattice definition of an edge; their equivalence for 0–1 polytopes is not part of the paper. The weight vector is integer-valued (`V → ℤ`), cast to $\mathbb R$ in the sum `intDot c x`. "The only two vectors" is encoded by $y\ne z$ together with the equality of the maximizer set with $\{y,z\}$, which also forces $y,z\in S(G)$.
-- source:
--   Chvátal, On certain polytopes associated with graphs, J. Combin. Theory Ser. B 18 (1975), p. 149, §6, proof of Theorem 6.2 (definition of neighbours in P(G))

import Mathlib
import Definitions.Def_ChvatalPolytopes_Neighbors_StablePolytope

namespace ChvatalPolytopes.Neighbors

/-- The value `cx = Σ (c_u x_u : u ∈ V)` of an integer-valued vector `c` at a real vector `x`. -/
def intDot {V : Type*} [Fintype V] (c : V → ℤ) (x : V → ℝ) : ℝ :=
  ∑ u, (c u : ℝ) * x u

/-- **Neighbours in `P(G)`** (Chvátal 1975, p. 149, first sentence of the proof of Theorem 6.2):
`y` and `z` are neighbours in `P(G)` if and only if there is an integer-valued vector
`c = (c_u : u ∈ V)` such that `y` and `z` are the only two vectors which maximize `cx` over `S(G)`.

"The only two" is spelled out as: `y ≠ z`, and for some `c : V → ℤ` the set of maximizers of
`cx` over `S(G)` is exactly `{y, z}`. -/
def AreNeighbors {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (y z : V → ℝ) : Prop :=
  y ≠ z ∧ ∃ c : V → ℤ,
    {x | x ∈ stableVectors G ∧ ∀ x' ∈ stableVectors G, intDot c x' ≤ intDot c x} = {y, z}

end ChvatalPolytopes.Neighbors


