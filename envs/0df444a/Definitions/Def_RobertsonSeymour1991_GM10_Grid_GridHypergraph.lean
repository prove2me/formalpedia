-- Prove2me | Definitions.Def_RobertsonSeymour1991_GM10_Grid_GridHypergraph
-- name    : RobertsonSeymour1991_GM10_Grid_GridHypergraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T14:44:42.385184+00:00
-- url     : https://prove2.me/theorems/7a363b0f-95df-4366-aaaa-2dcac751acbe
-- title:
--   §7, p. 171 — grid as a hypergraph, rows, columns and edge boundary
-- statement:
--   The **$\theta$-grid** has vertices $(i,j)$ with $1\le i,j\le\theta$ and an edge between two vertices when their Manhattan distance is one. In the hypergraph view, these same edges are incident with their two endpoints. For each $i$, $E(P_i)$ is the set of horizontal edges in row $i$; for each $j$, $E(Q_j)$ is the set of vertical edges in column $j$.
--
--   For an edge set $X\subseteq E(G)$, its **edge boundary** is
--
--   $$\partial(X)=\{v\in V(G):\text{$v$ is incident with an edge in $X$ and an edge in $E(G)\setminus X$}\}.$$
--
--   The boundary and row and column edge sets are the data in (7.1), (7.2) and (7.3).
--
--   **Formalization Note** The already published grid definition is reused, with its $0$-based vertices in $\mathrm{Fin}(\theta)\times\mathrm{Fin}(\theta)$; these correspond to the paper's $1$-based indices by subtracting one. Its edge type is the simple graph's edge set. The paper's phrase “vertices $v\in X$” in the boundary definition has a type slip because $X$ is an edge set; incidence determines the intended vertex set. The grid is finite.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), p. 171, §7, grid, Pᵢ, Qⱼ and ∂(X)

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_grid
import Definitions.Def_RobertsonSeymour1991_GM10_Grid_Hypergraph

namespace RobertsonSeymour1991.GM10.Grid

/-- §7, p. 171: the θ-grid as a hypergraph (a graph): its edges are the edges of `GM5.grid θ`,
and an edge is incident with its two ends. -/
def gridHypergraph (θ : ℕ) :
    Hypergraph (Fin θ × Fin θ) (RobertsonSeymour1986.GM5.grid θ).edgeSet where
  inc e v := v ∈ (e : Sym2 (Fin θ × Fin θ))

/-- `E(Pᵢ)`: the edges with both ends in row `i`. -/
def rowEdges (θ : ℕ) (i : Fin θ) : Set (RobertsonSeymour1986.GM5.grid θ).edgeSet :=
  {e | ∀ v ∈ (e : Sym2 (Fin θ × Fin θ)), v.1 = i}

/-- `E(Qⱼ)`: the edges with both ends in column `j`. -/
def colEdges (θ : ℕ) (j : Fin θ) : Set (RobertsonSeymour1986.GM5.grid θ).edgeSet :=
  {e | ∀ v ∈ (e : Sym2 (Fin θ × Fin θ)), v.2 = j}

/-- `∂(X)`: the vertices incident with an edge in `X` and with an edge not in `X`. -/
def boundary (θ : ℕ) (X : Set (RobertsonSeymour1986.GM5.grid θ).edgeSet) : Set (Fin θ × Fin θ) :=
  {v | ∃ e ∈ X, (gridHypergraph θ).inc e v ∧ ∃ e' ∉ X, (gridHypergraph θ).inc e' v}

end RobertsonSeymour1991.GM10.Grid


