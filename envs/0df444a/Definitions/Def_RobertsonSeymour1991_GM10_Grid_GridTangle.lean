-- Prove2me | Definitions.Def_RobertsonSeymour1991_GM10_Grid_GridTangle
-- name    : RobertsonSeymour1991_GM10_Grid_GridTangle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:10:57.999893+00:00
-- url     : https://prove2.me/theorems/a30eee09-0c05-4c75-96f5-9dd500808dab
-- title:
--   §7, p. 173 — selected grid separations
-- statement:
--   Let $G$ be the $\theta$-grid. The **grid tangle candidate** is the set of separations whose order is less than $\theta$ and whose first side has a small edge set:
--
--   $$\mathcal T_\theta=\{(A,B):\text{$(A,B)$ separates $G$},\ |V(A\cap B)|<\theta,\ E(A)\text{ is small}\}.$$
--
--   Result (7.3) asserts that this selected set satisfies all three tangle axioms.
--
--   **Formalization Note** The grid is represented by the published simple graph's vertex and edge types through the local hypergraph incidence relation. Separation and order use the paper's subhypergraph definitions; the selected side is the first component $A$.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), p. 173, §7, paragraph before (7.3)

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_Grid_Tangle
import Definitions.Def_RobertsonSeymour1991_GM10_Grid_Small

namespace RobertsonSeymour1991.GM10.Grid

/-- §7, p. 173: the separations of the θ-grid of order below θ whose first side has a small
edge set. -/
def gridTangle (θ : ℕ) : Set ((gridHypergraph θ).Sub × (gridHypergraph θ).Sub) :=
  {p | Hypergraph.IsSeparation p.1 p.2 ∧ Hypergraph.order p.1 p.2 < θ ∧ IsSmall θ p.1.edges}

end RobertsonSeymour1991.GM10.Grid


