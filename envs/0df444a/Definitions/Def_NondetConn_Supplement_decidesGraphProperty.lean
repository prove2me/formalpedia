-- Prove2me | Definitions.Def_NondetConn_Supplement_decidesGraphProperty
-- name    : NondetConn_Supplement_decidesGraphProperty
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T04:10:01.383825+00:00
-- url     : https://prove2.me/theorems/6e0d9928-612b-4d40-a5b9-7bb83047972a
-- title:
--   Five split-edge graph decision problems
-- statement:
--   Alice and Bob receive disjoint edge sets of an undirected graph on `Fin N`; equivalently they receive simple graphs $G_A,G_B$, and the input graph is $G_A\cup G_B$. According to the selected clause, the output says whether this union is bipartite, cycle-free, Eulerian, Hamiltonian, or planar.
--
--   Planarity means the existence of a crossing-free drawing by simple arcs in $\mathbb R^2$.
-- source:
--   Zhang, Settling Nondeterministic Communication Complexity of Graph Connectivity, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), Theorem 6.2, p.21 (PDF p.23), and proof, p.26 (PDF p.28)

import Definitions.Def_NondetConn_Supplement_GraphProperty
import Definitions.Def_NondetConn_Supplement_isEulerian
import Definitions.Def_RobertsonSeymour1986_GM5_IsPlanar

set_option autoImplicit false

namespace NondetConn.Supplement

/-- On a split-edge input `(G_A,G_B)`, decide one of the five properties of the union graph.
The communication theorems separately impose `Disjoint G_A G_B`, matching the paper's
edge-partition model. -/
noncomputable def decidesGraphProperty (property : GraphProperty) (N : ℕ)
    (GA GB : SimpleGraph (Fin N)) : Bool := by
  classical
  exact match property with
    | .bipartite => decide ((GA ⊔ GB).IsBipartite)
    | .cycleFree => decide ((GA ⊔ GB).IsAcyclic)
    | .eulerian => decide (isEulerian (GA ⊔ GB))
    | .hamiltonian => decide ((GA ⊔ GB).IsHamiltonian)
    | .planar => decide (RobertsonSeymour1986.GM5.IsPlanar (GA ⊔ GB))

end NondetConn.Supplement


