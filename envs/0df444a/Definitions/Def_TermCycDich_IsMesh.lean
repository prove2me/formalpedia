-- Prove2me | Definitions.Def_TermCycDich_IsMesh
-- name    : TermCycDich_IsMesh
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:43:41.884988+00:00
-- url     : https://prove2.me/theorems/1a23a2c0-b832-4b59-822e-a65e25d549c5
-- title:
--   $(n\times m)$-mesh
-- statement:
--   Let $n,m\ge2$. Paths $P_1,\dots,P_n$ and $Q_1,\dots,Q_m$ of a graph $G$ form an **$(n\times m)$-mesh** $M=P_1\cup\dots\cup P_n\cup Q_1\cup\dots\cup Q_m$ if
--
--   1. $P_1,\dots,P_n$ are pairwise vertex-disjoint, and $Q_1,\dots,Q_m$ are pairwise vertex-disjoint;
--   2. for all $i,j$, the intersection $P_i\cap Q_j$ is a path;
--   3. each $P_i$ is a $V(Q_1)$–$V(Q_m)$-path meeting $Q_1,\dots,Q_m$ in the given order, and each $Q_j$ is a $V(P_1)$–$V(P_n)$-path meeting $P_1,\dots,P_n$ in the given order.
--
--   The $P_i$ are the horizontal and the $Q_j$ the vertical paths. Lemma 3.10 reroutes a solution inside a $(4\times3)$-mesh.
--
--   **Formalization Note** The sizes are written $n+2$, $m+2$ and indices are 0-based. Paths are subgraphs traced by path walks (public `RobertsonSeymour1986.GM5.IsPathSubgraph`). "$P_i\cap Q_j$ induces a path" is read as: the common subgraph of $P_i$ and $Q_j$ (common vertices, common edges) is a path, in particular nonempty. The mesh is the union subgraph.
-- source:
--   Bentert–Cavallaro–Wiederrecht, A Dichotomy for Terminal Cyclability, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), Section 2.2, p.17 (PDF 19)

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_IsPathSubgraph
import Definitions.Def_TermCycDich_IsOrderedCrossing

namespace TermCycDich

/-- The paths `P_1, …, P_{n+2}` (horizontal) and `Q_1, …, Q_{m+2}` (vertical) of `G` form an
**`((n+2) × (m+2))`-mesh** `M = P_1 ∪ … ∪ Q_{m+2}`.

Bentert–Cavallaro–Wiederrecht, *A Dichotomy for Terminal Cyclability*, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), Section 2.2, p.17 (PDF 19): "Let n, m be integers with n, m ≥ 2. A (n × m)-mesh is a graph
M which is the union of paths M = P_1 ∪ . . . ∪ P_n ∪ Q_1 ∪ . . . ∪ Q_m where
• P_1, . . . , P_n are pairwise vertex-disjoint, and Q_1, . . . , Q_m are pairwise vertex-disjoint.
• for every i ∈ [n] and j ∈ [m], the intersection P_i ∩ Q_j induces a path,
• each P_i is a V(Q_1)-V(Q_m)-path intersecting the paths Q_1, . . . Q_m in the given order, and
each Q_j is a V(P_1)-V(P_n)-path intersecting the paths P_1, . . . , P_n in the given order."

**Formalization Note** The sizes are written `n + 2`, `m + 2` (so `≥ 2` is built in) and indices
are 0-based. Paths are subgraphs of `G` (`G.Subgraph`) traced by path walks (public
`RobertsonSeymour1986.GM5.IsPathSubgraph`, used for `P_i ∩ Q_j`; the ordered-crossing condition
`IsOrderedCrossing` makes each `P_i`, `Q_j` itself a path). "`P_i ∩ Q_j` induces a path" is read
as: the common subgraph `P i ⊓ Q j` (common vertices and common edges) is a path, in particular
nonempty. The mesh itself is the subgraph `(⨆ i, P i) ⊔ (⨆ j, Q j)`. -/
def IsMesh {V : Type} {G : SimpleGraph V} {n m : ℕ} (P : Fin (n + 2) → G.Subgraph)
    (Q : Fin (m + 2) → G.Subgraph) : Prop :=
  Pairwise (fun i i' => Disjoint (P i).verts (P i').verts) ∧
    Pairwise (fun j j' => Disjoint (Q j).verts (Q j').verts) ∧
    (∀ i j, RobertsonSeymour1986.GM5.IsPathSubgraph (P i ⊓ Q j)) ∧
    (∀ i, IsOrderedCrossing (P i) Q) ∧
    ∀ j, IsOrderedCrossing (Q j) P

end TermCycDich


