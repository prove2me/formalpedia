-- Prove2me | Definitions.Def_TermCycDich_IsOrderedCrossing
-- name    : TermCycDich_IsOrderedCrossing
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:42:44.446652+00:00
-- url     : https://prove2.me/theorems/f0b7b6b5-c253-4caf-b81f-0c83887da394
-- title:
--   Path crossing $Q_1,\dots,Q_m$ in order
-- statement:
--   For paths $Q_1,\dots,Q_m$ ($m\ge2$) of a graph $G$, a subgraph $P$ is a **$V(Q_1)$–$V(Q_m)$-path meeting $Q_1,\dots,Q_m$ in the given order** if $P$ is a path with one endpoint in $V(Q_1)$ and the other in $V(Q_m)$, internally disjoint from $V(Q_1)\cup V(Q_m)$, and, traversing $P$ from its endpoint in $V(Q_1)$, every vertex of $Q_j$ on $P$ comes before every vertex of $Q_{j'}$ on $P$ whenever $j<j'$.
--
--   This is the condition on each horizontal and each vertical path of a mesh.
--
--   **Formalization Note** The paths are indexed $0,\dots,m-1$ with $m = k+2$. "Internally disjoint from $A \cup B$" follows the paper's definition of an $A$–$B$-path (p.16).
-- source:
--   Bentert–Cavallaro–Wiederrecht, A Dichotomy for Terminal Cyclability, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), Section 2.2, p.17 (PDF 19), definition of meshes; A–B-paths p.16 (PDF 18)

import Mathlib

namespace TermCycDich

/-- `P` is a **`V(Q_0)`–`V(Q_last)`-path of `G` meeting `Q_0, …, Q_{k+1}` in the given order**
(the condition on each path of a mesh).

Bentert–Cavallaro–Wiederrecht, *A Dichotomy for Terminal Cyclability*, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), Section 2.2, p.17 (PDF 19), definition of meshes: "each P_i is a V(Q_1)-V(Q_m)-path
intersecting the paths Q_1, … Q_m in the given order"; Section 2.1, p.16 (PDF 18): "an A-B-path is
a path with one endpoint in A, the other in B, and internally disjoint from A ∪ B".

**Formalization Note** The `k + 2` paths are indexed by `Fin (k + 2)` (0-based: `Q_1` is `Q 0`,
`Q_m` is `Q (Fin.last (k + 1))`). `P` is the subgraph traced by a path walk `p` from `u ∈ V(Q 0)`
to `v ∈ V(Q last)` whose only vertices in `V(Q 0) ∪ V(Q last)` are its ends. "In the given order":
along `p`, every vertex of `Q j` comes strictly before every vertex of `Q j'` whenever `j < j'`
(`p.getVert i` is the vertex at position `i`; positions are unique since `p` is a path). -/
def IsOrderedCrossing {V : Type} {G : SimpleGraph V} (P : G.Subgraph) {k : ℕ}
    (Q : Fin (k + 2) → G.Subgraph) : Prop :=
  ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧ p.toSubgraph = P ∧
    u ∈ (Q 0).verts ∧ v ∈ (Q (Fin.last (k + 1))).verts ∧
    (∀ x ∈ p.support, x ∈ (Q 0).verts ∨ x ∈ (Q (Fin.last (k + 1))).verts → x = u ∨ x = v) ∧
    ∀ j j' : Fin (k + 2), j < j' → ∀ i i' : ℕ, i ≤ p.length → i' ≤ p.length →
      p.getVert i ∈ (Q j).verts → p.getVert i' ∈ (Q j').verts → i < i'

end TermCycDich


