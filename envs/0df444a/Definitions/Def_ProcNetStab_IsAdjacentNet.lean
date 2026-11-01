-- Prove2me | Definitions.Def_ProcNetStab_IsAdjacentNet
-- name    : ProcNetStab_IsAdjacentNet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:42:10.694174+00:00
-- url     : https://prove2.me/theorems/8cd02ebb-7ac4-4eb8-98f7-73e2f651b2e8
-- title:
--   Adding and removing a link; networks adjacent to the observed network
-- statement:
--   Fix a set $V$ of nodes (agents). A **network** on $V$ is an undirected, unweighted graph without loops; $ij \in h$ means that $i$ and $j$ are linked in $h$. For nodes $i, j$ the network $h + ij$ is $h$ with the link $ij$ added, and $h - ij$ is $h$ with the link $ij$ removed.
--
--   Let $g$ be the observed network. A network $h$ is **adjacent** to $g$ if it differs from $g$ by at most one link:
--   $$
--   h = g, \qquad\text{or}\qquad h = g + ij \text{ for some } ij \notin g, \qquad\text{or}\qquad h = g - ij \text{ for some } ij \in g .
--   $$
--
--   Adjacency to the observed network is the domain on which the paper's similarity relation $\simeq_k$ imposes restrictions on preferences.
--
--   **Formalization Note** Networks are `SimpleGraph V`. $h + ij$ is `h ⊔ SimpleGraph.edge i j` (`addLink`), which equals $h$ when $i = j$ or $ij \in h$. $h - ij$ is edge deletion `h.deleteEdges {s(i, j)}` (`delLink`), which equals $h$ when $ij \notin h$. A non-link $ij \notin g$ is a pair of distinct nodes that are not linked.
-- source:
--   Chiong, Qi, Stability of Procurement Networks (authors' manuscript, 2025), §3.1, p.6 (g + ij, g − ij); p.10 after Definition 3.8 and p.OA-1 (adjacent networks)

import Mathlib

namespace ProcNetStab

/-- The network `h + ij` obtained by adding the link between `i` and `j` (Chiong, Qi, *Stability
of Procurement Networks* (authors' manuscript, 2025), §3.1, p.6).

**Formalization Note** Networks on the node set `V` are `SimpleGraph V`; `h + ij` is
`h ⊔ SimpleGraph.edge i j`, which is `h` itself when `i = j` or `ij ∈ h`. -/
def addLink {V : Type*} (h : SimpleGraph V) (i j : V) : SimpleGraph V :=
  h ⊔ SimpleGraph.edge i j

/-- The network `h − ij` obtained by removing the link between `i` and `j` (Chiong, Qi, *Stability
of Procurement Networks* (authors' manuscript, 2025), §3.1, p.6).

**Formalization Note** `h − ij` is edge deletion `h.deleteEdges {s(i, j)}`; it is a no-op when
`ij ∉ h` (in particular when `i = j`). This is the literal reading of the notation, used in
Definitions 3.1, 3.9 and A.2 for all nodes `j`. -/
def delLink {V : Type*} (h : SimpleGraph V) (i j : V) : SimpleGraph V :=
  h.deleteEdges {s(i, j)}

/-- **Adjacent networks** (Chiong, Qi, *Stability of Procurement Networks* (authors' manuscript,
2025), p.10 after Definition 3.8, and p.OA-1): `h` is adjacent to the observed network `g` if
`h = g`, or `h = g + ij` for some non-link `ij ∉ g`, or `h = g − ij` for some link `ij ∈ g`.

**Formalization Note** A non-link is a pair of distinct nodes `i ≠ j` with `¬ g.Adj i j`. -/
def IsAdjacentNet {V : Type*} (g h : SimpleGraph V) : Prop :=
  h = g ∨ (∃ i j : V, i ≠ j ∧ ¬ g.Adj i j ∧ h = addLink g i j) ∨
    (∃ i j : V, g.Adj i j ∧ h = delLink g i j)

end ProcNetStab


