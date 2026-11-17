-- Prove2me | Definitions.Def_LovaszECCKernel_Supplement_IsCompleteBipartite
-- name    : LovaszECCKernel_Supplement_IsCompleteBipartite
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:09:35.88221+00:00
-- url     : https://prove2.me/theorems/b0c45597-d066-42a5-bdf9-1dd7eefc42e2
-- title:
--   Complete bipartite graphs (either side may be empty)
-- statement:
--   A graph $H$ on vertex set $V$ is **complete bipartite** if there is a partition $V=X\cup(V\setminus X)$ (either part may be empty) such that two vertices are adjacent exactly when they lie in different parts. This is the paper's complete $r$-partite graph for $r=2$: every edge joins the two parts, and every pair of vertices from different parts is an edge.
--
--   It is the extremal structure of the Erdős–Goodman–Pósa bound: the balanced complete bipartite graph $K_{\lfloor n/2\rfloor,\lceil n/2\rceil}$ attains $\mathrm{ecp}=\lfloor n^2/4\rfloor$, and the stability theorem says that graphs close to this bound are few edits away from a complete bipartite graph.
--
--   **Formalization Note** One part is a set $X\subseteq V$ and the other its complement. Because a part may be empty, every edgeless graph is complete bipartite (take $X=V$).
-- source:
--   Fomin, Golovach, Khargeliia, Sagunov, Simonov, Stability Meets Kernelization: Algorithmic Extensions of the Lovász and Erdős–Goodman–Pósa Theorems, STOC 2027 submission (manuscript sha256 a9d53ab8…), §2, p.15 (= PDF p.15), complete r-partite graphs with r = 2

import Mathlib

set_option autoImplicit false

namespace LovaszECCKernel.Supplement

/-- `H` is **complete bipartite** (Fomin, Golovach, Khargeliia, Sagunov, Simonov, *Stability Meets
Kernelization: Algorithmic Extensions of the Lovász and Erdős–Goodman–Pósa Theorems*, STOC 2027
submission (manuscript sha256 a9d53ab8…), §2, p.15 (= PDF p.15), with `r = 2`): "a graph G is an
r-partite if there is a partition {V1, . . . , Vr} of V (G) (some sets may be empty) such that the
endpoints of each edge are in distinct sets of the partition … A graph is a complete r-partite if for
every distinct i, j ∈ [r], and every u ∈ Vi and v ∈ Vj, uv ∈ E(G)."

**Formalization Note** The two parts are `X` and its complement; two vertices are adjacent iff they
lie on different sides. Either side may be empty (as the paper allows), so the edgeless graph on at
most one vertex, and every edgeless graph with `X = V`, count as complete bipartite. -/
def IsCompleteBipartite {V : Type*} (H : SimpleGraph V) : Prop :=
  ∃ X : Set V, ∀ u v : V, H.Adj u v ↔ (u ∈ X ↔ v ∉ X)

end LovaszECCKernel.Supplement


