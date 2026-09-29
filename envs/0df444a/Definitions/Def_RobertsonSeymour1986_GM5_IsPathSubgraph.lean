-- Prove2me | Definitions.Def_RobertsonSeymour1986_GM5_IsPathSubgraph
-- name    : RobertsonSeymour1986_GM5_IsPathSubgraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:54:45.178971+00:00
-- url     : https://prove2.me/theorems/c69ab8ae-8a24-4dca-8246-1e43cc8af192
-- title:
--   Path (as a subgraph)
-- statement:
--   A **path** in $G$ is a subgraph formed by a walk $u=x_0,x_1,\dots,x_\ell=v$ with no repeated vertex, where $u$ is the path's **initial vertex** and $v$ its **terminal vertex**. A path has at least one vertex; a single vertex ($\ell=0$) is a path.
--
--   **Formalization Note** A subgraph $P$ of $G$ is a path when $P$ equals the subgraph traced by some walk of $G$ that repeats no vertex.
-- source:
--   Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986), Sect. 1, p. 94 (PDF p. 3), terminology paragraph; DOI 10.1016/0095-8956(86)90030-4

import Mathlib

namespace RobertsonSeymour1986.GM5

/-- `IsPathSubgraph P`: the subgraph `P` of `G` is a path.

Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986),
Sect. 1, p. 94 (PDF p. 3), unnumbered: "A *path* has at least one vertex, and has no "repeated"
vertices. Every path has an *initial vertex* and a *terminal vertex*."

**Formalization Note** `P` is the subgraph traced by a walk `p` of `G` from `u` (initial vertex) to
`v` (terminal vertex) with no repeated vertex (`Walk.IsPath`). A single vertex (`Walk.nil`) is a
path, as in the paper. -/
def IsPathSubgraph {V : Type} {G : SimpleGraph V} (P : G.Subgraph) : Prop :=
  ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧ p.toSubgraph = P

end RobertsonSeymour1986.GM5


