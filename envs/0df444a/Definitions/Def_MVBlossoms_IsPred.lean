-- Prove2me | Definitions.Def_MVBlossoms_IsPred
-- name    : MVBlossoms_IsPred
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:41:16.622376+00:00
-- url     : https://prove2.me/theorems/ad23ecba-627a-4a83-be79-c78f34754905
-- title:
--   Predecessor
-- statement:
--   Let $(u,v)$ be an edge. The vertex $u$ is a **predecessor** of $v$ if some min level($v$) path has $(u,v)$ as its last edge.
--
--   If $v$ is outer the last edge is matched (the predecessor is the matched neighbour of $v$); otherwise it is unmatched.
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Definition 10, p.2018

import Mathlib
import Definitions.Def_MVBlossoms_IsMinLevelPath

namespace MVBlossoms

/-- **Predecessor.** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Definition 10, p.2018: "Consider a min level(v) path, and let
(u, v) be the last edge on it; ... we will say that u is a predecessor of v and that edge (u, v)
is a prop."

`IsPred M u v`: some min level(v) path ends with the edge `(u, v)`, i.e. it is `q.concat h` for a
walk `q` to `u` and `h : G.Adj u v`. -/
def IsPred {V : Type} {G : SimpleGraph V} (M : G.Subgraph) (u v : V) : Prop :=
  ∃ (f : V) (q : G.Walk f u) (h : G.Adj u v), IsMinLevelPath M (q.concat h)

end MVBlossoms


