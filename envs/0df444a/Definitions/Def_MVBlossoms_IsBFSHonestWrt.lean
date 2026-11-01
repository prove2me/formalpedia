-- Prove2me | Definitions.Def_MVBlossoms_IsBFSHonestWrt
-- name    : MVBlossoms_IsBFSHonestWrt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:41:00.320788+00:00
-- url     : https://prove2.me/theorems/901e7273-863c-464a-9e45-8a86b2023e14
-- title:
--   BFS honesty with respect to a base
-- statement:
--   Let $p$ be a path, $u$ a vertex on $p$, and $b$ a base (or iterated base) of $u$. The vertex $u$ is **BFS honest on $p$ with respect to $b$** if $p[b\text{ to }u]$ is an even level($b;u$) path when its length is even and an odd level($b;u$) path when its length is odd. The base $b$ may come before or after $u$ on $p$.
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Definitions 24 and 33, pp.2032, 2038

import Mathlib
import Definitions.Def_MVBlossoms_IsEvenLevelFromPath
import Definitions.Def_MVBlossoms_IsOddLevelFromPath
import Definitions.Def_MVBlossoms_IsSegmentFrom

namespace MVBlossoms

/-- **BFS honesty on p with respect to a (iterated) base.** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Definitions 24
(p.2032) and 33 (p.2038): "we will say that u is BFS honest on p w.r.t. b if p[b to u] is an even
level(b;u) (odd level(b;u)) path assuming that |p[b to u]| is even (odd). Note that we are allowing
b to appear either before or after u on path p."

`IsBFSHonestWrt M p u b`: the segment `q = p[b to u]` of `p`, read from `b`, is an even level(b;u)
path if its length is even and an odd level(b;u) path if its length is odd.

**Formalization Note.** The existential over `q` also asserts that `b` and `u` lie on `p`; on a
simple path the segment is unique. -/
def IsBFSHonestWrt {V : Type} {G : SimpleGraph V} (M : G.Subgraph) {f v : V} (p : G.Walk f v) (u b : V) : Prop :=
  ∃ q : G.Walk b u, IsSegmentFrom p q ∧ (Even q.length → IsEvenLevelFromPath M q) ∧
    (Odd q.length → IsOddLevelFromPath M q)

end MVBlossoms


