-- Prove2me | Definitions.Def_MVBlossoms_IsOddLevelPath
-- name    : MVBlossoms_IsOddLevelPath
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:39:31.105436+00:00
-- url     : https://prove2.me/theorems/e91027ca-f7f0-43b9-ad3c-9d3e3a162869
-- title:
--   Odd level($v$) path
-- statement:
--   An **odd level($v$) path** is an alternating path from an unmatched vertex $f$ to $v$ whose length is odd and equals $\mathrm{odd\ level}(v)$, i.e. a shortest odd-length alternating path to $v$ from any unmatched vertex.
--
--   These paths are the objects of Theorems 2 and 3: the paper studies how shortest alternating paths of each parity pass through other vertices.
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Definition 4, p.2016

import Mathlib
import Definitions.Def_MVBlossoms_IsAltPathFromUnmatched
import Definitions.Def_MVBlossoms_oddLevel

namespace MVBlossoms

/-- **Odd level(v) path.** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Definition 4, p.2016: "each such path
[a minimum odd-length alternating path from an unmatched vertex to v] will be called an
odd level(v) path."

`IsOddLevelPath M p` for `p : G.Walk f v`: `p` is an alternating path from the unmatched vertex
`f`, its length is odd, and its length equals `oddLevel M v`. -/
def IsOddLevelPath {V : Type} {G : SimpleGraph V} (M : G.Subgraph) {f v : V} (p : G.Walk f v) : Prop :=
  IsAltPathFromUnmatched M p ∧ Odd p.length ∧ (p.length : ℕ∞) = oddLevel M v

end MVBlossoms


