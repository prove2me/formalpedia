-- Prove2me | Definitions.Def_MVBlossoms_IsEvenLevelPath
-- name    : MVBlossoms_IsEvenLevelPath
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:39:04.609215+00:00
-- url     : https://prove2.me/theorems/42d65af4-c5cd-402c-b5f8-5d78b7147a85
-- title:
--   Even level($v$) path
-- statement:
--   An **even level($v$) path** is an alternating path from an unmatched vertex $f$ to $v$ whose length is even and equals $\mathrm{even\ level}(v)$, i.e. a shortest even-length alternating path to $v$ from any unmatched vertex.
--
--   These paths are the objects of Theorems 2 and 3: the paper studies how shortest alternating paths of each parity pass through other vertices.
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Definition 4, p.2016

import Mathlib
import Definitions.Def_MVBlossoms_IsAltPathFromUnmatched
import Definitions.Def_MVBlossoms_evenLevel

namespace MVBlossoms

/-- **Even level(v) path.** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Definition 4, p.2016: "each such path
[a minimum even-length alternating path from an unmatched vertex to v] will be called an
even level(v) path."

`IsEvenLevelPath M p` for `p : G.Walk f v`: `p` is an alternating path from the unmatched vertex
`f`, its length is even, and its length equals `evenLevel M v`. -/
def IsEvenLevelPath {V : Type} {G : SimpleGraph V} (M : G.Subgraph) {f v : V} (p : G.Walk f v) : Prop :=
  IsAltPathFromUnmatched M p ∧ Even p.length ∧ (p.length : ℕ∞) = evenLevel M v

end MVBlossoms


