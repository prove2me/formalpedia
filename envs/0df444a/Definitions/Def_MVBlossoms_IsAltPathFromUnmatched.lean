-- Prove2me | Definitions.Def_MVBlossoms_IsAltPathFromUnmatched
-- name    : MVBlossoms_IsAltPathFromUnmatched
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:37:14.012168+00:00
-- url     : https://prove2.me/theorems/e2f8b40c-08ab-4b39-a51b-1107f28af865
-- title:
--   Alternating path from an unmatched vertex
-- statement:
--   Let $G=(V,E)$ be a graph and $M$ a matching of $G$. A vertex is **unmatched** if no edge of $M$ is incident to it. An **alternating path** is a simple path whose edges alternate between $M$ and $E\setminus M$.
--
--   For a walk $p$ from $f$ to $v$, the predicate holds when $f$ is unmatched, $p$ is a simple path (no repeated vertex), and any two consecutive edges of $p$ consist of one matched and one unmatched edge. The path of length $0$ at an unmatched vertex qualifies.
--
--   All level notions of the paper (even and odd levels, tenacity, $l_m$) are minima over these paths.
--
--   **Formalization Note** "Unmatched" and "alternating" reuse the published predicates `BergeMatching.Core.IsNeutral` and `BergeMatching.Core.IsAlternatingWrt`; simplicity is `Walk.IsPath`.
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), §3.1 and Definition 4, p.2016

import Mathlib
import Definitions.Def_BergeMatching_Core_AlternatingChain

namespace MVBlossoms

/-- **Alternating path from an unmatched vertex.** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), §3.1, p.2016:
"An alternating path is a simple path whose edges alternate between M and E − M (i.e., matched and
unmatched)", and Definition 4, p.2016 ("alternating path from an unmatched vertex to v").

`IsAltPathFromUnmatched M p` holds for `p : G.Walk f v` when `f` is unmatched (no edge of `M`
contains `f`), `p` is a simple path, and consecutive edges of `p` alternate between `M` and
`E − M`. The length-0 path at an unmatched `f` qualifies.

**Formalization Note.** "Unmatched" is `BergeMatching.Core.IsNeutral M f` and alternation is
`BergeMatching.Core.IsAlternatingWrt M.edgeSet p` (trail + alternation of consecutive edges), both
from the published definition `BergeMatching_Core_AlternatingChain`; simplicity is `p.IsPath`.
Since `f` is unmatched, the first edge of a nontrivial such path is automatically unmatched. -/
def IsAltPathFromUnmatched {V : Type} {G : SimpleGraph V} (M : G.Subgraph) {f v : V}
    (p : G.Walk f v) : Prop :=
  BergeMatching.Core.IsNeutral M f ∧ p.IsPath ∧ BergeMatching.Core.IsAlternatingWrt M.edgeSet p

end MVBlossoms


