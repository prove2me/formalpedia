-- Prove2me | Definitions.Def_MVBlossoms_IsAltPathFromBase
-- name    : MVBlossoms_IsAltPathFromBase
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:37:16.151675+00:00
-- url     : https://prove2.me/theorems/6b226416-21f9-42af-b5b1-be68af4c78fd
-- title:
--   Alternating path starting with an unmatched edge
-- statement:
--   For vertices $b$ and $v$, the predicate holds for a walk from $b$ to $v$ that is a simple alternating path whose first edge exists and is unmatched.
--
--   These are the paths from a base into its blossom (Definitions 23 and 32).
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Definitions 23 and 32, pp.2031, 2037

import Mathlib
import Definitions.Def_BergeMatching_Core_AlternatingChain

namespace MVBlossoms

/-- **Alternating path from a base starting with an unmatched edge.** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024),
Definitions 23 (p.2031) and 32 (p.2037): "an alternating path in G from b to v that starts with an
unmatched edge".

`IsAltPathFromBase M q` for `q : G.Walk b v`: `q` is a simple path, its consecutive edges
alternate between `M` and `E − M`, and its first edge exists and is unmatched. -/
def IsAltPathFromBase {V : Type} {G : SimpleGraph V} (M : G.Subgraph) {b v : V} (q : G.Walk b v) : Prop :=
  q.IsPath ∧ BergeMatching.Core.IsAlternatingWrt M.edgeSet q ∧
    ∃ e, q.edges.head? = some e ∧ e ∉ M.edgeSet

end MVBlossoms


