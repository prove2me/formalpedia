-- Prove2me | Definitions.Def_SteinerCutDominants_WSG_wt
-- name    : SteinerCutDominants_WSG_wt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:15:25.27139+00:00
-- url     : https://prove2.me/theorems/0de4950e-90c3-4a23-9479-f885054b7ef5
-- title:
--   Pair weight of a weighted Steiner graph
-- statement:
--   The weight $c(xy)$ of the pair $x,y$ in a weighted Steiner graph, equal to $0$ when $xy$ is not an edge.
-- source:
--   Conforti, Kaibel, Steiner Cut Dominants, arXiv:2209.14802v2, (auxiliary; no counterpart in the paper)

import Mathlib
import Definitions.Def_SteinerCutDominants_WSG
import Definitions.Def_SteinerCutDominants_edgeVal

namespace SteinerCutDominants

/-- The weight `c(xy)` of the pair `x, y`, with value `0` when `xy` is not an edge. -/
def WSG.wt (H : WSG) (x y : H.V) : ℕ := edgeVal H.G H.c x y

end SteinerCutDominants


