-- Prove2me | Definitions.Def_OfflineStochMatching_UnitPatience_starWeight
-- name    : OfflineStochMatching_UnitPatience_starWeight
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:33:55.830353+00:00
-- url     : https://prove2.me/theorems/fd863929-3797-4ec6-83d1-f8824cc4a57b
-- title:
--   Weight $W(v)$ matched at a vertex of $V_2$
-- statement:
--   For a vertex $v$, $W(v)$ is the weight $w_e$ of the edge $e$ matched at $v$ by the algorithm of Section 4 (given the probing order, the rounded vector $Y$ and the realization $P$), and $0$ if $v$ is unmatched.
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3, §4, p. 16 (W(v) denotes the weight of the edge matched by the algorithm (if any) for a vertex v)

import Mathlib
import Definitions.Def_OfflineStochMatching_UnitPatience_StochGraph
import Definitions.Def_OfflineStochMatching_UnitPatience_algMatch

namespace OfflineStochMatching.UnitPatience

/-- **The weight `W(v)` matched at a vertex of `V2`.**
Brubach, Grammel, Ma, MacRury, Srinivasan, *Improved Guarantees for Offline Stochastic Matching via
New Ordered Contention Resolution Schemes*, arXiv:2106.06892v3, §4, p. 16: "where `W(v)` denotes
the weight of the edge matched by the algorithm (if any) for a vertex `v`."

`starWeight G σ Y P v` is `w_e` for the edge `e = algMatch σ Y P v` matched at `v`, and `0` if
no edge is matched there. -/
def starWeight {V E : Type*} (G : StochGraph V E) (σ : V → List E) (Y P : E → Bool) (v : V) :
    ℝ :=
  match algMatch σ Y P v with
  | some e => G.w e
  | none => 0

end OfflineStochMatching.UnitPatience


