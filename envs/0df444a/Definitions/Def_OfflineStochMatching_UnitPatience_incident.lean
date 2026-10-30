-- Prove2me | Definitions.Def_OfflineStochMatching_UnitPatience_incident
-- name    : OfflineStochMatching_UnitPatience_incident
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:29:56.937827+00:00
-- url     : https://prove2.me/theorems/893d20c9-c952-4bce-8fdb-eff4d51fe72f
-- title:
--   Edges $\delta(x)$ incident to a vertex
-- statement:
--   For a vertex $x$ of the stochastic graph $G$, $\delta(x)$ is the set of edges having $x$ as one of their two endpoints. It indexes the matching and patience constraints (3a), (3b) of the LP relaxation and the star of a vertex $v$ in the algorithm of Section 4.
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3, §2, p. 7 (δ(v), the set of edges incident to v)

import Mathlib
import Definitions.Def_OfflineStochMatching_UnitPatience_StochGraph

namespace OfflineStochMatching.UnitPatience

/-- **The edges `δ(x)` incident to a vertex.**
Brubach, Grammel, Ma, MacRury, Srinivasan, *Improved Guarantees for Offline Stochastic Matching via
New Ordered Contention Resolution Schemes*, arXiv:2106.06892v3, §2, p. 7: "we have let `δ(v)`
denote the set of edges incident to a vertex `v`."

`incident G x` is the finite set of edges with `x` as one of their two endpoints. -/
def incident {V E : Type*} [Fintype E] [DecidableEq V] (G : StochGraph V E) (x : V) :
    Finset E :=
  Finset.univ.filter (fun e => G.src e = x ∨ G.dst e = x)

end OfflineStochMatching.UnitPatience


