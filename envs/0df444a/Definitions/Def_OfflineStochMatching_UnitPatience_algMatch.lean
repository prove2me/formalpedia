-- Prove2me | Definitions.Def_OfflineStochMatching_UnitPatience_algMatch
-- name    : OfflineStochMatching_UnitPatience_algMatch
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:33:05.767007+00:00
-- url     : https://prove2.me/theorems/3e349ad6-02c7-4df8-892c-462c2945e122
-- title:
--   Edge matched at a vertex of $V_2$ by the algorithm of Section 4
-- statement:
--   Fix a probing order $\sigma_v$ of the edges at $v$, a rounded vector $Y\in\{0,1\}^E$ and an activeness realization $P\in\{0,1\}^E$. The algorithm of Section 4 probes, in the order $\sigma_v$, the edges $e$ with $Y_e=1$, and the first one found active is matched. The **edge matched at $v$** is the first $e$ in $\sigma_v$ with $Y_e=P_e=1$, if there is one; otherwise $v$ is unmatched.
--
--   **Formalization Note** The star of $v$ is treated in isolation, as in the paper's analysis: in the setting of Section 4 each vertex of the unit-patience side carries at most one rounded edge, so no other star competes for the other endpoint.
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3, §4, p. 16 (for each vertex v ∈ V2, probe the edges e ∈ δ(v) in decreasing order of weight, for each e with Y_e = 1); §1, p. 1

import Mathlib

namespace OfflineStochMatching.UnitPatience

/-- **The edge matched at a vertex of `V2` by the algorithm of §4.**
Brubach, Grammel, Ma, MacRury, Srinivasan, *Improved Guarantees for Offline Stochastic Matching via
New Ordered Contention Resolution Schemes*, arXiv:2106.06892v3, §4, p. 16: "For each vertex
`v ∈ V2`, we probe the edges `e ∈ δ(v)` in decreasing order of weight, for each `e` with
`Y_e = 1`"; §1, p. 1: "An edge whose endpoints are unmatched can be probed to determine whether
it is active, and if so, it is irrevocably inserted into the matching."

Given the probing order `σ v` of the edges at `v`, the rounded vector `Y` and the activeness
realization `P`, `algMatch σ Y P v` is the first edge `e` in `σ v` with `Y e = true` and
`P e = true` (the first probed edge that turns out active), or `none` if there is none.

**Formalization Note.** The star at `v` is treated in isolation, as the paper's analysis does
(p. 16: "it is the center of a star graph that is disconnected from any other vertices of
`V2`"); in the §4 setting each `u ∈ V1` carries at most one rounded edge, so no other star can
have matched the other endpoint. -/
def algMatch {V E : Type*} (σ : V → List E) (Y P : E → Bool) (v : V) : Option E :=
  (σ v).find? (fun e => Y e && P e)

end OfflineStochMatching.UnitPatience


