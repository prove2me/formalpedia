-- Prove2me | Definitions.Def_OfflineStochMatching_UnitPatience_algProbes
-- name    : OfflineStochMatching_UnitPatience_algProbes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:33:22.007713+00:00
-- url     : https://prove2.me/theorems/0b250c54-393f-4469-9ed6-de4959a91252
-- title:
--   Edges probed at a vertex of $V_2$ by the algorithm of Section 4
-- statement:
--   With the probing order $\sigma_v$, the rounded vector $Y$ and the activeness realization $P$, let $l$ be the sublist of $\sigma_v$ of edges with $Y_e=1$. The algorithm probes $l$ in order and stops at the first active edge, which is matched. The **edges probed at $v$** are the prefix of $l$ up to and including its first edge with $P_e=1$, or all of $l$ if none of its edges is active.
--
--   These are the probes counted by the patience constraint of $v$ and of the other endpoints.
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3, §4, p. 16 (for each vertex v ∈ V2, probe the edges e ∈ δ(v) in decreasing order of weight, for each e with Y_e = 1)

import Mathlib

namespace OfflineStochMatching.UnitPatience

/-- **The edges probed at a vertex of `V2` by the algorithm of §4.**
Brubach, Grammel, Ma, MacRury, Srinivasan, *Improved Guarantees for Offline Stochastic Matching via
New Ordered Contention Resolution Schemes*, arXiv:2106.06892v3, §4, p. 16: "For each vertex
`v ∈ V2`, we probe the edges `e ∈ δ(v)` in decreasing order of weight, for each `e` with
`Y_e = 1`."

Let `l` be the sublist of `σ v` of edges with `Y e = true`. The algorithm probes `l` in order and
stops at the first active edge (which is matched, so `v` can probe no further). `algProbes σ Y P v`
is the prefix of `l` up to and including its first edge with `P e = true`, or all of `l` if no
edge of `l` is active.

**Formalization Note.** `l.take (n + 1)` with `n` the length of the inactive prefix; when no edge
is active `n + 1` exceeds the length and the whole of `l` is returned. -/
def algProbes {V E : Type*} (σ : V → List E) (Y P : E → Bool) (v : V) : List E :=
  let l := (σ v).filter (fun e => Y e)
  l.take ((l.takeWhile (fun e => !P e)).length + 1)

end OfflineStochMatching.UnitPatience


