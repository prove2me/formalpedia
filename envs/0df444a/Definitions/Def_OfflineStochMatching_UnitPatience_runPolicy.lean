-- Prove2me | Definitions.Def_OfflineStochMatching_UnitPatience_runPolicy
-- name    : OfflineStochMatching_UnitPatience_runPolicy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:36:29.298487+00:00
-- url     : https://prove2.me/theorems/254d65fd-72a3-4da7-83d2-e13b492a2699
-- title:
--   History of a probing policy after $n$ steps
-- statement:
--   For a policy $\pi$ and an activeness realization $P$, the history after $n$ steps is defined recursively: it is empty after $0$ steps; at step $n+1$ the policy is consulted on the current history $h$, and if it asks to probe $e$ then $(e,P_e)$ is appended to $h$, while if it stops, $h$ is kept. A probed edge that is active is matched.
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3, §1, pp. 1–2 (probing; probes in any order based on past realizations)

import Mathlib
import Definitions.Def_OfflineStochMatching_UnitPatience_Policy

namespace OfflineStochMatching.UnitPatience

/-- **The history of a probing policy after `n` steps.**
Brubach, Grammel, Ma, MacRury, Srinivasan, *Improved Guarantees for Offline Stochastic Matching via
New Ordered Contention Resolution Schemes*, arXiv:2106.06892v3, §1, pp. 1–2: an edge "can be
*probed* to determine whether it is active, and if so, it is irrevocably inserted into the
matching"; algorithms "probe the edges in any order based on the realizations of past probes".

`runPolicy π P n` is the list of (edge, outcome) pairs after `n` steps of `π` under the
activeness realization `P`: starting from the empty history, at each step the policy is asked
for an edge `e`; if it answers `some e`, then `(e, P e)` is appended; if it answers `none`, the
history stays as it is (the run has stopped). -/
def runPolicy {E : Type*} (π : Policy E) (P : E → Bool) : ℕ → List (E × Bool)
  | 0 => []
  | n + 1 =>
    match π (runPolicy π P n) with
    | none => runPolicy π P n
    | some e => runPolicy π P n ++ [(e, P e)]

end OfflineStochMatching.UnitPatience


