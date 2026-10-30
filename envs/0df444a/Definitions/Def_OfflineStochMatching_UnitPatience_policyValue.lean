-- Prove2me | Definitions.Def_OfflineStochMatching_UnitPatience_policyValue
-- name    : OfflineStochMatching_UnitPatience_policyValue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:37:46.028907+00:00
-- url     : https://prove2.me/theorems/45a3df3a-6add-47e2-af7e-44b1e3eccb9a
-- title:
--   Expected weight matched by a probing policy
-- statement:
--   The expected weight matched by a policy $\pi$ is
--
--   $$
--   \sum_{P\in\{0,1\}^E}\Pr[P]\sum_{(e,1)\in h_\pi(P)} w_e,
--   $$
--
--   where $h_\pi(P)$ is the history of $\pi$ under the realization $P$ after $|E|$ steps and the inner sum runs over the probed edges found active, i.e. the matched edges.
--
--   **Formalization Note** A valid policy never probes an edge twice, so after $|E|$ steps its run has stopped and the history is complete.
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3, §1, p. 1 (maximize the expected weighted matching); §2, p. 7 (expected weight matched)

import Mathlib
import Definitions.Def_OfflineStochMatching_UnitPatience_activeProb
import Definitions.Def_OfflineStochMatching_UnitPatience_runPolicy

namespace OfflineStochMatching.UnitPatience

/-- **Expected weight matched by a probing policy.**
Brubach, Grammel, Ma, MacRury, Srinivasan, *Improved Guarantees for Offline Stochastic Matching via
New Ordered Contention Resolution Schemes*, arXiv:2106.06892v3, §1, p. 1: a probed edge that is
active "is irrevocably inserted into the matching. The objective is to sequentially probe the
edges in a way to maximize the expected weighted matching at the end."; §2, p. 7: "its expected
weight matched".

`policyValue G π = Σ_P Pr[P] · Σ_{(e, true) in the run} w_e`: the expected total weight of the
probed edges found active, i.e. of the matched edges, over independent activeness realizations
`P`, after `|E|` steps of the run.

**Formalization Note.** A valid policy (`IsValidPolicy`) never probes an edge twice, so after
`|E|` steps its run has stopped; the fuel `Fintype.card E` therefore gives the value of the
complete run. -/
def policyValue {V E : Type*} [Fintype E] [DecidableEq E] (G : StochGraph V E)
    (π : Policy E) : ℝ :=
  ∑ P : E → Bool, activeProb G P *
    ((runPolicy π P (Fintype.card E)).map (fun eb => if eb.2 then G.w eb.1 else 0)).sum

end OfflineStochMatching.UnitPatience


