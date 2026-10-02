-- Prove2me | Definitions.Def_ProcessingNetworks_FeedforwardStability_Feedforward
-- name    : ProcessingNetworks_FeedforwardStability_Feedforward
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T18:02:49.389082+00:00
-- url     : https://prove2.me/theorems/9509398e-5d06-4aa1-abae-df281e481e40
-- title:
--   Definition 8.13 — feedforward queueing network
-- statement:
--   **Definition 8.13.** A queueing network is **feedforward** if its stations can be numbered so
--   that, under the new numbering, a higher-numbered station never routes work into a
--   lower-numbered one: there is a relabeling $\tau$ of the pools such that
--   $\tau(p(i)) > \tau(p(j))$ implies $P_{ij} = 0$. Feedback to the same station
--   ($p(i) = p(j)$) is explicitly allowed.
--
--   **Formalization note.** "Can be numbered" is formalized as the existence of a permutation
--   $\tau$ of the pool index set `Fin K` relabeling the (arbitrary, fixed) pool assignment `p` —
--   matching the book's own phrasing that a *suitable* numbering exists, not that the given `p`
--   already has this property.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 144, Definition 8.13

import Mathlib
import Definitions.Def_ProcessingNetworks_FeedforwardStability_QueueingNetworkData

namespace ProcessingNetworks.FeedforwardStability

/-- Definition 8.13 (feedforward queueing network), Dai & Harrison p. 144 (PDF p. 160): a
queueing network is feedforward if its stations can be numbered (a relabeling `τ` of the pool
index set) so that a higher-numbered station never routes into a lower-numbered one: for
`i, j ∈ I`, `τ(p(i)) > τ(p(j))` implies `P i j = 0`. Feedback to the same station (`p(i) = p(j)`)
is allowed. -/
def IsFeedforward {I K : ℕ} (dat : QueueingNetworkData I K) : Prop :=
  ∃ τ : Equiv.Perm (Fin K), ∀ i j : Fin I, τ (dat.p i) > τ (dat.p j) → dat.P i j = 0

end ProcessingNetworks.FeedforwardStability


