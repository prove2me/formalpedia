-- Prove2me | Definitions.Def_OfflineStochMatching_UnitPatience_activeProb
-- name    : OfflineStochMatching_UnitPatience_activeProb
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:31:40.073325+00:00
-- url     : https://prove2.me/theorems/b5277e5e-915a-4554-b74c-a08125fa29f9
-- title:
--   Probability of an activeness realization under independent edges
-- statement:
--   Edges of $G$ are active independently, edge $e$ with probability $p_e$. For a realization $P\in\{0,1\}^E$ ($P_e=1$ iff $e$ is active) its probability is
--
--   $$
--   \Pr[P]=\prod_{e\in E} p_e^{P_e}(1-p_e)^{1-P_e}.
--   $$
--
--   Every expectation in this mission is a finite sum over realizations weighted by this probability.
--
--   **Formalization Note** Expectations are finite sums over `E → Bool`; no measure theory is used.
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3, §1, p. 1 (each edge e is active independently according to a known probability p_e)

import Mathlib
import Definitions.Def_OfflineStochMatching_UnitPatience_StochGraph

namespace OfflineStochMatching.UnitPatience

/-- **Probability of an activeness realization.**
Brubach, Grammel, Ma, MacRury, Srinivasan, *Improved Guarantees for Offline Stochastic Matching via
New Ordered Contention Resolution Schemes*, arXiv:2106.06892v3, §1, p. 1: "each edge `e` is
*active* independently according to a known probability `p_e`".

For a realization `P : E → Bool` (`P e = true` iff edge `e` is active),
`activeProb G P = Π_e (p_e if P e, else 1 − p_e)`, the probability of `P` when the edges are
active independently.

**Formalization Note.** Every expectation in this mission is a finite sum over realizations
`E → Bool` weighted by `activeProb` (and by the rounding distribution `μ`); no measure theory is
used. -/
def activeProb {V E : Type*} [Fintype E] (G : StochGraph V E) (P : E → Bool) : ℝ :=
  ∏ e, if P e then G.p e else 1 - G.p e

end OfflineStochMatching.UnitPatience


