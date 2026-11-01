-- Prove2me | Definitions.Def_ProcessingNetworks_MArP_IsInvariantDistribution
-- name    : ProcessingNetworks_MArP_IsInvariantDistribution
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:28:24.661816+00:00
-- url     : https://prove2.me/theorems/9fca3a96-a77a-41ca-af4e-b9f72e36ef5e
-- title:
--   Stationary distribution of a discrete-time Markov chain (Definition C.17)
-- statement:
--   A probability distribution $\pi$ on a countable state space $\mathcal S$ is a **stationary distribution** of the discrete-time Markov chain with transition matrix $P$ if it is invariant for $P$:
--   $$
--   \sum_{x\in\mathcal S}\pi(x)P(x,y)=\pi(y)\qquad\text{for every }y\in\mathcal S .
--   $$
--
--   **Formalization Note** The sum is taken in $[0,\infty]$. The continuous-time notion is the published `ProcessingNetworks.Stability.IsStationaryDistribution`, which carries exit rates.
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Definition C.17, p.279 (PDF p.295)

import Mathlib

namespace ProcessingNetworks.MArP

/-- `π` is a stationary distribution of the discrete-time chain with transition matrix `P`
(Dai & Harrison, Processing Networks, pre-publication draft 2020-4-2, Definition C.17, p.279,
PDF p.295): a probability distribution that is an invariant measure for `P`,
`∑_{x} π(x) P(x, y) = π(y)` for every `y`.

**Formalization Note.** A `PMF` is a probability distribution by construction, and the sum is taken
in `ℝ≥0∞`, so it has no junk value. -/
def IsInvariantDistribution {S : Type*} (P : S → PMF S) (π : PMF S) : Prop :=
  ∀ y, ∑' x, π x * P x y = π y

end ProcessingNetworks.MArP


