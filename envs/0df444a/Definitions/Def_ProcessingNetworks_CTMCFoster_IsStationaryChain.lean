-- Prove2me | Definitions.Def_ProcessingNetworks_CTMCFoster_IsStationaryChain
-- name    : ProcessingNetworks_CTMCFoster_IsStationaryChain
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:26:59.865623+00:00
-- url     : https://prove2.me/theorems/0f6ded1a-75fa-496d-8b47-914984aa8ff2
-- title:
--   Stationary distributions of a discrete-time chain (Definition C.17)
-- statement:
--   Let $P$ be a stochastic matrix on a countable set $\mathscr S$. A probability distribution $\pi$ on $\mathscr S$ is a **stationary distribution** of the discrete-time chain with transition matrix $P$ if $\pi$ is an invariant measure for $P$:
--
--   $$
--   \sum_{i}\pi(i)P_{ij}=\pi(j)\quad\text{for every }j\in\mathscr S.
--   $$
--
--   **Formalization Note** The sum is taken in the extended non-negative reals, where it needs no convergence side condition.
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Definition C.17, p.279 (PDF 295)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_MaxWeight_Chain

namespace ProcessingNetworks.CTMCFoster

open KellyStochasticNetworks.MaxWeight

/-- The probability distribution `π` is a stationary distribution of the discrete-time chain with
transition matrix `P` (Definition C.17): `π P = π`, i.e. `∑_i π(i) P(i, j) = π(j)` for every `j`.

Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Definition C.17,
p.279 (PDF 295).

**Formalization Note** The sum is taken in `ℝ≥0∞`; its terms are non-negative, so there is no junk
value, and the right side is at most one. -/
def IsStationaryChain {S : Type*} (P : Chain S) (π : PMF S) : Prop :=
  ∀ j, ∑' i, π i * P i j = π j

end ProcessingNetworks.CTMCFoster


