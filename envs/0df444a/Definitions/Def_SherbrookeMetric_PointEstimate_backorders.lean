-- Prove2me | Definitions.Def_SherbrookeMetric_PointEstimate_backorders
-- name    : SherbrookeMetric_PointEstimate_backorders
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:51:27.992082+00:00
-- url     : https://prove2.me/theorems/e703328b-0954-45e0-9cea-b1e183a04752
-- title:
--   Eq. (2), p. 132 — expected backorders $B(s \mid \lambda)$ under Poisson demand with mean $\lambda$
-- statement:
--   Consider a single recoverable item managed under a one-for-one replenishment policy with **spare stock** $s \in \{0, 1, 2, \dots\}$ (stock on hand plus on order plus in repair, minus backorders). Let the number of units in resupply at a random point in time be Poisson distributed with mean $\lambda$, so that
--   $$p(x \mid \lambda) = e^{-\lambda}\,\frac{\lambda^x}{x!}, \qquad x = 0, 1, 2, \dots$$
--   The **expected number of backorders** at a random point in time is
--   $$B(s \mid \lambda) = \sum_{x = s+1}^{\infty} (x - s)\, p(x \mid \lambda).$$
--
--   This is eq. (2) of Sherbrooke (1968), $B(s) = \sum_{x=s+1}^{\infty}(x-s)\,p(x \mid \lambda T)$, in the special case of Poisson demand used on p. 138: the paper's mean $\lambda T$ (customer rate times mean resupply time; on p. 138 the mean demand "over a unit time interval") enters only through the mean, written here as the single parameter $\lambda$. It is the expected positive part $\mathbb E[(X - s)^+]$ of a Poisson variable $X$ with mean $\lambda$, and is the quantity whose dependence on $\lambda$ the mission studies.
--
--   **Formalization Note** The Poisson probabilities are the published `ServiceParts.StockLevels.poissonPmf` (real mean, natural-number argument). The sum is written as a `tsum` over all $x \in \mathbb N$ of a term that is $0$ for $x \le s$. The family is summable for every real $\lambda$, so the `tsum` is the genuine series; no statement depends on the junk value $0$ that `tsum` assigns to non-summable families. The closed form $B(s \mid \lambda) = \lambda - s + \sum_{x < s}(s - x)\,p(x \mid \lambda)$ is a consequence, not the definition.
-- source:
--   Sherbrooke, METRIC: A Multi-Echelon Technique for Recoverable Item Control, Oper. Res. 16 (1968), p. 132, Eq. (2); p. 138, Demand Prediction

import Mathlib
import Definitions.Def_ServiceParts_StockLevels_Basic

namespace SherbrookeMetric.PointEstimate

open ServiceParts.StockLevels

/-- Expected backorders under Poisson demand, Sherbrooke (1968) eq. (2), p. 132, with the
compound Poisson density specialised to the Poisson probabilities `p(x | λ) = e^{-λ} λ^x / x!`
(p. 138) and the mean `λT` written as `lam`:
`B(s | λ) = Σ_{x = s+1}^{∞} (x - s) p(x | λ)` for spare stock `s` and mean demand `lam`.

The family is summable for every real `lam` (it is dominated by `x · |lam|^x / x!`), so the
`tsum` is the genuine series; no statement about `backorders` relies on the junk value `0`
that `tsum` returns on a non-summable family. -/
noncomputable def backorders (s : ℕ) (lam : ℝ) : ℝ :=
  ∑' x : ℕ, if s < x then ((x : ℝ) - s) * poissonPmf lam x else 0

end SherbrookeMetric.PointEstimate


