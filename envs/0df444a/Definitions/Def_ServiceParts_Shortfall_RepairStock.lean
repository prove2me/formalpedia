-- Prove2me | Definitions.Def_ServiceParts_Shortfall_RepairStock
-- name    : ServiceParts_Shortfall_RepairStock
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T23:21:07.942487+00:00
-- url     : https://prove2.me/theorems/e6cdeaae-f84f-4ba5-906a-4d506c239726
-- title:
--   M/M/1 repair system: η_i = λ_i/(µ − λ + λ_i), geometric pmf, and the item stock cost (Section 8.3.1)
-- statement:
--   Section 8.3.1 considers a depot repairing $n$ item types in a single first-come, first-served exponential server with repair rate $\mu$; reparable units of item $i$ arrive as a Poisson process with rate $\lambda_i$, and $\lambda = \sum_i \lambda_i$. This file defines three quantities used there.
--
--   1. The parameter
--   $$\eta_i = \frac{\lambda_i}{\mu - \lambda + \lambda_i}.$$
--   2. The geometric probability mass function $p(j) = (1 - \eta)\eta^j$, $j = 0, 1, 2, \dots$
--   3. The expected holding and backorder cost rate of an item at stock level $s \in \{0, 1, 2, \dots\}$, when the number of its units in repair has law $p$, holding cost rate $h$ and backorder cost rate $b$:
--   $$C(s) = h \sum_{j=0}^{s} (s - j)\,p(j) + b \sum_{j \ge s} (j - s)\,p(j).$$
--
--   These are the ingredients of the geometric law of the item-$i$ repair count and of the stock-level rule of Section 8.3.1.
--
--   **Formalization Note** The infinite sum in $C(s)$ is an unconditional sum (`tsum`); it converges for $0 \le \eta < 1$.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, pp. 201-205, Section 8.3 and 8.3.1 (eta_i p. 203, p_i(j) p. 204, cost p. 205)

import Mathlib

namespace ServiceParts.Shortfall

/-- The parameter `η_i = λ_i / (µ − λ + λ_i)` of Section 8.3.1, p. 203, for an item with
reparable-unit arrival rate `λ_i` (`lamI`), total arrival rate `λ` (`lam`) and repair rate `µ`
(`mu`). -/
noncomputable def repairEta (lamI lam mu : ℝ) : ℝ :=
  lamI / (mu - lam + lamI)

/-- The geometric probability mass function `p(j) = (1 − η) η^j`, `j = 0, 1, 2, …`. -/
noncomputable def geomPMF (η : ℝ) (j : ℕ) : ℝ :=
  (1 - η) * η ^ j

/-- The expected holding and backorder cost rate of item `i` at stock level `s` (Section 8.3.1,
p. 205), when the number of its units in the repair system has the geometric law
`p(j) = (1 − η) η^j`:
`h ∑_{j=0}^{s} (s − j) p(j) + b ∑_{j ≥ s} (j − s) p(j)`,
with holding cost rate `h` and backorder cost rate `b`. -/
noncomputable def stockCost (h b η : ℝ) (s : ℕ) : ℝ :=
  h * ∑ j ∈ Finset.range (s + 1), ((s : ℝ) - j) * geomPMF η j
    + b * ∑' j : ℕ, (if s ≤ j then ((j : ℝ) - s) * geomPMF η j else 0)

end ServiceParts.Shortfall


