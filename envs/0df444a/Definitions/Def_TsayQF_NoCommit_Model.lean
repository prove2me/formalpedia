-- Prove2me | Definitions.Def_TsayQF_NoCommit_Model
-- name    : TsayQF_NoCommit_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:45.911803+00:00
-- url     : https://prove2.me/theorems/251f9fc5-bb3d-4ae8-b98e-a09b1e1b1725
-- title:
--   §3, §4, §5, pp. 1344–1347 — costs, demand X = μ + ε, the retailer's conditional profit G(r|μ) (1), the no-commitment purchase, and the retailer, EM, system and centralized expected profits
-- statement:
--   This file sets up the two-player supply chain of Tsay (1999) without commitment.
--
--   **Costs (§3.1).** A cost datum consists of the retail price $p$, the unit transfer price $c$ paid by the retailer to the manufacturer (EM), the unit production cost $m$, the unit salvage value $u$ (the same for either party) and the unit goodwill loss $s$ on unmet demand. It carries the standing assumptions of the paper:
--   $$p > c > m > 0, \qquad u < m, \qquad s \ge 0 .$$
--   Three critical fractiles are attached to it: the retailer's $\kappa_R = \frac{p+s-c}{p+s-u}$, the EM's $\kappa_{EM} = \frac{c-m}{c-u}$ and the system's $\kappa_S = \frac{p+s-m}{p+s-u}$.
--
--   **Demand (§3.3).** Market demand is $X = \mu + \varepsilon$, where the signal $\mu$ has law $\nu$ (a probability measure on $\mathbb R$ with distribution function $\Theta$) and the error $\varepsilon \sim N(0, \sigma_\varepsilon^2)$ is independent of $\mu$. The law of $X$ is the image of $\nu \otimes N(0,\sigma_\varepsilon^2)$ under $(\mu,\varepsilon) \mapsto \mu + \varepsilon$; its distribution function is $F$. Given $\mu$, $X \sim N(\mu, \sigma_\varepsilon^2)$.
--
--   **The retailer's conditional problem (1).** After observing $\mu$, the retailer buying $r$ units earns in expectation
--   $$G(r \mid \mu) = E_{X\mid\mu}\big\{p\min[X,r] - c\,r - s[X-r]^+ + u[r-X]^+\big\}.$$
--   Given $z_\varepsilon$, the retailer's purchase without commitment, when the EM has built $Q$, is $r^*_{NC}(Q,\mu) = \min[\mu + z_\varepsilon\sigma_\varepsilon, Q]$.
--
--   **Expected profits.** At production $Q$:
--   1. the retailer earns $\pi_{R,NC}(Q) = E_\mu\, G(r^*_{NC}(Q,\mu)\mid\mu)$;
--   2. the EM sells the retailer's purchase at $c$, salvages its surplus at $u$ and pays $m$ per unit, so $\pi_{EM,NC}(Q) = (c-u)\,E_\mu\, r^*_{NC}(Q,\mu) - (m-u)\,Q$;
--   3. the expected total system profit is $\pi_{R,NC}(Q) + \pi_{EM,NC}(Q)$;
--   4. a central planner (§4) producing $Q$ before the signal earns $\Pi_{CC}(Q) = E_X\{p\min[X,Q] - s[X-Q]^+ + u[Q-X]^+\} - m\,Q$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** The variance $\sigma_\varepsilon^2$ is a parameter `v : ℝ≥0` and $\sigma_\varepsilon = \sqrt v$; `v = 0` is allowed and gives the Dirac law. The fractile $z_\varepsilon = \Phi^{-1}(\kappa_R)$ is not defined here: it is a real parameter `z` of the profit functions, and every theorem pins it by the hypothesis $\Phi(z) = \kappa_R$. Expectations are Bochner integrals; the theorems assume $\mu$ has a finite second moment, which makes every integrand integrable.
-- source:
--   Tsay, The quantity flexibility contract and supplier-customer incentives, Management Science 45(10) (1999), pp. 1344–1347, §3.1, §3.3, §4, §5.1 (1), §5.2

import Mathlib

namespace TsayQF.NoCommit

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- The cost data of §3.1 (p. 1344) together with the standing assumptions
(i) `p > c > m > 0`, (ii) `u < m`, (iii) `s ≥ 0`. -/
structure Data where
  /-- retail price per unit -/
  p : ℝ
  /-- unit wholesale ("transfer") price -/
  c : ℝ
  /-- unit production cost -/
  m : ℝ
  /-- salvage value per unit -/
  u : ℝ
  /-- goodwill loss per unit of unmet demand -/
  s : ℝ
  hm : 0 < m
  hmc : m < c
  hcp : c < p
  hum : u < m
  hs : 0 ≤ s

/-- The retailer's critical fractile `(p + s − c)/(p + s − u)`. -/
noncomputable def kR (D : Data) : ℝ := (D.p + D.s - D.c) / (D.p + D.s - D.u)

/-- The EM's critical fractile `(c − m)/(c − u)`. -/
noncomputable def kEM (D : Data) : ℝ := (D.c - D.m) / (D.c - D.u)

/-- The system's critical fractile `(p + s − m)/(p + s − u)`. -/
noncomputable def kS (D : Data) : ℝ := (D.p + D.s - D.m) / (D.p + D.s - D.u)

/-- The integrand of (1): the retailer's profit when demand is `x` and the purchase is `r`,
`p·min[x, r] − c·r − s[x − r]⁺ + u[r − x]⁺`. -/
noncomputable def payoff (D : Data) (x r : ℝ) : ℝ :=
  D.p * min x r - D.c * r - D.s * max (x - r) 0 + D.u * max (r - x) 0

/-- `G(r|μ)` of (1): the retailer's expected profit from purchase `r` given the signal `μ`,
with `X | μ ~ N(μ, v)` and `v = σ_ε²`. -/
noncomputable def G (D : Data) (v : ℝ≥0) (r μ : ℝ) : ℝ :=
  ∫ x, payoff D x r ∂(gaussianReal μ v)

/-- The law of market demand `X = μ + ε`, with `μ ~ ν` and `ε ~ N(0, v)` independent. -/
noncomputable def lawX (ν : Measure ℝ) (v : ℝ≥0) : Measure ℝ :=
  (ν.prod (gaussianReal 0 v)).map (fun z => z.1 + z.2)

/-- The retailer's purchase without commitment, `r*_NC(Q, μ) = min[μ + z σ_ε, Q]`. -/
noncomputable def ncPurchase (v : ℝ≥0) (z μ Q : ℝ) : ℝ :=
  min (μ + z * Real.sqrt v) Q

/-- The retailer's expected profit `π_R,NC` when the EM has produced `Q`. -/
noncomputable def retailerProfit (D : Data) (ν : Measure ℝ) (v : ℝ≥0) (z Q : ℝ) : ℝ :=
  ∫ μ, G D v (ncPurchase v z μ Q) μ ∂ν

/-- The EM's expected profit `π_EM,NC` from producing `Q`: it sells the retailer's purchase at
`c`, salvages the surplus at `u` and pays `m` per unit produced. -/
noncomputable def emProfit (D : Data) (ν : Measure ℝ) (v : ℝ≥0) (z Q : ℝ) : ℝ :=
  (D.c - D.u) * ∫ μ, ncPurchase v z μ Q ∂ν - (D.m - D.u) * Q

/-- Expected total system profit under no commitment at production `Q`. -/
noncomputable def systemProfit (D : Data) (ν : Measure ℝ) (v : ℝ≥0) (z Q : ℝ) : ℝ :=
  retailerProfit D ν v z Q + emProfit D ν v z Q

/-- Expected system profit of the central planner (§4) producing `Q`. -/
noncomputable def ccProfit (D : Data) (ν : Measure ℝ) (v : ℝ≥0) (Q : ℝ) : ℝ :=
  ∫ x, (D.p * min x Q - D.s * max (x - Q) 0 + D.u * max (Q - x) 0) ∂(lawX ν v) - D.m * Q

end TsayQF.NoCommit


