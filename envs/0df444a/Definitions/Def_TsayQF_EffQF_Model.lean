-- Prove2me | Definitions.Def_TsayQF_EffQF_Model
-- name    : TsayQF_EffQF_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:42.760969+00:00
-- url     : https://prove2.me/theorems/1eddc1da-a75d-42a2-bbf2-ee1b9dea474b
-- title:
--   §3, §4, §6–§7, pp. 1344–1350 — costs, the σ_ε = 0 retailer profit G(r|μ), the purchase μ ⊥ [q(1−ω), Q], EM profit (2), forecast and centralized profits, ψ and c̄(ψ) of (4)
-- statement:
--   These are the objects of Tsay's two-stage supply chain under a **quantity flexibility (QF) contract**, in the special case $\sigma_\varepsilon = 0$ of §7, where the demand signal $\mu$ predicts market demand perfectly.
--
--   **Costs (§3.1).** The retail price is $p$, the unit production cost of the manufacturer (EM) is $m$, the salvage value of an unused unit is $u$ (the same at either site), and $s$ is the goodwill loss per unit of unmet demand. The standing assumptions are $p > m > 0$, $u < m$ and $s \ge 0$. The unit transfer price $c$ paid by the retailer to the EM is kept as a separate argument of every object below. The system's critical fractile is
--   $$\kappa_S = \frac{p+s-m}{p+s-u}.$$
--
--   **Demand (§3.3 with $\sigma_\varepsilon = 0$).** The signal $\mu$ has law $\nu$, a probability measure on $\mathbb R$ with distribution function $\Theta$. Market demand equals $\mu$, so $F = \Theta$.
--
--   **Retailer's conditional profit ((1) at $\sigma_\varepsilon=0$).** A retailer that buys $r$ units after observing $\mu$ earns
--   $$G(r\mid\mu) = p\min[\mu,r] - c\,r - s[\mu-r]^+ + u[r-\mu]^+ .$$
--   Its right derivative in $r$ is $G'(r\mid\mu) = p+s-c$ if $r<\mu$ and $u-c$ if $r \ge \mu$.
--
--   **The QF contract (§6).** With forecast $q$ and parameters $\omega\in[0,1]$, $\alpha \ge -\omega$, the EM guarantees up to $q(1+\alpha)$ and the retailer must buy at least $q(1-\omega)$. When the EM has produced $Q$, the retailer buys $r^*_{QF} = \mu \perp [q(1-\omega), Q]$, where $y \perp [a,b] = \max\{a, \min\{y,b\}\}$ is the point of $[a,b]$ closest to $y$ (footnote 7).
--
--   **Expected profits.**
--   1. Retailer: $\pi_{R,QF}(q,Q) = E_\mu\{G(\mu\perp[q(1-\omega),Q]\mid\mu)\}$.
--   2. EM, display (2): $\pi_{EM,QF}(Q; q) = (c-u)E_\mu\{\mu\perp[q(1-\omega),Q]\} - (m-u)Q$.
--   3. Retailer's forecast objective (problem (III)), with the EM building $Q^*_{QF}(q) = q(1+\alpha)$ (Proposition 2): $q \mapsto \pi_{R,QF}(q, q(1+\alpha))$.
--   4. Central planner (§4): $\Pi_{CC}(Q) = E_\mu\{p\min[\mu,Q] - s[\mu-Q]^+ + u[Q-\mu]^+\} - mQ$.
--
--   **Flexibility and the efficient price.** The total flexibility is $\psi = (1+\alpha)/(1-\omega)$, and for a number $F^{-1}$ standing for $F^{-1}(\kappa_S)$ the transfer price (4) is
--   $$\bar c(\psi) = u + \frac{m-u}{\dfrac1\psi F\!\left(\dfrac1\psi F^{-1}\right) + \dfrac{m-u}{p+s-u}} .$$
--
--   These objects carry every statement of the mission: the retailer's purchase rule, its forecast problem (Proposition 3(a)), and the efficiency of the contract at $\bar c(\psi)$ (Proposition 6(a)).
--
--   **Formalization Note.** The transfer price $c$ is not part of the data structure and is not required to satisfy $m < c < p$, because the mission evaluates the objects at $c = \bar c(\psi)$, which can exceed $p$ when $s>0$. The inverse $F^{-1}(\kappa_S)$ is not a function here: `cbar` takes the number as an argument, and theorems supply it together with the equation $F(Q) = \kappa_S$. The forecast objective fixes the EM's production at $q(1+\alpha)$, as §6.1 does after Proposition 2. The value of $G'$ on the diagonal $r=\mu$ is irrelevant under a continuous $\Theta$. Expectations are Bochner integrals against $\nu$.
-- source:
--   Tsay, The quantity flexibility contract and supplier-customer incentives, Management Science 45(10) (1999), pp. 1344–1350, §3.1, §3.3, §4, §5.1 (1), §6, §6.1 (2), §7 (4), footnote 7

import Mathlib

namespace TsayQF.EffQF

open MeasureTheory ProbabilityTheory

/-- The cost data of §3.1 (p. 1344) without the transfer price: retail price `p`, unit
production cost `m`, salvage value `u`, goodwill loss `s`, with the standing assumptions
(i) `p > m > 0` (the part of `p > c > m > 0` not involving `c`), (ii) `u < m`, (iii) `s ≥ 0`.
The transfer price `c` is a separate argument of every object below. -/
structure Data where
  /-- retail price per unit -/
  p : ℝ
  /-- unit production cost -/
  m : ℝ
  /-- salvage value per unit -/
  u : ℝ
  /-- goodwill loss per unit of unmet demand -/
  s : ℝ
  hm : 0 < m
  hmp : m < p
  hum : u < m
  hs : 0 ≤ s

/-- The system's critical fractile `(p + s − m)/(p + s − u)`. -/
noncomputable def kS (D : Data) : ℝ := (D.p + D.s - D.m) / (D.p + D.s - D.u)

/-- `G(r|μ)` of (1) when `σ_ε = 0`: demand equals the signal `μ`, so the retailer who buys `r`
at transfer price `c` earns `p·min[μ, r] − c·r − s[μ − r]⁺ + u[r − μ]⁺`. -/
noncomputable def G (D : Data) (c r μ : ℝ) : ℝ :=
  D.p * min μ r - c * r - D.s * max (μ - r) 0 + D.u * max (r - μ) 0

/-- The right derivative of `r ↦ G(r|μ)` when `σ_ε = 0`: `p + s − c` if `r < μ`, `u − c` if
`r ≥ μ`. -/
noncomputable def Gderiv (D : Data) (c r μ : ℝ) : ℝ :=
  if r < μ then D.p + D.s - c else D.u - c

/-- `y ⊥ [a, b]` (footnote 7): the point of `[a, b]` closest to `y`, when `a ≤ b`. -/
noncomputable def clip (y a b : ℝ) : ℝ := max a (min y b)

/-- The retailer's expected profit `π_R,QF` at forecast `q` and EM production `Q`, when after
observing `μ` it buys `r*_QF = μ ⊥ [q(1 − ω), Q]`. -/
noncomputable def retailerProfit (D : Data) (ν : Measure ℝ) (c ω q Q : ℝ) : ℝ :=
  ∫ μ, G D c (clip μ (q * (1 - ω)) Q) μ ∂ν

/-- The EM's expected profit (2): `(c − u) E_μ{r*_QF(q, Q, μ)} − (m − u) Q`. -/
noncomputable def emProfit (D : Data) (ν : Measure ℝ) (c ω q Q : ℝ) : ℝ :=
  (c - D.u) * ∫ μ, clip μ (q * (1 - ω)) Q ∂ν - (D.m - D.u) * Q

/-- The objective of the retailer's forecast problem (III) under the QF contract
`{c, (α, ω)}`, with the EM producing `Q*_QF(q) = q(1 + α)` (Proposition 2). -/
noncomputable def forecastProfit (D : Data) (ν : Measure ℝ) (c α ω q : ℝ) : ℝ :=
  retailerProfit D ν c ω q (q * (1 + α))

/-- Expected system profit of the central planner (§4) producing `Q`, when `σ_ε = 0`
(market demand is `μ ~ ν`). -/
noncomputable def ccProfit (D : Data) (ν : Measure ℝ) (Q : ℝ) : ℝ :=
  ∫ μ, (D.p * min μ Q - D.s * max (μ - Q) 0 + D.u * max (Q - μ) 0) ∂ν - D.m * Q

/-- The total flexibility `ψ = (1 + α)/(1 − ω)`. -/
noncomputable def psi (α ω : ℝ) : ℝ := (1 + α) / (1 - ω)

/-- The transfer price `c̄(ψ)` of (4), with `F^{-1}((p + s − m)/(p + s − u))` passed as `Finv`:
`u + (m − u) / ((1/ψ) F((1/ψ) Finv) + (m − u)/(p + s − u))`, where `F` is the cdf of `ν`. -/
noncomputable def cbar (D : Data) (ν : Measure ℝ) (ψ Finv : ℝ) : ℝ :=
  D.u + (D.m - D.u) /
    ((1 / ψ) * cdf ν ((1 / ψ) * Finv) + (D.m - D.u) / (D.p + D.s - D.u))

end TsayQF.EffQF


