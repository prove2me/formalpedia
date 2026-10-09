-- Prove2me | Definitions.Def_SLPricing_Resp_Benchmark
-- name    : SLPricing_Resp_Benchmark
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T10:07:41.179124+00:00
-- url     : https://prove2.me/theorems/39681fbc-9e58-4f3a-a512-c297ebd88c8d
-- title:
--   §6.1, (5), Proposition 4, p. 19 — the no-SL responsive threshold $\chi(p_1)$, profit $\pi_{br}(p_1)$ and prices $p_1^*$, $p_2^*$
-- statement:
--   These are the closed-form expressions of the benchmark without social learning under responsive pricing (§6.1). Let $c\in[0,1)$ be the unit cost and $\delta\in[0,1]$ the consumers' discount factor.
--
--   1. The first-period threshold of (5):
--   $$\chi(p_1)=\begin{cases}\dfrac{2p_1-c\delta}{2-\delta} & \text{if } p_1\le \dfrac{2-\delta(1-c)}{2},\\[4pt] 1 & \text{if } p_1> \dfrac{2-\delta(1-c)}{2}.\end{cases}$$
--   2. The firm's profit as a function of the first-period price, as printed on p. 19:
--   $$\pi_{br}(p_1)=(p_1-c)\big(1-\chi(p_1)\big)+\frac{(\chi(p_1)-c)^2}{4}.$$
--   3. The prices of Proposition 4:
--   $$p_1^*=\frac{2c+\delta^2(1-c)+4(1-\delta)}{6-4\delta},\qquad p_2^*=\frac{\chi(p_1^*)+c}{2}.$$
--
--   These are formulas only. That $[\chi(p_1),1]$ is the equilibrium set of first-period buyers is the theorem (5), and that $p_1^*$ is optimal with value $\pi_{br}(p_1^*)$ is Proposition 4.
--
--   **Formalization Note** The functions take $(c,\delta,\dots)$ explicitly rather than a parameter record. The page's formula for $\chi$ is the equilibrium threshold only when $p_1\ge c$; the theorem (5) carries that hypothesis.
-- source:
--   Papanastasiou–Savva, accepted manuscript MS-14-00028.R2 (2016), §6.1, equation (5), profit π_br, Proposition 4, p. 19

import Mathlib

namespace SLPricing.Resp

/-- (5), §6.1, p. 19: the first-period purchasing threshold `χ(p₁)` under responsive pricing
without social learning, for unit cost `c` and consumer discount factor `δ`:
`(2p₁ − cδ)/(2 − δ)` if `p₁ ≤ (2 − δ(1 − c))/2`, and `1` otherwise. (The page's formula; it is
the equilibrium threshold only for `p₁ ≥ c`.) -/
noncomputable def chi (c δ p₁ : ℝ) : ℝ :=
  if p₁ ≤ (2 - δ * (1 - c)) / 2 then (2 * p₁ - c * δ) / (2 - δ) else 1

/-- §6.1, p. 19: the firm's profit without social learning as a function of the first-period
price, `π_br(p₁) = (p₁ − c)(1 − χ(p₁)) + (χ(p₁) − c)²/4`. -/
noncomputable def profitNoSL (c δ p₁ : ℝ) : ℝ :=
  (p₁ - c) * (1 - chi c δ p₁) + (chi c δ p₁ - c) ^ 2 / 4

/-- Proposition 4, p. 19: the optimal first-period price without social learning,
`p∗₁ = (2c + δ²(1 − c) + 4(1 − δ))/(6 − 4δ)`. -/
noncomputable def p1StarNoSL (c δ : ℝ) : ℝ :=
  (2 * c + δ ^ 2 * (1 - c) + 4 * (1 - δ)) / (6 - 4 * δ)

/-- Proposition 4, p. 19: the optimal second-period price without social learning,
`p∗₂ = (χ(p∗₁) + c)/2`. -/
noncomputable def p2StarNoSL (c δ : ℝ) : ℝ :=
  (chi c δ (p1StarNoSL c δ) + c) / 2

end SLPricing.Resp


