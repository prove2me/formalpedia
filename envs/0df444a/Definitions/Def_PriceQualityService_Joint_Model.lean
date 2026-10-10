-- Prove2me | Definitions.Def_PriceQualityService_Joint_Model
-- name    : PriceQualityService_Joint_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T18:21:51.580536+00:00
-- url     : https://prove2.me/theorems/0429d982-8045-4da0-9cbb-a03718670d17
-- title:
--   MNL demand with price, quality and service duration; markup and total profit (2)–(3)
-- statement:
--   A firm offers products $i\in\mathcal N=\{1,\dots,N\}$. Product $i$ has a price $p_i$, a quality level $q_i$ and a service duration $t_i$ (for instance a warranty length). The parameters are the quality sensitivity $\alpha_i$, the service utility per unit time $s_i$, the base service cost per unit time $a_i$, the marginal effect $b_i$ of quality on that service cost, and the production-cost coefficient $c_i$ (production cost $c_iq_i^2$ per unit).
--
--   Under the multinomial logit (MNL) model a consumer buys product $i$ with probability
--   $$
--   d_i(\mathbf p,\mathbf q,\mathbf t;\mathcal N)=\frac{\exp(\alpha_iq_i-p_i+t_is_i)}{1+\sum_{j\in\mathcal N}\exp(\alpha_jq_j-p_j+t_js_j)},
--   $$
--   where the $1$ in the denominator is the no-purchase (outside) option. The **markup** of product $i$ is its price minus its production cost and its service cost,
--   $$
--   p_i-c_iq_i^2-t_i(a_i-b_iq_i),
--   $$
--   and with the market size normalized to one the firm's **total expected profit** is
--   $$
--   \Pi(\mathbf p,\mathbf q,\mathbf t;\mathcal N)=\sum_{i\in\mathcal N}\bigl[p_i-c_iq_i^2-t_i(a_i-b_iq_i)\bigr]\cdot d_i(\mathbf p,\mathbf q,\mathbf t;\mathcal N).
--   $$
--   The module also names the exponent of Theorem 1(c) as a function of a duration $\tau$ of product $i$:
--   $$
--   \varphi_i(\tau)=\frac{b_i^2\tau^2}{4c_i}+\Bigl(s_i-a_i+\frac{\alpha_ib_i}{2c_i}\Bigr)\tau+\frac{\alpha_i^2}{4c_i}.
--   $$
--   These objects are the model of every result of §2.1 of the paper.
--
--   **Formalization Note** Products are `Fin N`, 0-based; the outside option is the `1 +` in the denominator, not an element of `Fin N`. The paper derives the choice probability from i.i.d. Gumbel utilities (McFadden 1974); here the closed-form formula (2) is the definition, and that derivation is not part of the mission. No sign restriction is placed on any parameter in the definitions; the theorems assume $c_i>0$ where needed.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), p. 7, eq. (2); p. 8 (costs $c_iq_i^2$ and $a_i-b_iq_i$); p. 9, eq. (3); p. 10, Theorem 1(c) (exponent)

import Mathlib

namespace PriceQualityService.Joint

/-- Attraction `exp(α_i q_i − p_i + t_i s_i)` of product `i` (the numerator of the MNL choice
probability (2), Wang, Ke & Cui, p. 7). Products are `Fin N`, 0-based: the paper's product `i` is
`⟨i - 1, _⟩`. The parameters are `α i` (quality sensitivity) and `s i` (service utility per unit
time); `p`, `q`, `t` are the price, quality and service-duration vectors. -/
noncomputable def attraction {N : ℕ} (α s p q t : Fin N → ℝ) (i : Fin N) : ℝ :=
  Real.exp (α i * q i - p i + t i * s i)

/-- MNL choice probability (2), p. 7:
`d_i(p, q, t; 𝒩) = exp(α_i q_i − p_i + t_i s_i) / (1 + ∑_{j∈𝒩} exp(α_j q_j − p_j + t_j s_j))`.
The outside option is not an element of `Fin N`; it is the `1 +` of the denominator. The paper
derives this formula from i.i.d. Gumbel utilities (McFadden 1974); that derivation is not part of
this definition, which takes the closed form as the model. -/
noncomputable def choiceProb {N : ℕ} (α s p q t : Fin N → ℝ) (i : Fin N) : ℝ :=
  attraction α s p q t i / (1 + ∑ j, attraction α s p q t j)

/-- Markup (profit margin) of product `i` in (3), p. 9: `p_i − c_i q_i² − t_i (a_i − b_i q_i)`,
price minus production cost `c_i q_i²` minus service cost `t_i (a_i − b_i q_i)`. -/
def markup {N : ℕ} (a b c p q t : Fin N → ℝ) (i : Fin N) : ℝ :=
  p i - c i * q i ^ 2 - t i * (a i - b i * q i)

/-- Total expected profit (3), p. 9, with market size normalized to one:
`Π(p, q, t; 𝒩) = ∑_{i∈𝒩} [p_i − c_i q_i² − t_i (a_i − b_i q_i)] · d_i(p, q, t; 𝒩)`. -/
noncomputable def profit {N : ℕ} (α a b c s p q t : Fin N → ℝ) : ℝ :=
  ∑ i, markup a b c p q t i * choiceProb α s p q t i

/-- Exponent of Theorem 1(c), p. 10, as a function of the duration `τ` of product `i`:
`b_i² τ²/(4c_i) + (s_i − a_i + α_i b_i/(2c_i)) τ + α_i²/(4c_i)`. -/
noncomputable def durationExponent {N : ℕ} (α a b c s : Fin N → ℝ) (i : Fin N) (τ : ℝ) : ℝ :=
  b i ^ 2 * τ ^ 2 / (4 * c i) + (s i - a i + α i * b i / (2 * c i)) * τ + α i ^ 2 / (4 * c i)

end PriceQualityService.Joint


