-- Prove2me | Definitions.Def_CVPricing_CertEquiv_Model
-- name    : CVPricing_CertEquiv_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T09:48:44.866758+00:00
-- url     : https://prove2.me/theorems/ad16a8cf-0dda-4a0e-b3cc-91ae63fa4483
-- title:
--   §2, p. 773 — the linear–Gaussian demand model, its standing assumptions, revenue and $p_{\mathrm{opt}}$
-- statement:
--   A monopolist sells a single product over discrete periods $t = 1, 2, \dots$. In each period it charges a price $p_t$ in the interval $[p_l, p_h]$ of acceptable prices, with $0 < p_l < p_h$, and observes a demand $d_t$. Proposition 1 concerns the special case $h(x) = x$, $v(x) = 1$ of the general model of §2: the demand at price $p$ is normally distributed with mean and variance
--
--   $$\mathbb E[D(p)] = a_0^{(0)} + a_1^{(0)} p, \qquad \operatorname{Var}[D(p)] = \sigma^2 .$$
--
--   The standing assumptions of §2 are imposed on the unknown parameters:
--
--   1. $\sigma > 0$, $a_0^{(0)} > 0$, $a_1^{(0)} < 0$ and $a_0^{(0)} + a_1^{(0)} p_h \ge 0$ (expected demand is decreasing and nonnegative on the price range);
--   2. the optimal price lies strictly between the extreme prices,
--   $$p_l < p_{\mathrm{opt}} < p_h, \qquad p_{\mathrm{opt}} = -\frac{a_0^{(0)}}{2 a_1^{(0)}} .$$
--
--   The expected single-period revenue at price $p$ under parameters $(a_0, a_1)$ is $r(p, a_0, a_1) = p\,(a_0 + a_1 p)$, and $p_{\mathrm{opt}}$ is its unique maximizer over $[p_l, p_h]$ at the true parameters.
--
--   These are the data every statement of the mission is written over.
--
--   **Formalization Note** For linear $h$, the paper's assumption that $r(\cdot, a_0, a_1)$ has a unique maximizer on $(p_l, p_h)$ with negative second derivative for all $(a_0, a_1)$ in an open neighbourhood $U$ of $a^{(0)}$ is equivalent to $p_l < p_{\mathrm{opt}} < p_h$; this is the field `opt_mem`. The law of the noise is not part of this structure: it is the referenced definition `RobustBooking.Shared.GaussianNoise`.
-- source:
--   den Boer, Zwart, Simultaneously Learning and Optimizing Using Controlled Variance Pricing, Management Science 60(3):770–783 (2014), p. 773 (PDF 5), §2, Eq. (1) and the standing assumptions; p. 775 (PDF 7), Proposition 1 (h(x) = x, v(x) = 1)

import Mathlib

namespace CVPricing.CertEquiv

/-- The linear–Gaussian special case of the pricing model of den Boer and Zwart (2014), §2,
p. 773, used by Proposition 1 (p. 775): expected demand `h(a₀ + a₁ p)` with `h(x) = x` and
variance `σ² v(·)` with `v ≡ 1`, so the demand at price `p` is `N(a₀ + a₁ p, σ²)`.

Fields are the standing assumptions of §2:
* the acceptable prices form `[p_l, p_h]` with `0 < p_l < p_h`;
* `σ > 0`, `a₀ > 0`, `a₁ < 0` and `a₀ + a₁ p_h ≥ 0`;
* the neighbourhood assumption, which for linear `h` says that the optimal price
  `p_opt = −a₀ / (2 a₁)` lies strictly between `p_l` and `p_h`. -/
structure Model where
  /-- the minimum acceptable price `p_l` -/
  pl : ℝ
  /-- the maximum acceptable price `p_h` -/
  ph : ℝ
  /-- the true intercept `a₀⁽⁰⁾` -/
  a₀ : ℝ
  /-- the true slope `a₁⁽⁰⁾` -/
  a₁ : ℝ
  /-- the demand standard deviation `σ` -/
  σ : ℝ
  pl_pos : 0 < pl
  pl_lt_ph : pl < ph
  σ_pos : 0 < σ
  a₀_pos : 0 < a₀
  a₁_neg : a₁ < 0
  demand_nonneg : 0 ≤ a₀ + a₁ * ph
  /-- `p_l < p_opt < p_h` with `p_opt = −a₀ / (2 a₁)` -/
  opt_mem : pl < -a₀ / (2 * a₁) ∧ -a₀ / (2 * a₁) < ph

/-- Expected single-period revenue `r(p, a₀, a₁) = p (a₀ + a₁ p)` (p. 773, with `h(x) = x`). -/
def revenue (a : ℝ × ℝ) (p : ℝ) : ℝ := p * (a.1 + a.2 * p)

/-- The optimal price `p_opt = −a₀⁽⁰⁾ / (2 a₁⁽⁰⁾)`, the maximizer of `p ↦ p (a₀ + a₁ p)` over
`[p_l, p_h]` (it lies in `(p_l, p_h)` by `Model.opt_mem`). -/
noncomputable def optPrice (M : Model) : ℝ := -M.a₀ / (2 * M.a₁)

end CVPricing.CertEquiv


