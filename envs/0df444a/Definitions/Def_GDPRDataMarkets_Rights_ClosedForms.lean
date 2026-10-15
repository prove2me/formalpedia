-- Prove2me | Definitions.Def_GDPRDataMarkets_Rights_ClosedForms
-- name    : GDPRDataMarkets_Rights_ClosedForms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T22:59:25.855842+00:00
-- url     : https://prove2.me/theorems/abf0d4bb-505f-4da9-86fa-5ea37825272c
-- title:
--   Eq. (4) and Appendix p. 46 — the opt-in threshold v*_M(p₁), the constants v₁*, P₁* and the reduced profits
-- statement:
--   This file names the closed-form quantities of §3.1 and of the proof of Proposition 1, in the parameters of the model ($\mu$, $\sigma$, $\delta$, $c$).
--
--   1. The **opt-in threshold** of eq. (4):
--   $$v^*_M(p_1)=\max\Big\{\frac{c}{\delta\sigma},\ \frac{p_1+c}{1+\delta\sigma}\Big\}.$$
--   2. The constants of the Appendix (p. 46):
--   $$v_1^*=\max\Big\{\frac{1+\delta\sigma+(1+\delta)c}{2+\delta+\delta\mu+\delta\sigma},\ \frac{c}{\delta\sigma}\Big\},\qquad P_1^*=\max\Big\{\frac{(1+\delta\sigma)^2-(1+\delta\mu-\delta^2\sigma)c}{2+\delta+\delta\mu+\delta\sigma},\ \frac{c}{\delta\sigma}\Big\}.$$
--   3. The **reduced second-period objective** of p. 14 for an opt-in threshold $w\in[0,1]$ and basic price $q$:
--   $$\pi_2(w,q)=\int_w^1\big((\mu-\sigma)v+\min\{v,q\}-c\big)\,dv\;+\;q\cdot\big|\{v\in[0,w):\ v\ge q\}\big|,$$
--   where $|\cdot|$ is Lebesgue measure: the first term is revenue from the opted-in consumers at the personalized price of eq. (2), the second from the remaining consumers who buy the basic good.
--   4. The **reduced first-period profit** of p. 15. With $w(p_1)=\min\{1,v^*_M(p_1)\}$,
--   $$\pi(p_1)=p_1\big(1-\min\{w,\max\{p_1,0\}\}\big)+\frac{\delta}{2}\Big(1-\min\Big\{\frac12,w^2\Big\}\Big)+\frac{\delta}{2}(\mu-\sigma)(1-w^2)-\delta(1-w)c.$$
--
--   These are the quantities in which the paper states and proves Proposition 1.
--
--   **Formalization Note** The paper's display on p. 15 is written for $p_1\ge 0$ and $v^*_M(p_1)\le 1$. Here $v^*_M$ is clipped to $[0,1]$ and $p_1$ is clipped below at $0$ inside the minimum, so that $\pi(p_1)$ equals the firm's equilibrium profit for every real $p_1$ (milestone "reduced first-period profit"). On the paper's range the two expressions coincide. The second term of $\pi_2$ counts the non-opted buyers $\{v\in[0,w): v\ge q\}$ instead of the page's $\max\{w-q,0\}$, which differs only for $q<0$.
-- source:
--   Ke, Sudhir, Privacy Rights and Data Security: GDPR and Personal Data Markets, SSRN 3643979 (pdfTeX build 2022-09-14), p. 14, eqs. (3)–(4); p. 15, first-period problem; p. 46, definitions of v₁* and P₁*

import Mathlib
import Definitions.Def_GDPRDataMarkets_Rights_Model

namespace GDPRDataMarkets.Rights

open MeasureTheory

noncomputable section

/-- The opt-in threshold of eq. (4), p. 14: `v*_M(p₁) = max{c/(δσ), (p₁ + c)/(1 + δσ)}`. -/
def vStar (P : Params) (p1 : ℝ) : ℝ :=
  max (P.c / (P.d * P.sigma)) ((p1 + P.c) / (1 + P.d * P.sigma))

/-- `v₁* = max{(1 + δσ + (1 + δ)c)/(2 + δ + δμ + δσ), c/(δσ)}` (Appendix, p. 46). -/
def v1star (P : Params) : ℝ :=
  max ((1 + P.d * P.sigma + (1 + P.d) * P.c) / (2 + P.d + P.d * P.mu + P.d * P.sigma))
    (P.c / (P.d * P.sigma))

/-- `P₁* = max{((1 + δσ)² − (1 + δμ − δ²σ)c)/(2 + δ + δμ + δσ), c/(δσ)}` (Appendix, p. 46). -/
def P1star (P : Params) : ℝ :=
  max (((1 + P.d * P.sigma) ^ 2 - (1 + P.d * P.mu - P.d ^ 2 * P.sigma) * P.c)
      / (2 + P.d + P.d * P.mu + P.d * P.sigma))
    (P.c / (P.d * P.sigma))

/-- The second-period objective of p. 14 for an opt-in threshold `w ∈ [0, 1]` and basic price `q`:
`∫_w^1 r*_M(v, q) dv` with `r*_M(v, q) = (μ − σ)v + min{v, q} − c` (eq. (2)), plus `q` times the mass
of the consumers in `[0, w)` (who did not opt in) with `v ≥ q`. -/
def profit2Red (P : Params) (w q : ℝ) : ℝ :=
  (∫ v in w..1, ((P.mu - P.sigma) * v + min v q - P.c))
    + q * (volume {v | v ∈ Set.Ico (0 : ℝ) w ∧ q ≤ v}).toReal

/-- The opt-in threshold clipped to the consumer interval: `min{1, v*_M(p₁)}`. -/
def wStar (P : Params) (p1 : ℝ) : ℝ := min 1 (vStar P p1)

/-- The reduced first-period profit of p. 15,
`p₁(1 − min{v*, p₁}) + (δ/2)(1 − min{1/2, v*²}) + (δ/2)(μ − σ)(1 − v*²) − δ(1 − v*)c`,
with `v*` clipped to `[0, 1]` (`wStar`) and `p₁` clipped below at `0` inside the `min`, so that the
formula is the firm's profit for every real `p₁`. -/
def profitRed (P : Params) (p1 : ℝ) : ℝ :=
  p1 * (1 - min (wStar P p1) (max p1 0))
    + P.d / 2 * (1 - min (1 / 2) (wStar P p1 ^ 2))
    + P.d / 2 * (P.mu - P.sigma) * (1 - wStar P p1 ^ 2)
    - P.d * (1 - wStar P p1) * P.c

end

end GDPRDataMarkets.Rights


