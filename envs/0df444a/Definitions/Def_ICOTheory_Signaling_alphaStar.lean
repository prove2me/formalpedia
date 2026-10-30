-- Prove2me | Definitions.Def_ICOTheory_Signaling_alphaStar
-- name    : ICOTheory_Signaling_alphaStar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:03:35.860908+00:00
-- url     : https://prove2.me/theorems/4f538098-5733-4da0-b309-e40ab234fe7b
-- title:
--   The least-cost separating threshold $\alpha^*$, display (25)
-- statement:
--   In the signaling model of Chod and Lyandres, an entrepreneur of high ($H$) or low ($L$) quality sells a fraction $\alpha$ of her venture's equity or tokens. The venture's revenue is $R_i=\xi_i^2/4$, where $\xi_i^2$ is normally distributed with mean $\mu_i$ and standard deviation $\sigma$, $i\in\{H,L\}$, and $\mu_H>\mu_L$; the entrepreneur has CARA utility with risk-aversion coefficient $\gamma>0$.
--
--   For real numbers $\mu_H,\mu_L,\sigma,\gamma$ define
--
--   $$
--   \alpha^*(\mu_H,\mu_L,\sigma,\gamma)=\frac{4\mu_H-4\mu_L+\sigma^2\gamma-\sqrt{(4\mu_H-4\mu_L)(4\mu_H-4\mu_L+2\sigma^2\gamma)}}{\sigma^2\gamma}.
--   $$
--
--   This is display (25). In the least-cost separating equilibrium of Proposition 5, $\alpha^*$ is the belief threshold and the share the high type sells: the largest share it can sell without the low type wanting to imitate it.
--
--   **Formalization Note** The formula is transcribed literally. It is meaningful for $\mu_L<\mu_H$, $\sigma>0$, $\gamma>0$; outside that domain Lean returns $\sqrt{x}=0$ for $x<0$ and $x/0=0$, so every statement about $\alpha^*$ carries these hypotheses.
-- source:
--   Chod, Lyandres, A Theory of ICOs: Diversification, Agency, and Information Asymmetry, SSRN 3159528 (December 14, 2019), §4, display (25), p. 20

import Mathlib

namespace ICOTheory.Signaling

/-- **The least-cost separating threshold `α*`, display (25).**
Chod, Lyandres, *A Theory of ICOs: Diversification, Agency, and Information Asymmetry*,
SSRN 3159528 (December 14, 2019), §4, display (25), p. 20:
`α* ≡ (4μ_H − 4μ_L + σ²γ − √((4μ_H − 4μ_L)(4μ_H − 4μ_L + 2σ²γ))) / (σ²γ)`.

Here `μH`, `μL` are the means of `ξ_H²`, `ξ_L²` (the high and the low type's revenue is
`R_i = ξ_i²/4` with `ξ_i² ~ N(μ_i, σ)`, p. 18), `σ` is the common standard deviation and `γ`
the entrepreneur's coefficient of absolute risk aversion (Assumption 1(i), p. 12). `α*` is the
largest share of the venture the high type can sell without being imitated by the low type
(p. 21).

**Formalization Note.** The formula is transcribed literally. It is meaningful (and lies in
`(0, 1)`) for `μL < μH`, `0 < σ`, `0 < γ`, the domain of §4; outside it Lean's `Real.sqrt` of a
negative number is `0` and division by `0` is `0`, so every statement about `alphaStar`
carries these hypotheses. -/
noncomputable def alphaStar (μH μL σ γ : ℝ) : ℝ :=
  (4 * μH - 4 * μL + σ ^ 2 * γ -
      Real.sqrt ((4 * μH - 4 * μL) * (4 * μH - 4 * μL + 2 * σ ^ 2 * γ))) / (σ ^ 2 * γ)

end ICOTheory.Signaling


