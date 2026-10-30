-- Prove2me | Definitions.Def_InfoBargaining_SellerPayoff_postMeanLaw
-- name    : InfoBargaining_SellerPayoff_postMeanLaw
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:12:33.750428+00:00
-- url     : https://prove2.me/theorems/942f089d-2c07-440a-b1bc-a8093ab19f00
-- title:
--   Law of the posterior mean $G(\cdot,\alpha)$
-- statement:
--   A seller and a buyer may trade one unit. Trade costs the seller $c>0$ and is worth $u$ to the buyer, who does not know $u$; the prior law of $u$ is $F$ with mean $\hat u>0$. Before negotiating, the buyer buys a truth-or-noise signal of informativeness $\alpha\in[\underline\alpha,\bar\alpha]\subseteq(0,1)$; its posterior mean is $v=\alpha w+(1-\alpha)\hat u$, whose law is $G(v,\alpha)=F\big((v-(1-\alpha)\hat u)/\alpha\big)$. The parties then split the net surplus $v-c$ in proportion to their bargaining powers $\theta_s,\theta_b\in(0,1)$, $\theta_s+\theta_b=1$.
--
--   Since the signal $w$ has the prior law marginally, the posterior mean $v=\alpha w+(1-\alpha)\hat u$ has the law of $\alpha u+(1-\alpha)\hat u$ with $u\sim\mu$. This definition is that law,
--
--   $$
--   G(\cdot,\alpha)=\text{law of }\ \alpha u+(1-\alpha)\hat u,\qquad u\sim\mu,\ \hat u=\int u\,d\mu,
--   $$
--
--   whose CDF is $G(v,\alpha)=F\big((v-(1-\alpha)\hat u)/\alpha\big)$ for $\alpha>0$.
--
--   **Formalization Note** The Bayesian update, the disclosure stage and the bargaining protocol (pp. 7–9) are the paper's own reduction to this law and are not formalized.
-- source:
--   Guo, Gathering Information before Negotiation, SSRN 3930651 (manuscript of 15 Feb 2022), §2, unnumbered, p. 7 ("the distribution of the posterior mean is G(v, α) ≡ F((v − (1 − α)û)/α)")

import Mathlib
import Definitions.Def_InfoBargaining_SellerPayoff_priorMean

open MeasureTheory

namespace InfoBargaining.SellerPayoff

/-- **The law of the buyer's posterior mean `v`, with CDF `G(v, α)`.**
Guo, *Gathering Information before Negotiation*, SSRN 3930651 (manuscript of 15 Feb 2022),
§2, p. 7: "what matters is only the posterior mean v ≡ αw + (1 − α)û … It follows that the
distribution of the posterior mean is G(v, α) ≡ F((v − (1 − α)û)/α)".

Under the truth-or-noise signal the signal `w` has the prior law `F` marginally, so `v` is the
image of the prior `μ` under `u ↦ αu + (1 − α)û`, with `û = priorMean μ`.

**Formalization Note.** `G(·, α)` is the CDF of this pushforward measure. The Bayesian update,
the disclosure stage and the bargaining split (pp. 7–9) are the paper's own reduction to this
law and are not formalized. -/
noncomputable def postMeanLaw (μ : Measure ℝ) (α : ℝ) : Measure ℝ :=
  μ.map (fun u => α * u + (1 - α) * priorMean μ)

end InfoBargaining.SellerPayoff


