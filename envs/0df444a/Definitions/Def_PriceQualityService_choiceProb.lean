-- Prove2me | Definitions.Def_PriceQualityService_choiceProb
-- name    : PriceQualityService_choiceProb
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:35:45.315362+00:00
-- url     : https://prove2.me/theorems/4fb2b3aa-bd46-4812-893f-3b40a90ea265
-- title:
--   MNL choice probability $d_i(\mathbf p,\mathbf q,\mathbf t;\mathcal N)$ (eq. (2))
-- statement:
--   The products are $\mathcal N=\{1,\dots,N\}$. Product $i$ has quality sensitivity $\alpha_i$, service utility per unit time $s_i$, production-cost coefficient $c_i$ and service-cost coefficients $a_i,b_i$; the firm chooses its price $p_i$, quality $q_i$ and service duration $t_i$.
--
--   With i.i.d. Gumbel noise and an outside option of utility $U_0=\xi_0$, the probability that a consumer buys product $i$ is the **multinomial logit (MNL)** probability
--
--   $$
--   d_i(\mathbf p,\mathbf q,\mathbf t;\mathcal N)=\frac{\exp(\alpha_i q_i-p_i+t_is_i)}{1+\sum_{j\in\mathcal N}\exp(\alpha_j q_j-p_j+t_js_j)} .
--   $$
--
--   The no-purchase probability is $1-\sum_{i}d_i$. These probabilities are the market shares entering the profit (3).
--
--   **Formalization Note** The offer set is all of `Fin N`; the denominator is at least $1$, so the division is always well defined.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript, SSRN 3766191 (MSOM 2020, doi:10.1287/msom.2020.0947), p. 7, eq. (2)

import Mathlib
import Definitions.Def_PriceQualityService_utility

namespace PriceQualityService

/-- **MNL choice probability of product `i`.**
Wang, Ke & Cui, *Product Price, Quality and Service Decisions under Consumer Choice Models*,
accepted manuscript, SSRN 3766191 (MSOM 2020, doi:10.1287/msom.2020.0947), eq. (2), p. 7:
`d_i(p, q, t; 𝒩) = exp(α_i q_i − p_i + t_i s_i) / (1 + Σ_{j∈𝒩} exp(α_j q_j − p_j + t_j s_j))`.

The denominator's `1` is the outside option, whose utility is normalized to `U_0 = ξ_0`; the
no-purchase probability is `1 − Σ_i d_i`.

**Formalization Note.** The offer set is all of `Fin N`; durations are a vector `t`. The
denominator is at least `1`, so no division by zero occurs. -/
noncomputable def choiceProb {N : ℕ} (α s p q t : Fin N → ℝ) (i : Fin N) : ℝ :=
  Real.exp (utility α s p q t i) / (1 + ∑ j, Real.exp (utility α s p q t j))

end PriceQualityService


