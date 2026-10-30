-- Prove2me | Definitions.Def_PriceQualityService_yValue
-- name    : PriceQualityService_yValue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:37:28.766086+00:00
-- url     : https://prove2.me/theorems/dd83e351-9e65-4df6-b1bf-d44f53727408
-- title:
--   Aggregate attraction $y=\sum_i e^{w_i}$ at a fixed quality vector (p. 30)
-- statement:
--   The products are $\mathcal N=\{1,\dots,N\}$. Product $i$ has quality sensitivity $\alpha_i$, service utility per unit time $s_i$, production-cost coefficient $c_i$ and service-cost coefficients $a_i,b_i$; the firm chooses its price $p_i$, quality $q_i$ and service duration $t_i$.
--
--   For qualities $\mathbf q$ and durations $\mathbf t$, the **aggregate attraction** is
--
--   $$
--   y(\mathbf q,\mathbf t)=\sum_{i\in\mathcal N}\exp\Bigl(\alpha_iq_i-c_iq_i^2+t_i\bigl(s_i-(a_i-b_iq_i)\bigr)\Bigr).
--   $$
--
--   In the proof of Theorem 3 the paper defines $y=\sum_{i}\exp\bigl(b_i^2t^2/(4c_i)+(s_i-a_i+\alpha_ib_i/(2c_i))t+\alpha_i^2/(4c_i)\bigr)$, the numerator of the right-hand side of eq. (25); that is exactly $y(\mathbf q,(t,\dots,t))$ at the unconstrained optimal quality $q_i=(\alpha_i+tb_i)/(2c_i)$.
--
--   **Formalization Note** The quality vector is kept free so that the maximization over quality can be restricted to any feasible quality set.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript, SSRN 3766191 (MSOM 2020, doi:10.1287/msom.2020.0947), proof of Theorem 3 (App. B), p. 30 (definition of y), and eq. (25), p. 29

import Mathlib
import Definitions.Def_PriceQualityService_netValue

namespace PriceQualityService

/-- **The aggregate attraction `y` at a fixed quality vector.**
Wang, Ke & Cui, *Product Price, Quality and Service Decisions under Consumer Choice Models*,
accepted manuscript, SSRN 3766191 (MSOM 2020, doi:10.1287/msom.2020.0947), proof of Theorem 3 (App. B), p. 30:
`y = Σ_{i∈𝒩} exp(b_i² t²/(4c_i) + (s_i − a_i + α_i b_i/(2c_i)) t + α_i²/(4c_i))`, the numerator of
the right-hand side of eq. (25).

Here `yValue α s a b c q t = Σ_i exp(α_i q_i − c_i q_i² + t_i (s_i − (a_i − b_i q_i)))`.

**Formalization Note.** The paper's `y` is this sum evaluated at the unconstrained optimal quality
`q_i = (α_i + t b_i)/(2c_i)` (substituting it gives exactly the displayed exponent). This
definition keeps the quality vector `q` free, so that the maximization over quality can be
restricted to any feasible set; it is the paper's `y` when `q` is that point. -/
noncomputable def yValue {N : ℕ} (α s a b c q t : Fin N → ℝ) : ℝ :=
  ∑ i, Real.exp (netValue α s a b c q t i)

end PriceQualityService


