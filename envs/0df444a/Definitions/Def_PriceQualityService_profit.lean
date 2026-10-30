-- Prove2me | Definitions.Def_PriceQualityService_profit
-- name    : PriceQualityService_profit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:36:39.041583+00:00
-- url     : https://prove2.me/theorems/b0e3ceb5-5e00-45a3-abe3-fb0e6659efd4
-- title:
--   Total expected profit $\Pi(\mathbf p,\mathbf q,\mathbf t;\mathcal N)$ (eq. (3))
-- statement:
--   The products are $\mathcal N=\{1,\dots,N\}$. Product $i$ has quality sensitivity $\alpha_i$, service utility per unit time $s_i$, production-cost coefficient $c_i$ and service-cost coefficients $a_i,b_i$; the firm chooses its price $p_i$, quality $q_i$ and service duration $t_i$.
--
--   With the market size normalized to one, the firm's **total expected profit** is
--
--   $$
--   \Pi(\mathbf p,\mathbf q,\mathbf t;\mathcal N)=\sum_{i\in\mathcal N}\bigl[p_i-c_iq_i^2-t_i(a_i-b_iq_i)\bigr]\, d_i(\mathbf p,\mathbf q,\mathbf t;\mathcal N).
--   $$
--
--   It is the objective of the joint price, quality and service problems (4) and (7).
--
--   **Formalization Note** Durations form a vector $\mathbf t$; the uniform-duration problem (7) evaluates $\Pi$ at the constant vector $(t,\dots,t)$. For $N=0$ the profit is $0$.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript, SSRN 3766191 (MSOM 2020, doi:10.1287/msom.2020.0947), p. 9, eq. (3)

import Mathlib
import Definitions.Def_PriceQualityService_choiceProb
import Definitions.Def_PriceQualityService_margin

namespace PriceQualityService

/-- **Total expected profit `Π(p, q, t; 𝒩)`.**
Wang, Ke & Cui, *Product Price, Quality and Service Decisions under Consumer Choice Models*,
accepted manuscript, SSRN 3766191 (MSOM 2020, doi:10.1287/msom.2020.0947), eq. (3), p. 9:
`Π(p, q, t; 𝒩) = Σ_{i∈𝒩} [p_i − c_i q_i² − t_i (a_i − b_i q_i)] · d_i(p, q, t; 𝒩)`,
with the market size normalized to one.

**Formalization Note.** The offer set is all of `Fin N` and durations are a vector `t`; problem
(7) evaluates this profit at the constant vector `fun _ => t`. For `N = 0` the profit is `0`. -/
noncomputable def profit {N : ℕ} (α s a b c p q t : Fin N → ℝ) : ℝ :=
  ∑ i, margin a b c p q t i * choiceProb α s p q t i

end PriceQualityService


