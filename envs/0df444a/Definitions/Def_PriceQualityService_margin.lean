-- Prove2me | Definitions.Def_PriceQualityService_margin
-- name    : PriceQualityService_margin
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:36:00.040979+00:00
-- url     : https://prove2.me/theorems/0e49486b-2603-47f3-b627-de137e0bb55d
-- title:
--   Per-unit margin $p_i - c_i q_i^2 - t_i(a_i - b_i q_i)$ (bracket of eq. (3))
-- statement:
--   The products are $\mathcal N=\{1,\dots,N\}$. Product $i$ has quality sensitivity $\alpha_i$, service utility per unit time $s_i$, production-cost coefficient $c_i$ and service-cost coefficients $a_i,b_i$; the firm chooses its price $p_i$, quality $q_i$ and service duration $t_i$.
--
--   The **per-unit margin** of product $i$ is
--
--   $$
--   m_i(\mathbf p,\mathbf q,\mathbf t)=p_i-c_iq_i^2-t_i(a_i-b_iq_i),
--   $$
--
--   price minus the production cost $c_iq_i^2$ minus the service cost, which accrues at rate $a_i-b_iq_i$ per unit time over the duration $t_i$ (p. 8).
--
--   **Formalization Note** No sign is imposed on $b_i$ (the paper's three scenarios $b_i>0$, $b_i<0$, $b_i=0$ are all covered) or on $c_i$.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript, SSRN 3766191 (MSOM 2020, doi:10.1287/msom.2020.0947), p. 9, eq. (3) (bracket); costs defined on p. 8

import Mathlib

namespace PriceQualityService

/-- **Per-unit margin of product `i`.**
Wang, Ke & Cui, *Product Price, Quality and Service Decisions under Consumer Choice Models*,
accepted manuscript, SSRN 3766191 (MSOM 2020, doi:10.1287/msom.2020.0947), the bracket of eq. (3), p. 9:
`p_i − c_i q_i² − t_i (a_i − b_i q_i)`.

Price minus the production cost `c_i q_i²` (p. 8) minus the service cost: `a_i − b_i q_i` per unit
time (p. 8) over the service duration `t_i`.

**Formalization Note.** No sign is imposed on `b i`: the paper's three scenarios `b_i > 0`,
`b_i < 0`, `b_i = 0` (pp. 8–9) are all covered, and `c i` is not required to be positive. -/
def margin {N : ℕ} (a b c p q t : Fin N → ℝ) (i : Fin N) : ℝ :=
  p i - c i * q i ^ 2 - t i * (a i - b i * q i)

end PriceQualityService


