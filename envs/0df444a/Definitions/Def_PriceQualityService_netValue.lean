-- Prove2me | Definitions.Def_PriceQualityService_netValue
-- name    : PriceQualityService_netValue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:36:55.852063+00:00
-- url     : https://prove2.me/theorems/8f42aaed-4a7b-4b52-9cbc-8c5c1eec6278
-- title:
--   Net value $\alpha_i q_i - c_i q_i^2 + t_i(s_i-(a_i-b_iq_i))$ (exponent of eq. (17))
-- statement:
--   The products are $\mathcal N=\{1,\dots,N\}$. Product $i$ has quality sensitivity $\alpha_i$, service utility per unit time $s_i$, production-cost coefficient $c_i$ and service-cost coefficients $a_i,b_i$; the firm chooses its price $p_i$, quality $q_i$ and service duration $t_i$.
--
--   The **net value** of product $i$ is
--
--   $$
--   w_i(\mathbf q,\mathbf t)=\alpha_iq_i-c_iq_i^2+t_i\bigl(s_i-(a_i-b_iq_i)\bigr),
--   $$
--
--   the deterministic utility the product would have if priced at its unit cost $c_iq_i^2+t_i(a_i-b_iq_i)$. It is the exponent of eq. (17) without the term $-r-1$, and drives the price-optimized profit.
--
--   **Formalization Note** Qualities and durations are free vectors; the paper's later substitution of the unconstrained optimal quality $q_i=(\alpha_i+t_ib_i)/(2c_i)$ is not built in.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript, SSRN 3766191 (MSOM 2020, doi:10.1287/msom.2020.0947), proof of Theorem 1 (App. B), p. 26, eq. (17) (exponent)

import Mathlib

namespace PriceQualityService

/-- **Net value of product `i` at quality `q_i` and duration `t_i`.**
Wang, Ke & Cui, *Product Price, Quality and Service Decisions under Consumer Choice Models*,
accepted manuscript, SSRN 3766191 (MSOM 2020, doi:10.1287/msom.2020.0947), proof of Theorem 1 (App. B), eq. (17), p. 26: the exponent
`α_i q_i − c_i q_i² + t_i (s_i − (a_i − b_i q_i)) − r − 1` without the term `− r − 1`.

`netValue α s a b c q t i = α i * q i - c i * q i ^ 2 + t i * (s i - (a i - b i * q i))`: the
deterministic utility of product `i` net of its production and service costs, i.e. the utility
at a price equal to unit cost.

**Formalization Note.** Quality and duration are free vectors; the paper's later substitution of
the unconstrained optimal quality `q_i = (α_i + t_i b_i)/(2 c_i)` is not built in. -/
def netValue {N : ℕ} (α s a b c q t : Fin N → ℝ) (i : Fin N) : ℝ :=
  α i * q i - c i * q i ^ 2 + t i * (s i - (a i - b i * q i))

end PriceQualityService


