-- Prove2me | Definitions.Def_PriceQualityService_optPrice
-- name    : PriceQualityService_optPrice
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:37:45.780961+00:00
-- url     : https://prove2.me/theorems/9e4fa262-a230-4f06-97c3-9b6a2ec49966
-- title:
--   Equal-markup price $p_i = 1 + r + c_iq_i^2 + t_i(a_i-b_iq_i)$ (p. 26)
-- statement:
--   The products are $\mathcal N=\{1,\dots,N\}$. Product $i$ has quality sensitivity $\alpha_i$, service utility per unit time $s_i$, production-cost coefficient $c_i$ and service-cost coefficients $a_i,b_i$; the firm chooses its price $p_i$, quality $q_i$ and service duration $t_i$.
--
--   For a real number $r$, the **equal-markup price** of product $i$ is
--
--   $$
--   \hat p_i(r)=1+r+c_iq_i^2+t_i(a_i-b_iq_i),
--   $$
--
--   unit cost plus the common markup $1+r$. In the proof of Theorem 1 the paper shows that, for a given profit level $r$, this price maximizes each product's contribution; with $r$ the optimal profit it is the optimal price.
--
--   **Formalization Note** $r$ is a free parameter here; theorems supply the root of eq. (17) as a hypothesis.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript, SSRN 3766191 (MSOM 2020, doi:10.1287/msom.2020.0947), proof of Theorem 1 (App. B), p. 26 (maximizer of h_i(r, p_i)); also p. 15

import Mathlib

namespace PriceQualityService

/-- **The equal-markup price `p_i = 1 + c_i q_i² + t_i (a_i − b_i q_i) + r`.**
Wang, Ke & Cui, *Product Price, Quality and Service Decisions under Consumer Choice Models*,
accepted manuscript, SSRN 3766191 (MSOM 2020, doi:10.1287/msom.2020.0947), proof of Theorem 1 (App. B), p. 26: "it achieves its maximum at
`p_i = 1 + c_i q_i² + t_i(a_i − b_i q_i) + r`".

The price of product `i` equals its unit cost plus the common markup `1 + r`, where `r` is the
profit level (the root of eq. (17) at optimality).

**Formalization Note.** `r` is a free real parameter here; the theorems pass the root of (17)
as a hypothesis. -/
def optPrice {N : ℕ} (a b c q t : Fin N → ℝ) (r : ℝ) (i : Fin N) : ℝ :=
  1 + r + c i * q i ^ 2 + t i * (a i - b i * q i)

end PriceQualityService


