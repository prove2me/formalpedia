-- Prove2me | Definitions.Def_PriceQualityService_utility
-- name    : PriceQualityService_utility
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:35:09.033964+00:00
-- url     : https://prove2.me/theorems/bff44b18-afc9-4bbc-ae3f-c0df3f5e06cc
-- title:
--   Deterministic utility $\alpha_i q_i - p_i + t_i s_i$ (eq. (1))
-- statement:
--   The products are $\mathcal N=\{1,\dots,N\}$. Product $i$ has quality sensitivity $\alpha_i$, service utility per unit time $s_i$, production-cost coefficient $c_i$ and service-cost coefficients $a_i,b_i$; the firm chooses its price $p_i$, quality $q_i$ and service duration $t_i$.
--
--   The **deterministic utility** of product $i$ is
--
--   $$
--   u_i(p,q,t)=\alpha_i q_i - p_i + t_i s_i ,
--   $$
--
--   the utility $U_i=\alpha_i q_i-p_i+t_is_i+\xi_i$ of eq. (1) without the Gumbel noise $\xi_i$. Utility increases in quality and in service duration and decreases in price.
--
--   **Formalization Note** Products are indexed by `Fin N`; all quantities are real vectors and no sign assumption is built in.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript, SSRN 3766191 (MSOM 2020, doi:10.1287/msom.2020.0947), p. 6, eq. (1)

import Mathlib

namespace PriceQualityService

/-- **Deterministic utility of product `i`.**
Wang, Ke & Cui, *Product Price, Quality and Service Decisions under Consumer Choice Models*,
accepted manuscript, SSRN 3766191 (MSOM 2020, doi:10.1287/msom.2020.0947), eq. (1), p. 6:
`U_i = α_i q_i − p_i + t_i s_i + ξ_i`.

`utility α s p q t i = α i * q i - p i + t i * s i` is the deterministic part of `U_i` (the
utility without the Gumbel noise `ξ_i`), for product `i` with quality sensitivity `α i`,
service utility per unit time `s i`, price `p i`, quality `q i` and service duration `t i`.

**Formalization Note.** The products `𝒩 = {1, …, N}` are `Fin N`; every parameter and decision
is a vector `Fin N → ℝ`. The paper's sign assumptions (`α_i > 0`, `s_i > 0`) are not part of
the definition. -/
def utility {N : ℕ} (α s p q t : Fin N → ℝ) (i : Fin N) : ℝ :=
  α i * q i - p i + t i * s i

end PriceQualityService


