-- Prove2me | Definitions.Def_PriceQualityService_qualityDomain
-- name    : PriceQualityService_qualityDomain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:38:00.677749+00:00
-- url     : https://prove2.me/theorems/c983192d-ebf9-44a3-baf2-a67e7587e6a5
-- title:
--   Quality domain of the model (pp. 8–9)
-- statement:
--   The products are $\mathcal N=\{1,\dots,N\}$. Product $i$ has quality sensitivity $\alpha_i$, service utility per unit time $s_i$, production-cost coefficient $c_i$ and service-cost coefficients $a_i,b_i$; the firm chooses its price $p_i$, quality $q_i$ and service duration $t_i$.
--
--   The **quality domain** is the set of quality vectors with
--
--   $$
--   q_i\ge 0\quad\text{for all } i,\qquad q_i<\frac{a_i}{b_i}\quad\text{whenever } b_i>0 .
--   $$
--
--   For $b_i>0$ (scenario (1), service cost decreasing in quality) the paper normalizes the lowest quality to zero and lets $q_i$ vary in $[0,a_i/b_i)$, which keeps the service cost rate $a_i-b_iq_i$ positive; for $b_i<0$ (scenario (2)) it normalizes the lowest quality to zero.
--
--   **Formalization Note** For $b_i=0$ (scenario (3)) the page states no restriction; this definition reads it as $q_i\ge 0$, like the other two scenarios. The mission's main theorem is stated for an arbitrary quality set, so it covers this domain under either reading.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript, SSRN 3766191 (MSOM 2020, doi:10.1287/msom.2020.0947), pp. 8–9, scenarios (1)–(3)

import Mathlib

namespace PriceQualityService

/-- **The quality domain of the model.**
Wang, Ke & Cui, *Product Price, Quality and Service Decisions under Consumer Choice Models*,
accepted manuscript, SSRN 3766191 (MSOM 2020, doi:10.1287/msom.2020.0947), pp. 8–9: for `b_i > 0` (scenario (1)), "`q_i ≥ 0`, and it varies in `[0, a_i/b_i)`";
for `b_i < 0` (scenario (2)), "the lowest possible quality level is zero"; for `b_i = 0`
(scenario (3)) the page states no restriction.

`qualityDomain a b = {q | ∀ i, 0 ≤ q i ∧ (0 < b i → q i < a i / b i)}`.

**Formalization Note.** The scenario `b_i = 0` is read with `q_i ≥ 0` (normalizing the lowest
quality to zero, as in the other two scenarios). The mission's main theorem is stated for an
arbitrary quality set, so it covers this domain under either reading of scenario (3). -/
def qualityDomain {N : ℕ} (a b : Fin N → ℝ) : Set (Fin N → ℝ) :=
  {q | ∀ i, 0 ≤ q i ∧ (0 < b i → q i < a i / b i)}

end PriceQualityService


