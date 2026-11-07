-- Prove2me | Definitions.Def_AvgCaseTI_pi1
-- name    : AvgCaseTI_pi1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:41:25.950903+00:00
-- url     : https://prove2.me/theorems/14282e9f-713b-41df-ae4c-5de2bd822ca1
-- title:
--   The limiting hull-one probability $\pi_1(q)$
-- statement:
--   For $q>1$,
--   $$
--   \pi_1(q)=\frac{1}{q-1}\prod_{j=1}^{\infty}\bigl(1-q^{-(2j-1)}\bigr).
--   $$
--   It is the limit, as $n\to\infty$, of the probability that a uniformly random $n$-dimensional subspace of $\mathrm M(n,q)$ has a one-dimensional hull (Proposition 3.3).
--
--   **Formalization Note** The infinite product is the infimum of its partial products $\prod_{j=1}^{m}(1-q^{-(2j-1)})$, which are positive and decreasing for $q>1$.
-- source:
--   Li, Li, Qiao, Tao, Wang, On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields, arXiv:2604.00591 (held version sha256 baf552e1…), Proposition 3.3, p.16 (PDF p.18)

import Mathlib

set_option autoImplicit false

namespace AvgCaseTI

/-- **The limiting hull-one probability `π₁(q) = (q − 1)^{−1} ∏_{j≥1} (1 − q^{−(2j−1)})`.**

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), Proposition 3.3, p.16
(PDF p.18).

**Formalization Note.** The infinite product is the infimum of its partial products
`∏_{j=1}^{m} (1 − q^{−(2j−1)})`, which are positive and decreasing for `q > 1`. -/
noncomputable def pi1 (q : ℝ) : ℝ :=
  (q - 1)⁻¹ * ⨅ m : ℕ, ∏ j ∈ Finset.range m, (1 - q ^ (-(2 * (j : ℤ) + 1)))

end AvgCaseTI


