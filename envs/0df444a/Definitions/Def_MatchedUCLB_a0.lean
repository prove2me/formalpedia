-- Prove2me | Definitions.Def_MatchedUCLB_a0
-- name    : MatchedUCLB_a0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:23.858206+00:00
-- url     : https://prove2.me/theorems/a419e210-34d9-4d18-b582-0a29c98a5bc9
-- title:
--   The constant $a_0=\tfrac12(3/4)^{q-2}$
-- statement:
--   For the matched order $q=p+\nu$ (with $p\ge2$, $0<\nu\le1$), the construction uses the constant
--
--   $$
--   a_0=\frac12\Bigl(\frac34\Bigr)^{q-2} .
--   $$
--
--   It depends only on $q$, hence only on $p$ and $\nu$.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Eq. (4.6), p.6

import Mathlib

namespace MatchedUCLB

/-- **The constant `a_0 = ½ (3/4)^{q−2}`.** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, (4.6), p.6. Here `q = p + ν`.

**Formalization Note.** `q` is a real parameter; every power with exponent depending on `q` is
`Real.rpow`. The constant depends on `q` only. -/
noncomputable def a0 (q : ℝ) : ℝ :=
  1 / 2 * (3 / 4 : ℝ) ^ (q - 2)

end MatchedUCLB


