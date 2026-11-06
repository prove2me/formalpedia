-- Prove2me | Definitions.Def_MatchedUCLB_aQ
-- name    : MatchedUCLB_aQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:24.988459+00:00
-- url     : https://prove2.me/theorems/1995ae6d-f16a-4e95-a366-b2a25760bd70
-- title:
--   The exponent $a_q=(3q-2)/2$
-- statement:
--   For the matched order $q=p+\nu$ (with $p\ge2$, $0<\nu\le1$), the construction uses the constant
--
--   $$
--   a_q=\frac{3q-2}{2} .
--   $$
--
--   It depends only on $q$, hence only on $p$ and $\nu$.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Eq. (4.15), p.9

import Mathlib

namespace MatchedUCLB

/-- **The constant `a_q = (3q−2)/2`.** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, (4.15), p.9. Here `q = p + ν`.

**Formalization Note.** `q` is a real parameter; every power with exponent depending on `q` is
`Real.rpow`. The constant depends on `q` only. -/
noncomputable def aQ (q : ℝ) : ℝ :=
  (3 * q - 2) / 2

end MatchedUCLB


