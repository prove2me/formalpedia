-- Prove2me | Definitions.Def_MatchedUCLB_c0
-- name    : MatchedUCLB_c0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:30.330846+00:00
-- url     : https://prove2.me/theorems/862f778e-34b3-4710-8f60-bd06801afd97
-- title:
--   The constant $c_0=2^{-q-3}/q$
-- statement:
--   For the matched order $q=p+\nu$ (with $p\ge2$, $0<\nu\le1$), the construction uses the constant
--
--   $$
--   c_0=\frac{2^{-q-3}}{q} .
--   $$
--
--   It depends only on $q$, hence only on $p$ and $\nu$.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Sec. 4.3, p.8

import Mathlib

namespace MatchedUCLB

/-- **The constant `c_0 = 2^{−q−3}/q`.** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, Sec. 4.3, p.8 ("with `c_0 = c_1 = 2^{−q−3}/q`"). Here `q = p + ν`.

**Formalization Note.** `q` is a real parameter; every power with exponent depending on `q` is
`Real.rpow`. The constant depends on `q` only. -/
noncomputable def c0 (q : ℝ) : ℝ :=
  (2 : ℝ) ^ (-q - 3) / q

end MatchedUCLB


