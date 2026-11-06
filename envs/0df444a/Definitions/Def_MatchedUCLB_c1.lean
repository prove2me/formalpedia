-- Prove2me | Definitions.Def_MatchedUCLB_c1
-- name    : MatchedUCLB_c1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:27.581229+00:00
-- url     : https://prove2.me/theorems/c1f23c01-a786-4f65-a761-d5f4b59b2caf
-- title:
--   The constant $c_1=2^{-q-3}/q$
-- statement:
--   For the matched order $q=p+\nu$ (with $p\ge2$, $0<\nu\le1$), the construction uses the constant
--
--   $$
--   c_1=\frac{2^{-q-3}}{q} .
--   $$
--
--   It depends only on $q$, hence only on $p$ and $\nu$.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Sec. 4.3, p.8; Lemma 4.5(c), p.10

import Mathlib

namespace MatchedUCLB

/-- **The constant `c_1 = 2^{−q−3}/q`.** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, Sec. 4.3, p.8, and Lemma 4.5(c), p.10. Here `q = p + ν`.

**Formalization Note.** `q` is a real parameter; every power with exponent depending on `q` is
`Real.rpow`. The constant depends on `q` only. -/
noncomputable def c1 (q : ℝ) : ℝ :=
  (2 : ℝ) ^ (-q - 3) / q

end MatchedUCLB


