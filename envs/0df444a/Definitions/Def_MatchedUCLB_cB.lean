-- Prove2me | Definitions.Def_MatchedUCLB_cB
-- name    : MatchedUCLB_cB
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:24.998601+00:00
-- url     : https://prove2.me/theorems/b57883ed-0ae4-46b8-801d-8bb6b621ef9a
-- title:
--   The uniform-convexity constant $c_B=1/(2q\cdot16^{q-2})$
-- statement:
--   For the matched order $q=p+\nu$ (with $p\ge2$, $0<\nu\le1$), the construction uses the constant
--
--   $$
--   c_B=\frac{1}{2q\cdot16^{q-2}} .
--   $$
--
--   It depends only on $q$, hence only on $p$ and $\nu$.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Lemma 4.3(a), p.6; Lemma E.9, p.90

import Mathlib

namespace MatchedUCLB

/-- **The constant `c_B = 1/(2q·16^{q−2})`.** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, Lemma 4.3(a), p.6, and Lemma E.9, p.90. Here `q = p + ν`.

**Formalization Note.** `q` is a real parameter; every power with exponent depending on `q` is
`Real.rpow`. The constant depends on `q` only. -/
noncomputable def cB (q : ℝ) : ℝ :=
  1 / (2 * q * (16 : ℝ) ^ (q - 2))

end MatchedUCLB


