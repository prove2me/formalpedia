-- Prove2me | Definitions.Def_MatchedUCLB_KConst
-- name    : MatchedUCLB_KConst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:29:20.325384+00:00
-- url     : https://prove2.me/theorems/53f26a68-70e0-4584-b74d-04db96d0e253
-- title:
--   The chain constant $K=5^{(q-1)/2}/c_0$
-- statement:
--   For the matched order $q=p+\nu$ (with $p\ge2$, $0<\nu\le1$), the construction uses the constant
--
--   $$
--   K=\frac{5^{\frac{q-1}{2}}}{c_0} .
--   $$
--
--   It depends only on $q$, hence only on $p$ and $\nu$.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Lemma 4.5, p.10; Eq. (4.16), p.10

import Mathlib
import Definitions.Def_MatchedUCLB_c0

namespace MatchedUCLB

/-- **The constant `K = 5^{(q−1)/2}/c_0`.** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, Lemma 4.5, p.10 (and (4.16)). Here `q = p + ν`.

**Formalization Note.** `q` is a real parameter; every power with exponent depending on `q` is
`Real.rpow`. The constant depends on `q` only. -/
noncomputable def KConst (q : ℝ) : ℝ :=
  (5 : ℝ) ^ ((q - 1) / 2) / c0 q

end MatchedUCLB


