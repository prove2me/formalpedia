-- Prove2me | Definitions.Def_MatchedUCLB_betaQ
-- name    : MatchedUCLB_betaQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:30:35.344115+00:00
-- url     : https://prove2.me/theorems/a9d8f250-45b5-4904-b177-7b4cf3d6aa27
-- title:
--   The constant $\beta_q=1/q+a_{\mathrm{lift}}\theta^2$
-- statement:
--   For the matched order $q=p+\nu$ (with $p\ge2$, $0<\nu\le1$), the construction uses the constant
--
--   $$
--   \beta_q=\frac1q+a_{\mathrm{lift}}\theta^2 .
--   $$
--
--   It depends only on $q$, hence only on $p$ and $\nu$.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Lemma 4.3(b), Eq. (4.7), p.7

import Mathlib
import Definitions.Def_MatchedUCLB_aLift
import Definitions.Def_MatchedUCLB_theta

namespace MatchedUCLB

/-- **The constant `β_q = 1/q + a_lift θ²`.** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, Lemma 4.3(b), Eq. (4.7), p.7. Here `q = p + ν`.

**Formalization Note.** `q` is a real parameter; every power with exponent depending on `q` is
`Real.rpow`. The constant depends on `q` only. -/
noncomputable def betaQ (q : ℝ) : ℝ :=
  1 / q + aLift q * theta q ^ 2

end MatchedUCLB


