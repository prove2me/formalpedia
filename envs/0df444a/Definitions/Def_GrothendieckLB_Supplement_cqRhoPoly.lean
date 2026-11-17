-- Prove2me | Definitions.Def_GrothendieckLB_Supplement_cqRhoPoly
-- name    : GrothendieckLB_Supplement_cqRhoPoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:38:03.480257+00:00
-- url     : https://prove2.me/theorems/59e2e89a-8815-4cc9-879b-4d069ae3d3cf
-- title:
--   Cubic–quintic correlation map $\rho(t)=(t-s_3^2t^3+s_5^2t^5)/V$
-- statement:
--   For real parameters $s_3,s_5$, set $V=1+s_3^2+s_5^2$ and
--   $$
--   \rho(t)=\frac{t-s_3^2t^3+s_5^2t^5}{V}.
--   $$
--   This is the correlation of the first coordinate of the cubic–quintic limiting scheme (11). Its coefficients have absolute values summing to $(1+s_3^2+s_5^2)/V=1$, so it is allowable.
--
--   **Formalization Note** $\rho$ is a polynomial; its value at $t$ is the polynomial evaluation and the coefficient $[t^j]\rho(t)^a$ is the polynomial coefficient of $\rho^a$.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), (11), p.24

import Mathlib
open Polynomial

namespace GrothendieckLB

namespace Supplement

/-- The correlation map of the cubic–quintic scheme as a polynomial (Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), (11), p.24):
`ρ(t) = (t − s₃² t³ + s₅² t⁵)/V` with `V = 1 + s₃² + s₅²`.

**Formalization Note** `ρ` is a polynomial, so it is a `Polynomial ℝ` and its value is
`(cqRhoPoly s₃ s₅).eval t`; the coefficient `[t^j] ρ(t)^a` of (16) is
`((cqRhoPoly s₃ s₅) ^ a).coeff j`. The parameters are free reals; the paper's are (10). -/
noncomputable def cqRhoPoly (s₃ s₅ : ℝ) : ℝ[X] :=
  C (1 / (1 + s₃ ^ 2 + s₅ ^ 2)) * (X - C (s₃ ^ 2) * X ^ 3 + C (s₅ ^ 2) * X ^ 5)

end Supplement

end GrothendieckLB


