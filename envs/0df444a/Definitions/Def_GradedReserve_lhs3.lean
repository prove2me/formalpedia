-- Prove2me | Definitions.Def_GradedReserve_lhs3
-- name    : GradedReserve_lhs3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:33:07.467013+00:00
-- url     : https://prove2.me/theorems/64d3ff5f-7f8f-4cee-91bc-087598b50f9b
-- title:
--   Left side of equation (3)
-- statement:
--   For the power law, the left side of equation (3) of Theorem 3.1,
--   $$R_n(0)+\frac n\ell\,\bar v^{\,\ell}\,\frac p{p+\ell}-\frac{n(k+1)}{N+1}\,\bar v^{\,N+1}\,\frac p{p+N+1},$$
--   as a function of $p$; equation (3) sets it equal to $\tau$.
--
--   **Formalization Note** $R_n(0)$ is the revenue curve (1) of the power law at $r=0$.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Theorem 3.1, p.5 (PDF 6), equation (3)

import Mathlib
import Definitions.Def_GradedReserve_revCurve
import Definitions.Def_GradedReserve_powerDensity
import Definitions.Def_GradedReserve_powL
import Definitions.Def_GradedReserve_powN
import Definitions.Def_GradedReserve_vbar
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- The left side of equation (3) (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Theorem 3.1, p.5, PDF 6):
`R_n(0) + (n/ℓ) v̄^ℓ p/(p+ℓ) − (n(k+1)/(N+1)) v̄^{N+1} p/(p+N+1)`, for the power law
`F(v) = v^k`.

**Formalization Note.** `R_n(0)` is the revenue curve (1) of the power law at `r = 0`, not its
closed form. -/
noncomputable def lhs3 (k : ℝ) (n : ℕ) (p : ℝ) : ℝ :=
  revCurve (powerDensity k) n 0
    + (n / powL k n) * vbar k n p ^ powL k n * (p / (p + powL k n))
    - (n * (k + 1) / (powN k n + 1)) * vbar k n p ^ (powN k n + 1) * (p / (p + powN k n + 1))

end GradedReserve


