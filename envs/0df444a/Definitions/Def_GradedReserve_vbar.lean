-- Prove2me | Definitions.Def_GradedReserve_vbar
-- name    : GradedReserve_vbar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:31:08.533194+00:00
-- url     : https://prove2.me/theorems/e369df0c-14b4-43b0-b8b0-f3644bddad13
-- title:
--   $\bar v$ with $\bar v^{k}=\frac1{k+1}\big(1-\frac{km}{p(p+\ell)}\big)$
-- statement:
--   For $p>p_{\min}$, $\bar v>0$ is defined by
--   $$\bar v^{\,k}=\frac1{k+1}\Big(1-\frac{km}{p(p+\ell)}\Big).$$
--   It is the type from which the optimal graded reserve sells with certainty.
--
--   **Formalization Note** $\bar v$ is the real $k$-th root of the bracket, which is positive exactly for $p>p_{\min}$.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Theorem 3.1, p.5 (PDF 6)

import Mathlib
import Definitions.Def_GradedReserve_powM
import Definitions.Def_GradedReserve_powL
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- `v̄`, defined by `v̄^k = (1/(k+1)) (1 − km/(p(p + ℓ)))` (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Theorem 3.1, p.5, PDF 6).

**Formalization Note.** `v̄` is the `k`-th root (`Real.rpow` with exponent `1/k`) of the bracket,
which is positive exactly when `p > p_min` (p.5); `v̄` is used only for such `p`. -/
noncomputable def vbar (k : ℝ) (n : ℕ) (p : ℝ) : ℝ :=
  ((1 / (k + 1)) * (1 - k * powM k n / (p * (p + powL k n)))) ^ (1 / k)

end GradedReserve


