-- Prove2me | Definitions.Def_DSICCompComp_erLaw
-- name    : DSICCompComp_erLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:29:06.388588+00:00
-- url     : https://prove2.me/theorems/e7684a35-579a-461e-9fc9-66db0bdb3783
-- title:
--   Equal Revenue distribution $\mathcal{ER}$
-- statement:
--   The **Equal Revenue distribution** $\mathcal{ER}$ is the distribution on $[1,\infty)$ with CDF
--   $$
--   F(x) = 1 - \frac1x, \qquad x \ge 1,
--   $$
--   equivalently with density $x^{-2}$ on $[1,\infty)$. Every posted price $p \ge 1$ earns the same revenue $p\,(1 - F(p)) = 1$, which gives the distribution its name.
--
--   **Formalization Note** This is Mathlib's Pareto distribution with scale $1$ and shape $1$.
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), §3.2, p.11 (pdf p.12)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace DSICCompComp

/-- The **Equal Revenue distribution** `ℰℛ` (Ryu–Weinberg–Xue, *The DSIC Competition Complexity
of Additive Buyers over Independent Items*, STOC 2027 submission, manuscript of Nov. 3, 2026,
sha256 bf61bfdb…, §3.2, p.11 (pdf p.12)): the law on `ℝ` with support `[1, +∞)` and CDF
`1 − 1/x`, i.e. density `x⁻²` on `[1, ∞)`.

**Formalization Note** This is Mathlib's Pareto distribution with scale `1` and shape `1`
(`paretoMeasure 1 1 = volume.withDensity (x ↦ 1 · 1¹ · x^{−2} on [1, ∞))`). -/
noncomputable def erLaw : Measure ℝ :=
  paretoMeasure 1 1

instance : IsProbabilityMeasure erLaw :=
  isProbabilityMeasure_paretoMeasure one_pos one_pos

end DSICCompComp


