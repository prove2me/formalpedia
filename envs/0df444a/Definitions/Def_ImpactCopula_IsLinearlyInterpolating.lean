-- Prove2me | Definitions.Def_ImpactCopula_IsLinearlyInterpolating
-- name    : ImpactCopula_IsLinearlyInterpolating
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:54:47.38283+00:00
-- url     : https://prove2.me/theorems/e6631792-976e-4311-a326-ad9a11b462c4
-- title:
--   Linearly interpolating copula on $\overline{\mathcal R}_X^c \times \overline{\mathcal R}_\theta$
-- statement:
--   Let $\Delta_X$ be the set of discontinuity points of $F_X$ and $F_X(d-) = \lim_{x \to d^-} F_X(x)$. A copula $C$ is **linearly interpolating on $\overline{\mathcal R}_X^c \times \overline{\mathcal R}_\theta$ with respect to $u$** if
--
--   $$
--   C(u, v) = \frac{F_X(d) - u}{F_X(d) - F_X(d-)}\, C\big(F_X(d-), v\big) + \frac{u - F_X(d-)}{F_X(d) - F_X(d-)}\, C\big(F_X(d), v\big) \tag{13}
--   $$
--
--   for every $d \in \Delta_X$ and every $(u, v) \in (F_X(d-), F_X(d)) \times \overline{\mathcal R}_\theta$.
--
--   The intervals $(F_X(d-), F_X(d))$ make up $\overline{\mathcal R}_X^c = [0,1] \setminus \overline{\mathcal R}_X$, the region where (10) does not determine $C$; the condition says $C(\cdot, v)$ is affine across each such gap. When $F_X$ is continuous the condition is empty.
--
--   **Formalization Note** $\Delta_X$ is the set of points where `cdfX μ` is not continuous, and $F_X(d-)$ is `Function.leftLim (cdfX μ) d`.
-- source:
--   Lo–Wu–Zhang–Zhao, Optimal Impact Portfolios with General Dependence and Marginals, SSRN 4177277 (draft of February 25, 2024), Definition 1, eq. (13) and footnote 15, p.11 (PDF p.14)

import Mathlib
import Definitions.Def_ImpactCopula_cdfX
import Definitions.Def_ImpactCopula_rbarTheta

open MeasureTheory

namespace ImpactCopula

/-- A copula linearly interpolating on `R̄_X^c × R̄_θ` with respect to `u` (Definition 1, eq. (13)),
Lo–Wu–Zhang–Zhao, *Optimal Impact Portfolios with General Dependence and Marginals*, SSRN 4177277 (draft of February 25, 2024), p.11 (PDF p.14): for every discontinuity point `d ∈ Δ_X` of `F_X` and every
`(u, v) ∈ (F_X(d−), F_X(d)) × R̄_θ`,
`C(u, v) = (F_X(d) − u)/(F_X(d) − F_X(d−)) · C(F_X(d−), v)
  + (u − F_X(d−))/(F_X(d) − F_X(d−)) · C(F_X(d), v)`,
with `F_X(d−) = lim_{x→d−} F_X(x)`.

**Formalization Note.** `Δ_X` is `{d | ¬ ContinuousAt (cdfX μ) d}`; `F_X(d−)` is
`Function.leftLim (cdfX μ) d`, which is the left limit for the monotone `F_X`. `R̄_θ` is
`rbarTheta μ`. At a discontinuity `F_X(d−) < F_X(d)`, so no denominator vanishes. -/
def IsLinearlyInterpolating (C : ℝ → ℝ → ℝ) (μ : Measure (ℝ × ℝ)) : Prop :=
  ∀ d : ℝ, ¬ ContinuousAt (cdfX μ) d →
    ∀ u ∈ Set.Ioo (Function.leftLim (cdfX μ) d) (cdfX μ d),
    ∀ v ∈ rbarTheta μ,
      C u v = (cdfX μ d - u) / (cdfX μ d - Function.leftLim (cdfX μ) d)
                * C (Function.leftLim (cdfX μ) d) v
            + (u - Function.leftLim (cdfX μ) d) / (cdfX μ d - Function.leftLim (cdfX μ) d)
                * C (cdfX μ d) v

end ImpactCopula


