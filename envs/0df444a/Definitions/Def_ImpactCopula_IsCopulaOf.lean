-- Prove2me | Definitions.Def_ImpactCopula_IsCopulaOf
-- name    : ImpactCopula_IsCopulaOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:54:00.571694+00:00
-- url     : https://prove2.me/theorems/fb49a84c-770a-47cb-a55d-848a0d5d72bf
-- title:
--   $C$ is a copula of $F$: $F(x,y) = C(F_X(x), F_\theta(y))$
-- statement:
--   A **copula** is a function $C : [0,1]^2 \to [0,1]$ with $C(u,0) = C(0,u) = 0$ and $C(u,1) = C(1,u) = u$ for $u \in [0,1]$, and nonnegative $C$-volume on every rectangle $[u_1,u_2]\times[v_1,v_2] \subseteq [0,1]^2$. Let $F$ be a bivariate distribution with law $\mu$ on $\mathbb R^2$ and marginal distribution functions $F_X$, $F_\theta$. A copula $C$ is a **copula of $F$** if
--
--   $$
--   F(x, y) = \mu\big((-\infty,x]\times(-\infty,y]\big) = C\big(F_X(x), F_\theta(y)\big) \qquad \text{for all } x, y \in \mathbb R . \tag{10}
--   $$
--
--   By Sklar's theorem such a $C$ exists; it is unique on $\overline{\mathcal R}_X \times \overline{\mathcal R}_\theta$ but not elsewhere when a marginal has atoms.
--
--   **Formalization Note** The copula is a function `ℝ → ℝ → ℝ` satisfying the published `ActuarialValuation.coIsCopula` on the unit square; its values off $[0,1]^2$ are unconstrained and unused.
-- source:
--   Lo–Wu–Zhang–Zhao, Optimal Impact Portfolios with General Dependence and Marginals, SSRN 4177277 (draft of February 25, 2024), §3.1, eq. (10), p.10 (PDF p.13)

import Mathlib
import Definitions.Def_actuarial_coIsCopula
import Definitions.Def_ImpactCopula_cdfX
import Definitions.Def_ImpactCopula_cdfTheta

open MeasureTheory

namespace ImpactCopula

/-- `C` is a copula of `F` (eq. (10)), Lo–Wu–Zhang–Zhao, *Optimal Impact Portfolios with General Dependence and Marginals*, SSRN 4177277 (draft of February 25, 2024), p.10 (PDF p.13): `C` is a copula and
`F(x, y) = C(F_X(x), F_θ(y))` for all `x, y ∈ ℝ`; "we refer to C as a copula of F when it
satisfies (10)".

**Formalization Note.** A copula is a function `ℝ → ℝ → ℝ` satisfying the published
`ActuarialValuation.coIsCopula` (grounded, uniform margins and 2-increasing on `[0, 1]²`); its
values off the unit square are unconstrained and never used. `F(x, y)` is
`μ(( -∞, x] × (-∞, y])`. A copula of `F` need not be unique when a marginal has atoms. -/
def IsCopulaOf (C : ℝ → ℝ → ℝ) (μ : Measure (ℝ × ℝ)) : Prop :=
  ActuarialValuation.coIsCopula C ∧
    ∀ x y : ℝ, μ.real (Set.Iic x ×ˢ Set.Iic y) = C (cdfX μ x) (cdfTheta μ y)

end ImpactCopula


