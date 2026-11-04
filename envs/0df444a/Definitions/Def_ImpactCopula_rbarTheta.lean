-- Prove2me | Definitions.Def_ImpactCopula_rbarTheta
-- name    : ImpactCopula_rbarTheta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:53:46.651442+00:00
-- url     : https://prove2.me/theorems/8b2a0645-07a9-4f26-9b5c-dbd9d8dd6b51
-- title:
--   The closure $\overline{\mathcal R}_\theta$ of the range of $F_\theta$
-- statement:
--   For the joint law $\mu$ of $(X_i, \theta_i)$, let
--
--   $$
--   \overline{\mathcal R}_\theta = \overline{\{F_\theta(y) : y \in \mathbb R\}}
--   $$
--
--   be the closure of the range of the marginal distribution function $F_\theta$. It is a closed subset of $[0,1]$ containing $0$ and $1$, and its complement in $[0,1]$ is the union of the gaps $(F_\theta(d-), F_\theta(d))$ over the atoms $d$ of $\theta_i$. By Sklar's theorem a copula of $\mu$ is determined on $\overline{\mathcal R}_X \times \overline{\mathcal R}_\theta$ only.
-- source:
--   Lo–Wu–Zhang–Zhao, Optimal Impact Portfolios with General Dependence and Marginals, SSRN 4177277 (draft of February 25, 2024), §3.1, p.10 (PDF p.13)

import Mathlib
import Definitions.Def_ImpactCopula_cdfTheta

open MeasureTheory

namespace ImpactCopula

/-- `R̄_θ`, the closure of the range of `F_θ`, Lo–Wu–Zhang–Zhao, *Optimal Impact Portfolios with General Dependence and Marginals*, SSRN 4177277 (draft of February 25, 2024), p.10 (PDF p.13): "R̄_X and R̄_θ are
the closures of the ranges of F_X and F_θ, respectively". For a probability measure it is a
closed subset of `[0, 1]` containing `0` and `1`. -/
def rbarTheta (μ : Measure (ℝ × ℝ)) : Set ℝ :=
  closure (Set.range (cdfTheta μ))

end ImpactCopula


