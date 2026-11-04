-- Prove2me | Definitions.Def_ImpactCopula_mixture
-- name    : ImpactCopula_mixture
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:55:43.975254+00:00
-- url     : https://prove2.me/theorems/d1b4a300-c5e4-46f6-a888-24c116abe5a4
-- title:
--   The mixture function $g(u,w) = F_\theta^{-1}\circ g_u(w)$
-- statement:
--   Given a copula $C$ and the marginal distribution function $F_\theta$ of the residual return, the **mixture function** of the representation theorem is
--
--   $$
--   g(u, w) = F_\theta^{-1}\big(g_u(w)\big), \tag{15}
--   $$
--
--   where $g_u$ is the inverse of $v \mapsto D_1C(u,v)$ and $F_\theta^{-1}(p) = \inf\{x : F_\theta(x) \ge p\}$ is the inverse function of Definition A.1. It depends on $C$ and $F_\theta$ only, not on $F_X$.
--
--   **Formalization Note** $F_\theta^{-1}$ is the published `quantileFunction` of `μ.map Prod.snd`. Both inverses are real `sInf`s; where the paper's value is $\pm\infty$ ($w \le 0$, $g_u(w) = 0$, or $g_u(w) = 1$ with $F_\theta < 1$) Lean returns $0$. By Remark 1 (ii) this happens only on a Lebesgue-null set of $(u, w) \in [0,1]^2$, so laws of $g(U, V)$ are unaffected.
-- source:
--   Lo–Wu–Zhang–Zhao, Optimal Impact Portfolios with General Dependence and Marginals, SSRN 4177277 (draft of February 25, 2024), Theorem 2, eq. (15), p.12 (PDF p.15); Definition A.1, p.42 (PDF p.45)

import Mathlib
import Definitions.Def_ImpactCopula_condInv
import Definitions.Def_RiskFunctionals_StochDominance_QuantileFunction

open MeasureTheory

namespace ImpactCopula

/-- The mixture function of Theorem 2 (eq. (15)), Lo–Wu–Zhang–Zhao, *Optimal Impact Portfolios with General Dependence and Marginals*, SSRN 4177277 (draft of February 25, 2024), p.12 (PDF p.15):
`g(u, w) = F_θ⁻¹ ∘ g_u(w)`, where `g_u` is the inverse function of `v ↦ D₁C(u, v)` and `F_θ⁻¹` is
the inverse function of Definition A.1 (p.42, PDF p.45), `F_θ⁻¹(y) = inf {x : F_θ(x) ≥ y}`.

**Formalization Note.** `F_θ⁻¹` is the published `quantileFunction` of the second marginal
`μ.map Prod.snd`. Both inverses are real-valued `sInf`s: where the paper's value is `±∞`
(`w ≤ 0`, `g_u(w) = 0`, or `g_u(w) = 1` with `F_θ < 1`), Lean returns `0`. This happens only on a
Lebesgue-null set of `(u, w) ∈ [0, 1]²` (by Remark 1 (ii), `∫₀¹ D₁C(u, 0) du = C(1, 0) = 0` and
`∫₀¹ (1 − D₁C(u, 1−)) du = 0`), so it changes no law built from `g(U, V)`. -/
noncomputable def mixture (C : ℝ → ℝ → ℝ) (μ : Measure (ℝ × ℝ)) (u w : ℝ) : ℝ :=
  RiskFunctionals.StochDominance.quantileFunction (μ.map Prod.snd) (condInv C u w)

end ImpactCopula


