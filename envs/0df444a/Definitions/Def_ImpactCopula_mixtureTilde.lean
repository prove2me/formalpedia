-- Prove2me | Definitions.Def_ImpactCopula_mixtureTilde
-- name    : ImpactCopula_mixtureTilde
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:56:26.497833+00:00
-- url     : https://prove2.me/theorems/e0d9da73-2ae6-4929-a3d9-8755ecb14ef6
-- title:
--   $\tilde g(u,w) = F_\theta^{-1}\circ\tilde g_u(w)$
-- statement:
--   The modified mixture function of the proof of Theorem 2:
--
--   $$
--   \tilde g(u, w) = F_\theta^{-1}\big(\tilde g_u(w)\big), \tag{A.71}
--   $$
--
--   with $F_\theta^{-1}(p) = \inf\{x : F_\theta(x) \ge p\}$.
--
--   **Formalization Note** $F_\theta^{-1}$ is the published `quantileFunction` of `μ.map Prod.snd` (real `sInf`; the paper's $\pm\infty$ at $p = 0$ and, when $F_\theta < 1$, at $p = 1$ become $0$).
-- source:
--   Lo–Wu–Zhang–Zhao, Optimal Impact Portfolios with General Dependence and Marginals, SSRN 4177277 (draft of February 25, 2024), Appendix C.3, proof of Theorem 2, eq. (A.71), p.80 (PDF p.83)

import Mathlib
import Definitions.Def_ImpactCopula_condInvTilde
import Definitions.Def_RiskFunctionals_StochDominance_QuantileFunction

open MeasureTheory

namespace ImpactCopula

/-- `g̃(u, w) = F_θ⁻¹ ∘ g̃_u(w)` (eq. (A.71)), Lo–Wu–Zhang–Zhao, *Optimal Impact Portfolios with General Dependence and Marginals*, SSRN 4177277 (draft of February 25, 2024), p.80 (PDF p.83).

**Formalization Note.** `F_θ⁻¹` is the published `quantileFunction` of `μ.map Prod.snd`
(Definition A.1, real-valued `sInf`; the paper's `±∞` values at `0` and, when `F_θ < 1`, at `1`
become `0`). -/
noncomputable def mixtureTilde (C : ℝ → ℝ → ℝ) (μ : Measure (ℝ × ℝ)) (u w : ℝ) : ℝ :=
  RiskFunctionals.StochDominance.quantileFunction (μ.map Prod.snd) (condInvTilde C μ u w)

end ImpactCopula


