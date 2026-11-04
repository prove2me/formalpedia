-- Prove2me | Definitions.Def_ImpactCopula_mpddTilde
-- name    : ImpactCopula_mpddTilde
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:54:46.71833+00:00
-- url     : https://prove2.me/theorems/6a6cf2aa-0673-487d-8023-9cb0fa518a72
-- title:
--   The modified MPDD $\tilde D_1C(u,v)$ of (A.67)
-- statement:
--   In the proof of Theorem 2, the MPDD is modified at the jump values of $F_X$:
--
--   $$
--   \tilde D_1C(u,v) = \begin{cases} \dfrac{C(F_X(d), v) - C(F_X(d-), v)}{F_X(d) - F_X(d-)}, & u = F_X(d),\ d \in \Delta_X,\\[1ex] D_1C(u,v), & \text{otherwise}. \end{cases} \tag{A.67}
--   $$
--
--   At $u = F_X(d)$ it is the slope of $C(\cdot, v)$ across the gap $(F_X(d-), F_X(d))$.
--
--   **Formalization Note** The jump $d$ with $u = F_X(d)$ is unique when it exists (distinct jumps have distinct values $F_X(d)$), so a choice function picks the paper's $d$. $F_X(d-)$ is `Function.leftLim (cdfX μ) d`.
-- source:
--   Lo–Wu–Zhang–Zhao, Optimal Impact Portfolios with General Dependence and Marginals, SSRN 4177277 (draft of February 25, 2024), Appendix C.3, proof of Theorem 2, eq. (A.67), p.79 (PDF p.82)

import Mathlib
import Definitions.Def_ImpactCopula_mpdd
import Definitions.Def_ImpactCopula_cdfX

open MeasureTheory

namespace ImpactCopula

open Classical in
/-- The modified MPDD `D̃₁C` of the proof of Theorem 2 (eq. (A.67)), Lo–Wu–Zhang–Zhao, *Optimal Impact Portfolios with General Dependence and Marginals*, SSRN 4177277 (draft of February 25, 2024), p.79 (PDF p.82):
`D̃₁C(u, v) = (C(F_X(d), v) − C(F_X(d−), v))/(F_X(d) − F_X(d−))` if `u = F_X(d)` for a
discontinuity point `d ∈ Δ_X` of `F_X`, and `D̃₁C(u, v) = D₁C(u, v)` otherwise.

**Formalization Note.** The discontinuity point `d` with `u = F_X(d)` is unique when it exists
(distinct jumps `d₁ < d₂` have `F_X(d₁) ≤ F_X(d₂−) < F_X(d₂)`), so `Classical.choose` picks the
paper's `d`. `F_X(d−)` is `Function.leftLim (cdfX μ) d`. -/
noncomputable def mpddTilde (C : ℝ → ℝ → ℝ) (μ : Measure (ℝ × ℝ)) (u v : ℝ) : ℝ :=
  if h : ∃ d : ℝ, ¬ ContinuousAt (cdfX μ) d ∧ u = cdfX μ d then
    (C (cdfX μ h.choose) v - C (Function.leftLim (cdfX μ) h.choose) v) /
      (cdfX μ h.choose - Function.leftLim (cdfX μ) h.choose)
  else mpdd C u v

end ImpactCopula


