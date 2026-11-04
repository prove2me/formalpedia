-- Prove2me | Definitions.Def_ImpactCopula_condInvTilde
-- name    : ImpactCopula_condInvTilde
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:55:44.936625+00:00
-- url     : https://prove2.me/theorems/344ae5b6-0e39-48ed-8304-441e070299ab
-- title:
--   $\tilde g_u(w) = \inf\{v \in \overline{\mathcal R}_\theta : \tilde D_1C(u,v) \ge w\}$
-- statement:
--   The inverse of the modified MPDD restricted to $\overline{\mathcal R}_\theta$:
--
--   $$
--   \tilde g_u(w) = \inf\{v : \tilde D_1C(u,v) \ge w,\ v \in \overline{\mathcal R}_\theta\} . \tag{A.71}
--   $$
--
--   **Formalization Note** The infimum is a real `sInf`; for a copula of a probability measure and $w \in [0,1]$ the set is nonempty and lies in $[0,1]$, so this is the paper's value.
-- source:
--   Lo–Wu–Zhang–Zhao, Optimal Impact Portfolios with General Dependence and Marginals, SSRN 4177277 (draft of February 25, 2024), Appendix C.3, proof of Theorem 2, eq. (A.71), p.80 (PDF p.83)

import Mathlib
import Definitions.Def_ImpactCopula_mpddTilde
import Definitions.Def_ImpactCopula_rbarTheta

open MeasureTheory

namespace ImpactCopula

/-- `g̃_u(w) = inf {v : D̃₁C(u, v) ≥ w, v ∈ R̄_θ}` (eq. (A.71)), Lo–Wu–Zhang–Zhao, *Optimal Impact Portfolios with General Dependence and Marginals*, SSRN 4177277 (draft of February 25, 2024), p.80 (PDF p.83).

**Formalization Note.** Real-valued `sInf`. For a copula of a probability measure and
`w ∈ [0, 1]` the set is nonempty (`1 ∈ R̄_θ` and `D̃₁C(u, 1) = 1`) and bounded below
(`R̄_θ ⊆ [0, 1]`), so the value is the paper's. -/
noncomputable def condInvTilde (C : ℝ → ℝ → ℝ) (μ : Measure (ℝ × ℝ)) (u w : ℝ) : ℝ :=
  sInf {v : ℝ | v ∈ rbarTheta μ ∧ w ≤ mpddTilde C μ u v}

end ImpactCopula


