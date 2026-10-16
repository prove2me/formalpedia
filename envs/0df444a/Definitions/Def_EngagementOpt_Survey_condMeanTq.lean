-- Prove2me | Definitions.Def_EngagementOpt_Survey_condMeanTq
-- name    : EngagementOpt_Survey_condMeanTq
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T06:19:26.490872+00:00
-- url     : https://prove2.me/theorems/f19d95e6-2989-41e3-b22d-eb744b6f0848
-- title:
--   (9): the conditional mean $\mathbb E[T_q\mid T=t]$
-- statement:
--   For parameters $p,q$ and a session length $t\ge1$, the conditional mean of system 2's span $T_q$ given that the session lasted $T=T_q+T_p-1=t$ steps is defined by Bayes' rule, as in equation (9) of the paper:
--
--   $$
--   \mathbb E[T_q\mid T=t]=\mathbb E[T_q\mid T_q+T_p=t+1]
--   =\frac{\sum_{\tau=1}^{t}\tau\,\Pr[T_q=\tau\cap T_p=t-\tau+1]}{\sum_{\tau'=1}^{t}\Pr[T_q=\tau'\cap T_p=t-\tau'+1]},
--   $$
--
--   with the joint masses of `jointMass`.
--
--   **Formalization Note** Equation (9) is taken as the definition of the conditional expectation; no measure-theoretic conditioning is used. The denominator is $\Pr[T=t]$, which is positive for $t\ge1$ when $0<p,q<1$; at $t=0$ both sums are empty and Lean's convention $0/0=0$ applies, but $t=0$ is outside the support of $T$ and never used.
-- source:
--   Kleinberg, Mullainathan, Raghavan, The Challenge of Understanding What Users Want, arXiv:2202.11776v3, p. 20, eq. (9)

import Mathlib
import Definitions.Def_EngagementOpt_Survey_jointMass

namespace EngagementOpt.Survey

/-- Equation (9) of arXiv:2202.11776v3, p. 20, taken as the definition of the conditional mean
`E[T_q | T = t] = E[T_q | T_q + T_p = t + 1]`:
`(∑_{τ=1}^t τ Pr[T_q = τ ∩ T_p = t-τ+1]) / (∑_{τ'=1}^t Pr[T_q = τ' ∩ T_p = t-τ'+1])`. -/
noncomputable def condMeanTq (p q : ℝ) (t : ℕ) : ℝ :=
  (∑ τ ∈ Finset.Icc 1 t, (τ : ℝ) * jointMass p q t τ) /
    (∑ τ ∈ Finset.Icc 1 t, jointMass p q t τ)

end EngagementOpt.Survey


