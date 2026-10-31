-- Prove2me | Definitions.Def_CompInvestBayes_theta
-- name    : CompInvestBayes_theta
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:03:42.354749+00:00
-- url     : https://prove2.me/theorems/45910c64-3e88-4789-aac3-a4b13d61f2d0
-- title:
--   Market state $\theta = \mathbf 1\{U<y_0\}$ and the earning potentials $\mu(\theta), \mu_1(\theta), \mu_2(\theta)$
-- statement:
--   For a prior $y_0$, the market state is $\theta=\mathbf 1\{U<y_0\}$ ($\theta=1$: favorable market). The expected potential earning rates are
--
--   $$
--   \mu(\theta)=\begin{cases}\mu_H & \theta=1\\ \mu_L&\theta=0\end{cases},\qquad
--   \mu_1(\theta)=\begin{cases}\mu_{1,H} & \theta=1\\ \mu_{1,L}&\theta=0\end{cases},\qquad
--   \mu_2(\theta)=\begin{cases}\mu_{2,H} & \theta=1\\ \mu_{2,L}&\theta=0\end{cases}.
--   $$
--
--   $\mu(\theta)$ is the leader's rate before the follower enters, $\mu_1(\theta)$ and $\mu_2(\theta)$ are the leader's and the follower's rates after entry. The file also records that these random variables are measurable.
-- source:
--   Sunar, Yu, Kulkarni, Competitive Investment with Bayesian Learning: Choice of Business Size and Timing, SSRN 3408260 (submitted version), §2, pp.7–9 (PDF 7–9), θ ∈ {0, 1}, µ_i(1) = µ_{i,H}, µ_i(0) = µ_{i,L}, µ(θ) = µ_1(θ) + µ_2(θ)

import Mathlib
import Definitions.Def_CompInvestBayes_Params
import Definitions.Def_CompInvestBayes_Setup

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace CompInvestBayes

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The market state `θ ∈ {0, 1}` for prior `y₀`, realized as `θ = 1{U < y₀}`
(SSRN 3408260, p.7 and p.9, PDF 7, 9: "The favorableness of the market is represented by the random
variable θ ∈ {0,1}"; the initial belief is `P(θ = 1) = π₀ = y₀`). Since `U` is uniform on `[0, 1]`
and independent of the Brownian motions, `P(θ = 1) = y₀` for `y₀ ∈ [0, 1]` and `θ` is independent of
the Brownian motions. -/
noncomputable def theta (E : Setup Ω) (y0 : ℝ) (ω : Ω) : ℝ := if E.U ω < y0 then 1 else 0

/-- The leader's pre-entry expected potential earning rate `µ(θ) = µ_H` if `θ = 1` (i.e. `U < y₀`),
`µ_L` if `θ = 0` (SSRN 3408260, pp.8–9, PDF 8–9). -/
noncomputable def muTot (p : Params) (E : Setup Ω) (y0 : ℝ) (ω : Ω) : ℝ :=
  if E.U ω < y0 then p.muH else p.muL

/-- The leader's post-entry expected potential earning rate `µ₁(θ) = µ_{1,H}` or `µ_{1,L}`
(SSRN 3408260, p.8, PDF 8). -/
noncomputable def mu1 (p : Params) (E : Setup Ω) (y0 : ℝ) (ω : Ω) : ℝ :=
  if E.U ω < y0 then p.mu1H else p.mu1L

/-- The follower's expected potential earning rate `µ₂(θ) = µ_{2,H}` or `µ_{2,L}`
(SSRN 3408260, p.8, PDF 8). -/
noncomputable def mu2 (p : Params) (E : Setup Ω) (y0 : ℝ) (ω : Ω) : ℝ :=
  if E.U ω < y0 then p.mu2H else p.mu2L

lemma measurable_muTot (p : Params) (E : Setup Ω) (y0 : ℝ) : Measurable (muTot p E y0) :=
  Measurable.ite (measurableSet_lt E.measurable_U measurable_const) measurable_const
    measurable_const

lemma measurable_mu1 (p : Params) (E : Setup Ω) (y0 : ℝ) : Measurable (mu1 p E y0) :=
  Measurable.ite (measurableSet_lt E.measurable_U measurable_const) measurable_const
    measurable_const

lemma measurable_mu2 (p : Params) (E : Setup Ω) (y0 : ℝ) : Measurable (mu2 p E y0) :=
  Measurable.ite (measurableSet_lt E.measurable_U measurable_const) measurable_const
    measurable_const

end CompInvestBayes


