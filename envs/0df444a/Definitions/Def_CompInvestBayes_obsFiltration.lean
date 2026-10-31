-- Prove2me | Definitions.Def_CompInvestBayes_obsFiltration
-- name    : CompInvestBayes_obsFiltration
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:04:23.710962+00:00
-- url     : https://prove2.me/theorems/01cd6100-014b-4afa-8be5-9cba71daede3
-- title:
--   The leader's pre-entry earnings $X^s_1$ and the follower's information filtration
-- statement:
--   Before the follower enters, the leader's cumulative earnings follow
--
--   $$
--   dX^s_{1,t}=\min(S_1,\mu(\theta))\,dt+\sigma\,dB^s_{1,t},\qquad X^s_{1,0}=0,
--   $$
--
--   for an investment size $S_1>0$; for $S_1=0$ the leader earns nothing and $X^s_1\equiv 0$. The follower observes $X^s_1$, and its information at time $t$ is the natural filtration $\mathcal F_t=\sigma(X^s_{1,u}:0\le u\le t)$.
--
--   The follower's admissible investment times are the stopping times of this filtration.
--
--   **Formalization Note** The filtration is Mathlib's raw natural filtration; the paper's filtration is in addition augmented ("satisfies the standard properties"). The process is defined for all $t\ge0$, as the paper does for the belief process.
-- source:
--   Sunar, Yu, Kulkarni, Competitive Investment with Bayesian Learning: Choice of Business Size and Timing, SSRN 3408260 (submitted version), eq. (1), p.7 and the natural filtration F^{X^s_1}, p.9 (PDF 7, 9)

import Mathlib
import Definitions.Def_CompInvestBayes_theta

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace CompInvestBayes

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The leader's pre-entry cumulative earning process** `X^s_{1,t}` (SSRN 3408260, (1), p.7,
PDF 7): `dX^s_{1,t} = min(S₁, µ(θ)) dt + σ dB^s_{1,t}` for `S₁ > 0`, started at `X^s_{1,0} = 0`;
"If Si = 0, firm i's cumulative earning at any time instant is zero" (p.8).

**Formalization Note.** The process is defined for every `t ≥ 0`, as the paper does for the
posterior belief ("For mathematical convenience, we define the posterior belief process for
t ∈ [0, ∞)", p.9); only `t < τ` matters for the payoffs. -/
noncomputable def obsProcess (p : Params) (σ : ℝ) (E : Setup Ω) (S1 y0 : ℝ) (t : ℝ≥0)
    (ω : Ω) : ℝ :=
  if 0 < S1 then min S1 (muTot p E y0 ω) * (t : ℝ) + σ * E.Bs t ω else 0

lemma measurable_obsProcess (p : Params) (σ : ℝ) (E : Setup Ω) (S1 y0 : ℝ) (t : ℝ≥0) :
    Measurable (obsProcess p σ E S1 y0 t) := by
  unfold obsProcess
  split_ifs
  · have h1 := measurable_muTot p E y0
    have h2 := E.measurable_Bs t
    fun_prop
  · exact measurable_const

/-- **The follower's information**: the natural filtration `F^{X^s_1}` of the leader's pre-entry
earning process (SSRN 3408260, p.9, PDF 9), `F_t = σ(X^s_{1,u}, 0 ≤ u ≤ t)`.

**Formalization Note.** This is Mathlib's raw natural filtration; the paper's filtration in addition
"satisfies the standard properties" (the usual augmentation). Admissible stopping times of the
follower are stopping times of this filtration with values in `[0, ∞]`. -/
noncomputable def obsFiltration (p : Params) (σ : ℝ) (E : Setup Ω) (S1 y0 : ℝ) :
    Filtration ℝ≥0 ‹MeasurableSpace Ω› :=
  Filtration.natural (fun t => obsProcess p σ E S1 y0 t)
    (fun t => (measurable_obsProcess p σ E S1 y0 t).stronglyMeasurable)

end CompInvestBayes


