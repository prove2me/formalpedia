-- Prove2me | Definitions.Def_CompInvestBayes_FollowerStrategy
-- name    : CompInvestBayes_FollowerStrategy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:05:54.607995+00:00
-- url     : https://prove2.me/theorems/2bef5294-660b-4cb6-ac50-355ed70227db
-- title:
--   Follower strategies $(\tau,S_2)$, the follower's profit (7) and best responses (9)
-- statement:
--   Given the leader's size $S_1$ and the prior $y_0$, a **feasible strategy** of the follower is a pair $(\tau,S_2)$ where $\tau\in[0,\infty]$ is a stopping time of the natural filtration of $X^s_1$ (the investment time) and $S_2\ge0$ is the investment size, known at time $\tau$ (measurable with respect to $\mathcal F_\tau$). Its **expected total discounted profit** is
--
--   $$
--   J_2(\tau,S_2)=\mathbb E\Big[\int_\tau^\infty e^{-\lambda t}\,dX_{2,t}-e^{-\lambda\tau}c_2S_2\Big],
--   \qquad dX_{2,t}=\min(S_2,\mu_2(\theta))\,dt+\sigma\,dB_{2,t},
--   $$
--
--   where the follower earns nothing if $S_2=0$ and $e^{-\lambda\cdot\infty}=0$. A strategy is a **best response** if no feasible strategy has a larger profit, i.e. it attains the maximum in (9).
--
--   **Formalization Note** The paper writes "an investment size $S_2\ge0$". Its optimal size depends on the belief at entry (Proposition 2), so the size is an $\mathcal F_\tau$-measurable random variable. The conditioning on $\pi_0=y_0$ is realized by the prior of $\theta$.
-- source:
--   Sunar, Yu, Kulkarni, Competitive Investment with Bayesian Learning: Choice of Business Size and Timing, SSRN 3408260 (submitted version), feasible strategy p.9, profit (7) p.10, V_2 (9) p.11 (PDF 9–11)

import Mathlib
import Definitions.Def_CompInvestBayes_obsFiltration
import Definitions.Def_CompInvestBayes_discInt

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace CompInvestBayes

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The follower's expected total discounted profit** (7) (SSRN 3408260, p.10, PDF 10) when it
invests at the random time `τ ∈ [0, ∞]` with the random size `S₂ ≥ 0`, under the prior `π₀ = y₀`:

`E[ ∫_τ^∞ e^{-λt} dX_{2,t} − e^{-λτ} c₂ S₂ ]`,

where after entry `dX_{2,t} = min(S₂, µ₂(θ)) dt + σ dB_{2,t}` for `S₂ > 0` ((4), p.8) and the
follower earns nothing if `S₂ = 0` (p.8).

**Formalization Note.** The conditioning on `π₀ = y₀` is realized by the prior `y₀` of the market
state `θ = 1{U < y₀}` on the fixed space. `e^{-λ·∞} := 0`, so a follower that never invests
(`τ = ∞`) earns `0` and pays nothing. The stochastic integral is the pathwise `discInt`. -/
noncomputable def followerValue (p : Params) (σ : ℝ) (E : Setup Ω) (y0 : ℝ)
    (τ : Ω → WithTop ℝ≥0) (S2 : Ω → ℝ) : ℝ :=
  ∫ ω, ((if 0 < S2 ω then
          discInt p.lam σ (min (S2 ω) (mu2 p E y0 ω)) (fun t => E.B2 t ω) (τ ω) ⊤
        else 0)
      - discFactor p.lam (τ ω) * p.c2 * S2 ω) ∂E.P

/-- **A feasible strategy of the follower** (SSRN 3408260, p.9, PDF 9), given the leader's size
`S₁` and the prior `y₀`: "an admissible stopping time τ ∈ R̄₊ at which the follower stops learning
about the favorableness of the market and invests, and (b) an investment size S₂ ≥ 0", where
"A stopping time τ is called admissible for the follower if it is adapted to the natural filtration
F^{X^s_1}".

**Formalization Note.** `τ` takes values in `[0, ∞] = WithTop ℝ≥0` and is a stopping time of the
natural filtration of `X^s_1` (`obsFiltration`). The size `S₂ ≥ 0` is a random variable measurable
with respect to the σ-algebra `F_τ` of events known at the entry time: the paper's optimal size
depends on the belief `π_τ` at entry (Proposition 2), so a constant size would be too narrow, and a
size that may depend on the future would not be a strategy. -/
structure FollowerStrategy (p : Params) (σ : ℝ) (E : Setup Ω) (S1 y0 : ℝ) where
  /-- investment time `τ ∈ [0, ∞]` -/
  τ : Ω → WithTop ℝ≥0
  /-- investment size `S₂` -/
  S2 : Ω → ℝ
  isStoppingTime : IsStoppingTime (obsFiltration p σ E S1 y0) τ
  S2_nonneg : ∀ ω, 0 ≤ S2 ω
  measurable_S2 : Measurable[isStoppingTime.measurableSpace] S2

/-- **Best response of the follower**: the strategy `s` attains the maximum in (9)
(SSRN 3408260, p.11, PDF 11) and in Definition 1 (p.10): no feasible strategy gives the follower a
larger expected total discounted profit (7). -/
def IsFollowerOptimal {p : Params} {σ : ℝ} {E : Setup Ω} {S1 y0 : ℝ}
    (s : FollowerStrategy p σ E S1 y0) : Prop :=
  ∀ s' : FollowerStrategy p σ E S1 y0,
    followerValue p σ E y0 s'.τ s'.S2 ≤ followerValue p σ E y0 s.τ s.S2

end CompInvestBayes


