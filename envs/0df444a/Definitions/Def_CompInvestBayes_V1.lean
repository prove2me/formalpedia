-- Prove2me | Definitions.Def_CompInvestBayes_V1
-- name    : CompInvestBayes_V1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:07:13.298284+00:00
-- url     : https://prove2.me/theorems/fc4068fa-cbb0-4a4d-93dc-55e24858b398
-- title:
--   Leader's profit $H(S_1,y_0)$ (15) and equilibrium value $V_1(y_0)=\max_{S_1\ge0}H(S_1,y_0)$
-- statement:
--   The leader invests $S_1\ge0$ at time $0$ at cost $c_1S_1$. If the follower enters at $\tau$, the leader's expected total discounted profit is
--
--   $$
--   \mathbb E\Big[\int_0^\tau e^{-\lambda t}\,dX^s_{1,t}+\int_\tau^\infty e^{-\lambda t}\,dX_{1,t}-c_1S_1\Big],
--   \qquad dX_{1,t}=\min(S_1,\mu_1(\theta))\,dt+\sigma\,dB_{1,t}\ \ (t\ge\tau).
--   $$
--
--   A **best-response selection** chooses, for every $S_1\ge0$ and every prior $y_0\in[0,1]$, a best response of the follower. Given one, $H(S_1,y_0)$ is the leader's profit against the selected response, and the leader's **equilibrium value** is
--
--   $$
--   V_1(y_0)=\max_{S_1\ge0}H(S_1,y_0).
--   $$
--
--   **Formalization Note** The maximum is a supremum (`sSup`) over $S_1\ge0$; the payoffs are bounded above by $\mu_H/\lambda$. The leader's profit depends on the follower's strategy only through $\tau$.
-- source:
--   Sunar, Yu, Kulkarni, Competitive Investment with Bayesian Learning: Choice of Business Size and Timing, SSRN 3408260 (submitted version), leader's problem (8), p.10; H (15) and V_1, p.13 (PDF 10, 13); Definition 1, p.10

import Mathlib
import Definitions.Def_CompInvestBayes_FollowerStrategy

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace CompInvestBayes

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The leader's expected total discounted profit** (8), (15) (SSRN 3408260, pp.10, 13,
PDF 10, 13) for the size `S₁ ≥ 0` when the follower enters at `τ`, under the prior `π₀ = y₀`:

`E[ ∫_0^τ e^{-λt} dX^s_{1,t} + ∫_τ^∞ e^{-λt} dX_{1,t} − c₁ S₁ ]`,

with `dX^s_{1,t} = min(S₁, µ(θ)) dt + σ dB^s_{1,t}` before entry ((1), p.7) and
`dX_{1,t} = min(S₁, µ₁(θ)) dt + σ dB_{1,t}` after entry ((3), p.8); the leader earns nothing if
`S₁ = 0` (p.8).

**Formalization Note.** The stochastic integrals are the pathwise `discInt`; `τ = ∞` (the follower
never enters) gives `∫_0^∞` before entry and `0` after. -/
noncomputable def leaderPayoff (p : Params) (σ : ℝ) (E : Setup Ω) (S1 y0 : ℝ)
    (τ : Ω → WithTop ℝ≥0) : ℝ :=
  ∫ ω, ((if 0 < S1 then
          discInt p.lam σ (min S1 (muTot p E y0 ω)) (fun t => E.Bs t ω) 0 (τ ω)
            + discInt p.lam σ (min S1 (mu1 p E y0 ω)) (fun t => E.B1 t ω) (τ ω) ⊤
        else 0)
      - p.c1 * S1) ∂E.P

/-- **A best-response selection of the follower**: for every leader size `S₁ ≥ 0` and every prior
`y₀ ∈ [0, 1]`, `br S₁ y₀` is a follower strategy attaining the maximum in (9)
(SSRN 3408260, p.11, PDF 11; Definition 1, p.10). -/
def IsBestResponseSelection {p : Params} {σ : ℝ} {E : Setup Ω}
    (br : (S1 y0 : ℝ) → FollowerStrategy p σ E S1 y0) : Prop :=
  ∀ S1 : ℝ, 0 ≤ S1 → ∀ y0 ∈ Set.Icc (0 : ℝ) 1, IsFollowerOptimal (br S1 y0)

/-- **The leader's expected total discounted profit in equilibrium**
`V₁(y₀) := max_{S₁ ≥ 0} H(S₁, y₀)` (SSRN 3408260, p.13, PDF 13), where `H(S₁, y₀)` (15) is the
leader's profit "subject to the follower's optimal policy", here the response `br S₁ y₀` of a
best-response selection `br`.

**Formalization Note.** `max` is `sSup` over `S₁ ≥ 0`; the leader's payoffs are bounded above
(by `µ_H / λ`), so this is the supremum. The leader's payoff depends on the follower's strategy only
through its entry time `τ`. -/
noncomputable def V1 (p : Params) (σ : ℝ) (E : Setup Ω)
    (br : (S1 y0 : ℝ) → FollowerStrategy p σ E S1 y0) (y0 : ℝ) : ℝ :=
  sSup ((fun S1 => leaderPayoff p σ E S1 y0 (br S1 y0).τ) '' Set.Ici (0 : ℝ))

end CompInvestBayes


