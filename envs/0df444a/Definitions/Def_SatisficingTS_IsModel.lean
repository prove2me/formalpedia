-- Prove2me | Definitions.Def_SatisficingTS_IsModel
-- name    : SatisficingTS_IsModel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:22:51.174995+00:00
-- url     : https://prove2.me/theorems/7d659c85-4cf5-4559-8f27-553bb3e8c4d2
-- title:
--   The Bayesian sequential decision model of §2
-- statement:
--   An agent chooses actions $A_0, A_1, \dots$ from an action set $\mathcal A$ and observes outcomes $Y_t\in\mathcal Y$. On a probability space $(\Omega,\mathbb P)$ there are
--
--   1. a parameter $\theta$ with values in a measurable space $\Theta$, fixed over time;
--   2. disturbances $W_0, W_1, \dots$ in a measurable space $\mathcal W$, which are independent and identically distributed, and each $W_t$ is independent of $\theta$;
--   3. the policy's exogenous random variable $\xi$ in a measurable space $\Xi$, independent of $\theta$ and of the disturbance sequence $(W_t)_{t\ge0}$.
--
--   A known **system function** $g:\mathcal A\times\Theta\times\mathcal W\to\mathcal Y$ produces the outcomes,
--   $$
--   Y_t=g(A_t,\theta,W_t),
--   $$
--   and a **policy** $\psi=(\psi_t)_{t\ge0}$ maps the history $\mathcal H_{t-1}=(A_0,Y_0,\dots,A_{t-1},Y_{t-1})$ and $\xi$ to the next action, $A_t=\psi_t(\mathcal H_{t-1},\xi)$.
--
--   The predicate $\mathrm{IsModel}(\mathbb P,\theta,W,\xi,g,\psi)$ collects these probabilistic assumptions together with measurability of $\theta$, every $W_t$, $\xi$, of $g$ in $(a,\theta,w)$ and of every $\psi_t$ in $(\mathcal H_{t-1},\xi)$. It is the setting of every result of the paper.
--
--   **Formalization Note** Measurability is not stated in the paper; it is the standing convention that makes $A_t$ and $Y_t$ random variables. The independence assumptions are taken in their weakest literal form; the usual joint forms imply them. $\psi_t$ receives the history as a $t$-tuple (0-based).
-- source:
--   Russo & Van Roy, Satisficing in Time-Sensitive Bandit Learning, arXiv:1803.02855v2, §2, pp.4–5 (system function Y_t = g(A_t, θ, W_t), iid disturbances independent of θ, policy A_t = ψ_t(H_{t−1}, ξ), ξ independent of θ and the disturbances)

import Mathlib
open MeasureTheory ProbabilityTheory

namespace SatisficingTS

/-- **The probabilistic model of §2** (Russo & Van Roy, *Satisficing in Time-Sensitive Bandit
Learning*, arXiv:1803.02855v2, §2, pp.4–5).

On a probability space `(Ω, P)` there are a parameter `θ : Ω → Θ` "fixed over time", an iid
sequence of disturbances `W : ℕ → Ω → 𝒲` that is independent of `θ`, and the policy's exogenous
random variable `ξ : Ω → Ξ`, "independent of θ and the disturbances (Wt)t∈N0" (p.5). Outcomes are
`Y_t = g(A_t, θ, W_t)` for a known system function `g`, and actions are `A_t = ψ_t(H_{t−1}, ξ)` for
a policy `ψ = (ψ_t)_{t∈ℕ₀}`. `IsModel P θ W ξ g ψ` collects these assumptions:

* `θ`, every `W_t` and `ξ` are measurable;
* `g`, as a function of `(a, θ, w)`, and every `ψ_t`, as a function of `(history, ξ)`, are
  measurable;
* the `W_t` are mutually independent and identically distributed;
* every `W_t` is independent of `θ`;
* `ξ` is independent of `θ` and independent of the disturbance sequence `(W_t)_t`.

**Formalization Note.** The paper does not state measurability; it is the standing convention
that makes `A_t`, `Y_t` random variables. `ψ_t` receives the history `H_{t−1}` as a function
`Fin t → 𝒜 × 𝒴` (0-based: `H_{t−1}` has `t` entries `(A_0,Y_0),…,(A_{t−1},Y_{t−1})`). The
independence assumptions are taken in their weakest literal form ("The disturbances Wt are
independent of θ": each `W_t` is; "ξ … independent of θ and the disturbances": of `θ` and of the
sequence `(W_t)_t`); the usual joint forms imply them. -/
structure IsModel {Ω Θ 𝒲 Ξ 𝒜 𝒴 : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    [MeasurableSpace 𝒲] [MeasurableSpace Ξ] [MeasurableSpace 𝒜] [MeasurableSpace 𝒴]
    (P : Measure Ω) (θ : Ω → Θ) (W : ℕ → Ω → 𝒲) (ξ : Ω → Ξ)
    (g : 𝒜 → Θ → 𝒲 → 𝒴) (ψ : (t : ℕ) → (Fin t → 𝒜 × 𝒴) → Ξ → 𝒜) : Prop where
  measurable_theta : Measurable θ
  measurable_W : ∀ t, Measurable (W t)
  measurable_xi : Measurable ξ
  measurable_g : Measurable (fun p : 𝒜 × Θ × 𝒲 => g p.1 p.2.1 p.2.2)
  measurable_psi : ∀ t, Measurable (fun p : (Fin t → 𝒜 × 𝒴) × Ξ => ψ t p.1 p.2)
  iIndepFun_W : iIndepFun W P
  identDistrib_W : ∀ t, IdentDistrib (W t) (W 0) P P
  indepFun_W_theta : ∀ t, IndepFun (W t) θ P
  indepFun_xi_theta : IndepFun ξ θ P
  indepFun_xi_W : IndepFun ξ (fun ω t => W t ω) P

end SatisficingTS


