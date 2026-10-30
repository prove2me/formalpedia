-- Prove2me | Definitions.Def_KellyKolmogorov_IsStationary
-- name    : KellyKolmogorov_IsStationary
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:35:04.719279+00:00
-- url     : https://prove2.me/theorems/f1f48ad8-d174-40ca-8011-eaeea4a4370c
-- title:
--   Stationary process
-- statement:
--   A process $X(t)$, $t\in\mathbb R$, with values in a countable set $\mathcal S$ is **stationary** if for all $n$, all times $t_1,\dots,t_n$ and every shift $\tau\in\mathbb R$ the vector $(X(t_1+\tau),\dots,X(t_n+\tau))$ has the same distribution as $(X(t_1),\dots,X(t_n))$, i.e.
--   $$
--   \mathbb P\bigl(X(t_1+\tau)=j_1,\dots,X(t_n+\tau)=j_n\bigr)=\mathbb P\bigl(X(t_1)=j_1,\dots,X(t_n)=j_n\bigr)\quad\text{for all } j_1,\dots,j_n\in\mathcal S.
--   $$
--
--   Stationarity is the hypothesis under which reversibility is characterized in Theorems 1.3 and 1.8.
--
--   **Formalization Note** "Same distribution" is equality of all cylinder probabilities, which is equivalent because $\mathcal S$ is countable.
-- source:
--   Kelly, Reversibility and Stochastic Networks (Wiley 1979), §1.1, p. 1 (PDF p. 4), definition of a stationary process

import Mathlib
import Definitions.Def_KellyKolmogorov_cylProb

open MeasureTheory

namespace KellyKolmogorov

/-- **Stationary process.**
Kelly, *Reversibility and Stochastic Networks* (Wiley 1979), §1.1, p. 1: "If
`(X(t₁), X(t₂), …, X(tₙ))` has the same distribution as `(X(t₁ + τ), X(t₂ + τ), …, X(tₙ + τ))`
for all `t₁, t₂, …, tₙ, τ ∈ 𝒯` then the stochastic process `X(t)` is stationary."

**Formalization Note.** Time is `ℝ`. "Same distribution" is equality of all cylinder
probabilities `cylProb` (the state space is countable). -/
def IsStationary {Ω 𝒮 : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : ℝ → Ω → 𝒮) : Prop :=
  ∀ (n : ℕ) (t : Fin n → ℝ) (τ : ℝ) (j : Fin n → 𝒮),
    cylProb μ X (fun i => t i + τ) j = cylProb μ X t j

end KellyKolmogorov


