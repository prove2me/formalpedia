-- Prove2me | Definitions.Def_KellyKolmogorov_IsReversible
-- name    : KellyKolmogorov_IsReversible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:35:43.403247+00:00
-- url     : https://prove2.me/theorems/45eef351-b741-4109-ad67-a2347cd5ecd4
-- title:
--   Reversible process
-- statement:
--   A process $X(t)$, $t\in\mathbb R$, with values in a countable set $\mathcal S$ is **reversible** if for all $n$, all times $t_1,\dots,t_n$ and every $\tau\in\mathbb R$ the vector $(X(t_1),\dots,X(t_n))$ has the same distribution as $(X(\tau-t_1),\dots,X(\tau-t_n))$:
--   $$
--   \mathbb P\bigl(X(t_1)=j_1,\dots,X(t_n)=j_n\bigr)=\mathbb P\bigl(X(\tau-t_1)=j_1,\dots,X(\tau-t_n)=j_n\bigr)\quad\text{for all } j_1,\dots,j_n\in\mathcal S.
--   $$
--
--   Intuitively, a film of the process run backwards is statistically indistinguishable from the film run forwards. This is the property characterized by detailed balance (Theorem 1.3) and by Kolmogorov's criterion (Theorem 1.8).
--
--   **Formalization Note** This is the statement about finite-dimensional distributions, not the detailed balance conditions; "same distribution" is equality of all cylinder probabilities.
-- source:
--   Kelly, Reversibility and Stochastic Networks (Wiley 1979), §1.2, Definition, p. 5 (PDF p. 8)

import Mathlib
import Definitions.Def_KellyKolmogorov_cylProb

open MeasureTheory

namespace KellyKolmogorov

/-- **Reversible process.**
Kelly, *Reversibility and Stochastic Networks* (Wiley 1979), §1.2, Definition, p. 5: "A
stochastic process `X(t)` is reversible if `(X(t₁), X(t₂), …, X(tₙ))` has the same distribution
as `(X(τ − t₁), X(τ − t₂), …, X(τ − tₙ))` for all `t₁, t₂, …, tₙ, τ ∈ 𝒯`."

**Formalization Note.** Time is `ℝ`. "Same distribution" is equality of all cylinder
probabilities `cylProb` (the state space is countable). This is the statement about
finite-dimensional distributions, not the detailed balance conditions. -/
def IsReversible {Ω 𝒮 : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : ℝ → Ω → 𝒮) : Prop :=
  ∀ (n : ℕ) (t : Fin n → ℝ) (τ : ℝ) (j : Fin n → 𝒮),
    cylProb μ X t j = cylProb μ X (fun i => τ - t i) j

end KellyKolmogorov


