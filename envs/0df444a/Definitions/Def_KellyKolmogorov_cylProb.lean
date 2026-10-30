-- Prove2me | Definitions.Def_KellyKolmogorov_cylProb
-- name    : KellyKolmogorov_cylProb
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:34:34.721554+00:00
-- url     : https://prove2.me/theorems/462c6775-fca6-44f3-ae80-db87e0bfec1e
-- title:
--   Cylinder probability $\mathbb P(X(t_1)=j_1,\dots,X(t_n)=j_n)$
-- statement:
--   Let $X(t)$, $t\in\mathbb R$, be a stochastic process on a probability space $(\Omega,\mathcal F,\mathbb P)$ with values in a countable state space $\mathcal S$. For times $t_1,\dots,t_n\in\mathbb R$ and states $j_1,\dots,j_n\in\mathcal S$ the **cylinder probability** is
--   $$
--   \mathbb P\bigl(X(t_1)=j_1,\ X(t_2)=j_2,\ \dots,\ X(t_n)=j_n\bigr).
--   $$
--
--   Because $\mathcal S$ is countable, the distribution of the random vector $(X(t_1),\dots,X(t_n))$ is determined by these numbers. Two such vectors have the same distribution exactly when all their cylinder probabilities agree; this is how stationarity and reversibility are stated.
--
--   **Formalization Note** The process is a family `X : ℝ → Ω → 𝒮`; the value is in $[0,\infty]$ (`ℝ≥0∞`), as a measure of a set.
-- source:
--   Kelly, Reversibility and Stochastic Networks (Wiley 1979), §1.1, p. 1 (PDF p. 4): finite-dimensional distributions of X(t)

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace KellyKolmogorov

/-- **Cylinder probability of a process on a countable state space.**
Kelly, *Reversibility and Stochastic Networks* (Wiley 1979), §1.1, p. 1: "Let `X(t)` be a
stochastic process taking values in a countable state space `𝒮` for `t ∈ 𝒯`. Thus
`(X(t₁), X(t₂), …, X(tₙ))` has a known distribution for `t₁, t₂, …, tₙ ∈ 𝒯`."

`cylProb μ X t j = μ {ω | X (t i) ω = j i for every i}` is the probability that the random
vector `(X(t₁), …, X(tₙ))` takes the value `(j₁, …, jₙ)`.

**Formalization Note.** The process is a family `X : ℝ → Ω → 𝒮` of maps on a probability space
`(Ω, μ)` (continuous time, `𝒯 = ℝ`). Because `𝒮` is countable, the law of the random vector
`(X(t₁), …, X(tₙ))` on the countable set `𝒮ⁿ` is determined by these point masses, so two such
vectors "have the same distribution" exactly when all their cylinder probabilities agree. -/
def cylProb {Ω 𝒮 : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : ℝ → Ω → 𝒮) {n : ℕ}
    (t : Fin n → ℝ) (j : Fin n → 𝒮) : ℝ≥0∞ :=
  μ {ω | ∀ i, X (t i) ω = j i}

end KellyKolmogorov


