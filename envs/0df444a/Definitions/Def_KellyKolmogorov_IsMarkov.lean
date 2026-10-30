-- Prove2me | Definitions.Def_KellyKolmogorov_IsMarkov
-- name    : KellyKolmogorov_IsMarkov
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:36:03.14268+00:00
-- url     : https://prove2.me/theorems/1e1282e4-7704-4279-b22d-b884e4f6f2f8
-- title:
--   Markov property of a process
-- statement:
--   A process $X(t)$, $t\in\mathbb R$, with values in a countable set $\mathcal S$ is a **Markov process** if for every $n\ge1$, all times $t_1<t_2<\dots<t_n<t_{n+1}$ and all states $j_1,\dots,j_{n+1}$,
--   $$
--   \mathbb P\bigl(X(t_{n+1})=j_{n+1}\mid X(t_1)=j_1,\dots,X(t_n)=j_n\bigr)=\mathbb P\bigl(X(t_{n+1})=j_{n+1}\mid X(t_n)=j_n\bigr)
--   $$
--   whenever the conditioning event $\{X(t_1)=j_1,\dots,X(t_n)=j_n\}$ has positive probability.
--
--   The state at a given time carries all the information about the past that is of use in predicting the future.
--
--   **Formalization Note** Conditional probabilities are Mathlib's `ProbabilityTheory.cond`, used only when the conditioning event has positive measure. Times are indexed by `Fin (n+2)` (the book's $n$ is $n+1\ge1$).
-- source:
--   Kelly, Reversibility and Stochastic Networks (Wiley 1979), §1.1, p. 1 (PDF p. 4), definition of a Markov process

import Mathlib

open MeasureTheory

namespace KellyKolmogorov

/-- **Markov property of a process.**
Kelly, *Reversibility and Stochastic Networks* (Wiley 1979), §1.1, p. 1: "The stochastic process
`X(t)` is a Markov process if for `t₁ < t₂ < ⋯ < tₙ < tₙ₊₁` the joint distribution of
`(X(t₁), X(t₂), …, X(tₙ), X(tₙ₊₁))` is such that
`P(X(tₙ₊₁) = jₙ₊₁ | X(t₁) = j₁, X(t₂) = j₂, …, X(tₙ) = jₙ) = P(X(tₙ₊₁) = jₙ₊₁ | X(tₙ) = jₙ)`
whenever the conditioning event `(X(t₁) = j₁, X(t₂) = j₂, …, X(tₙ) = jₙ)` has positive
probability."

Here the times are `t 0 < t 1 < ⋯ < t (n+1)` (so the book's `n` is `n + 1`, every `n ≥ 1`), the
conditioning event is `{X (t i) = j i for i ≤ n}` and the last time is `t (n+1)`.

**Formalization Note.** `P(B | A)` is Mathlib's conditional measure
`ProbabilityTheory.cond μ A B = μ (A ∩ B) / μ A`, used only when `μ A ≠ 0`. -/
def IsMarkov {Ω 𝒮 : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : ℝ → Ω → 𝒮) : Prop :=
  ∀ (n : ℕ) (t : Fin (n + 2) → ℝ) (j : Fin (n + 2) → 𝒮), StrictMono t →
    μ {ω | ∀ i : Fin (n + 1), X (t i.castSucc) ω = j i.castSucc} ≠ 0 →
    ProbabilityTheory.cond μ {ω | ∀ i : Fin (n + 1), X (t i.castSucc) ω = j i.castSucc}
        {ω | X (t (Fin.last (n + 1))) ω = j (Fin.last (n + 1))} =
      ProbabilityTheory.cond μ {ω | X (t (Fin.last n).castSucc) ω = j (Fin.last n).castSucc}
        {ω | X (t (Fin.last (n + 1))) ω = j (Fin.last (n + 1))}

end KellyKolmogorov


