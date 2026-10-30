-- Prove2me | Definitions.Def_KellyKolmogorov_transProb
-- name    : KellyKolmogorov_transProb
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:36:16.071294+00:00
-- url     : https://prove2.me/theorems/7fdeb66c-9591-448e-9727-94a5594a02e0
-- title:
--   Transition probability $\mathbb P(X(t+\tau)=k\mid X(t)=j)$
-- statement:
--   For a process $X(t)$, $t\in\mathbb R$, with values in a countable set $\mathcal S$, times $t,\tau\in\mathbb R$ and states $j,k\in\mathcal S$, this is the conditional probability
--   $$
--   \mathbb P\bigl(X(t+\tau)=k\mid X(t)=j\bigr)=\frac{\mathbb P(X(t)=j,\ X(t+\tau)=k)}{\mathbb P(X(t)=j)} .
--   $$
--
--   It enters the definitions of time homogeneity and of the transition rates.
--
--   **Formalization Note** Mathlib's `ProbabilityTheory.cond`, with values in $[0,\infty]$; it is $0$ when $\mathbb P(X(t)=j)=0$, so every statement that uses it assumes $\mathbb P(X(t)=j)>0$.
-- source:
--   Kelly, Reversibility and Stochastic Networks (Wiley 1979), §1.1, pp. 1–3 (PDF pp. 4–6)

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace KellyKolmogorov

/-- **Transition probability over a time step `τ`.**
Kelly, *Reversibility and Stochastic Networks* (Wiley 1979), §1.1, pp. 1–3: the quantity
`P(X(t + τ) = k | X(t) = j)`.

`transProb μ X t τ j k = P(X(t + τ) = k | X(t) = j)`.

**Formalization Note.** Mathlib's conditional measure `ProbabilityTheory.cond`; it is the zero
measure when `μ {X t = j} = 0`, so every statement using `transProb` assumes
`μ {X t = j} ≠ 0`, as the book's conditional probabilities do. -/
noncomputable def transProb {Ω 𝒮 : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℝ → Ω → 𝒮) (t τ : ℝ) (j k : 𝒮) : ℝ≥0∞ :=
  ProbabilityTheory.cond μ {ω | X t ω = j} {ω | X (t + τ) ω = k}

end KellyKolmogorov


