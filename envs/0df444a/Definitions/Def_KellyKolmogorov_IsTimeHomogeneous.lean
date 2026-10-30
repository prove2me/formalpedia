-- Prove2me | Definitions.Def_KellyKolmogorov_IsTimeHomogeneous
-- name    : KellyKolmogorov_IsTimeHomogeneous
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:37:18.935451+00:00
-- url     : https://prove2.me/theorems/332f27e8-ccf7-4e3e-902f-1059c9642d82
-- title:
--   Time-homogeneous process
-- statement:
--   A process $X(t)$, $t\in\mathbb R$, with values in a countable set $\mathcal S$ is **time homogeneous** if the transition probability $\mathbb P(X(t+\tau)=k\mid X(t)=j)$ does not depend on $t$: for every $\tau>0$, all states $j,k$ and all times $s,t$ with $\mathbb P(X(s)=j)>0$ and $\mathbb P(X(t)=j)>0$,
--   $$
--   \mathbb P\bigl(X(s+\tau)=k\mid X(s)=j\bigr)=\mathbb P\bigl(X(t+\tau)=k\mid X(t)=j\bigr).
--   $$
--
--   **Formalization Note** Forward steps $\tau>0$ (the case $\tau=0$ is trivial); the condition is imposed only at times at which the conditioning event has positive probability.
-- source:
--   Kelly, Reversibility and Stochastic Networks (Wiley 1979), §1.1, p. 1 (PDF p. 4), definition of a time homogeneous Markov process

import Mathlib
import Definitions.Def_KellyKolmogorov_transProb

open MeasureTheory

namespace KellyKolmogorov

/-- **Time homogeneity.**
Kelly, *Reversibility and Stochastic Networks* (Wiley 1979), §1.1, p. 1: "A Markov process is
time homogeneous if `P(X(t + τ) = k | X(t) = j)` does not depend upon `t`".

For every step `τ > 0` and states `j, k`, the transition probability
`P(X(t + τ) = k | X(t) = j)` takes the same value at all times `t` at which it is defined
(`P(X(t) = j) > 0`).

**Formalization Note.** Forward steps `τ > 0` (the transition probability of a Markov process);
`τ = 0` is trivial. -/
def IsTimeHomogeneous {Ω 𝒮 : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : ℝ → Ω → 𝒮) :
    Prop :=
  ∀ (s t τ : ℝ) (j k : 𝒮), 0 < τ → μ {ω | X s ω = j} ≠ 0 → μ {ω | X t ω = j} ≠ 0 →
    transProb μ X s τ j k = transProb μ X t τ j k

end KellyKolmogorov


