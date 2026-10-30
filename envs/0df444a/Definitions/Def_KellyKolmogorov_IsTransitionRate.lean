-- Prove2me | Definitions.Def_KellyKolmogorov_IsTransitionRate
-- name    : KellyKolmogorov_IsTransitionRate
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:38:59.227315+00:00
-- url     : https://prove2.me/theorems/a1c0046d-edb8-44a8-ad87-ff4acc5596f2
-- title:
--   Transition rates $q(j,k)$ of a process
-- statement:
--   Let $X(t)$, $t\in\mathbb R$, be a process with values in a countable set $\mathcal S$. A family $q(j,k)\ge0$, $j,k\in\mathcal S$, is the family of **transition rates** of $X$ if
--
--   1. $q(j,j)=0$ for every $j$;
--   2. for $j\ne k$ and every time $t$ with $\mathbb P(X(t)=j)>0$,
--   $$
--   q(j,k)=\lim_{\tau\downarrow0}\frac{\mathbb P\bigl(X(t+\tau)=k\mid X(t)=j\bigr)}{\tau}.
--   $$
--
--   The rates are the data in terms of which Kolmogorov's criterion (Theorem 1.8) is stated.
--
--   **Formalization Note** Rates are typed as nonnegative reals. The limit is one-sided. The rates are given together with this limit property, so they are tied to the process and no default value is used when a limit fails to exist.
-- source:
--   Kelly, Reversibility and Stochastic Networks (Wiley 1979), §1.1, p. 3 (PDF p. 6), definition of the transition rate

import Mathlib
import Definitions.Def_KellyKolmogorov_transProb

open MeasureTheory Filter Topology
open scoped NNReal

namespace KellyKolmogorov

/-- **Transition rates of a process.**
Kelly, *Reversibility and Stochastic Networks* (Wiley 1979), §1.1, p. 3: "Define the transition
rate from state `j` to state `k` to be
`q(j, k) = lim_{τ→0} P(X(t + τ) = k | X(t) = j) / τ`, `j ≠ k`. It will be convenient to let
`q(j, j) = 0`."

`IsTransitionRate μ X q` says that `q` is the family of transition rates of `X`:
1. `q(j, j) = 0` for every state `j`;
2. for `j ≠ k` and every time `t` with `P(X(t) = j) > 0`,
   `P(X(t + τ) = k | X(t) = j) / τ → q(j, k)` as `τ ↓ 0`.

**Formalization Note.** Rates are limits of nonnegative ratios and are typed in `ℝ≥0`. The
limit is one-sided (`τ ↓ 0`), since the transition probability concerns a forward step. The
rates are given together with this limit property, so `q` is tied to `X`; no default value is
used when a limit fails to exist. -/
def IsTransitionRate {Ω 𝒮 : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : ℝ → Ω → 𝒮)
    (q : 𝒮 → 𝒮 → ℝ≥0) : Prop :=
  (∀ j, q j j = 0) ∧
    ∀ j k : 𝒮, j ≠ k → ∀ t : ℝ, μ {ω | X t ω = j} ≠ 0 →
      Tendsto (fun τ : ℝ => (transProb μ X t τ j k).toReal / τ) (𝓝[>] 0) (𝓝 (q j k : ℝ))

end KellyKolmogorov


