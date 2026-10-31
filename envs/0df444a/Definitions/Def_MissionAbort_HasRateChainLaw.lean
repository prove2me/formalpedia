-- Prove2me | Definitions.Def_MissionAbort_HasRateChainLaw
-- name    : MissionAbort_HasRateChainLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:48:50.739564+00:00
-- url     : https://prove2.me/theorems/7eaaaf3e-6c2b-4b9c-8fb4-bbd4cf0b55ca
-- title:
--   Finite-dimensional law of a continuous-time chain on a set of times
-- statement:
--   A process $X$ has the law of a continuous-time Markov chain with initial law $\pi_0$ and rate matrix $Q$ on the set of times $\mathbb T$ if, for every strictly increasing tuple $0=t_0<t_1<\dots<t_k$ in $\mathbb T$ and all states $s_0,\dots,s_k$,
--   $$
--   \mathbb P\big(X(t_i)=s_i\ \forall i\big)=\pi_0(s_0)\prod_{i=0}^{k-1}\big[e^{(t_{i+1}-t_i)Q}\big]_{s_is_{i+1}}.
--   $$
--   A genuine chain satisfies this for every set of nonnegative times containing $0$.
--
--   **Formalization Note** The start is random, which is what (4) requires. Requiring the identity along strictly increasing tuples only loses nothing: a repeated time adds no information.
-- source:
--   Sun, Hu & Ye, Optimal Abort Policy for Mission-Critical Systems under Imperfect Condition Monitoring, arXiv:2505.03225v1, §4.1, pp.13–14

import Mathlib
import Definitions.Def_MissionAbort_pathWeight

namespace MissionAbort

open MeasureTheory

/-- The process `X` has, at the times of the set `𝕋`, the finite-dimensional laws of a continuous-time
Markov chain with initial law `π₀` and rate matrix `Q`: for every strictly increasing tuple of
times in `𝕋` starting at `0`, the joint law of `X` along the tuple is `pathWeight π₀ Q`.

**Formalization Note.** A genuine CTMC satisfies this for every set of nonnegative times containing
`0`, in particular for a finite set. Used for the surrogate of Sun, Hu & Ye, arXiv:2505.03225v1,
§4.1, pp.13–14, whose start (4) is random. -/
def HasRateChainLaw {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω]
    (π₀ : ι → ℝ) (Q : Matrix ι ι ℝ) (𝕋 : Set ℝ) (X : ℝ → Ω → ι) (μ : Measure Ω) : Prop :=
  ∀ (k : ℕ) (t : Fin (k + 1) → ℝ) (s : Fin (k + 1) → ι), t 0 = 0 → StrictMono t → (∀ i, t i ∈ 𝕋) →
    μ.real {ω | ∀ i, X (t i) ω = s i} = pathWeight π₀ Q t s

end MissionAbort


