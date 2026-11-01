-- Prove2me | Definitions.Def_WiretapFeedback_testBeta
-- name    : WiretapFeedback_testBeta
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:23:48.921807+00:00
-- url     : https://prove2.me/theorems/95f1e53e-6106-4803-83a5-e032e9ce5d82
-- title:
--   Optimal type-II error $\beta_\epsilon(P,Q)$
-- statement:
--   Let $P$ and $Q$ be distributions on the same alphabet $\mathcal X$. A **stochastic test** is a function $T(0|\cdot):\mathcal X\to[0,1]$, the probability of accepting the null hypothesis $P$ on observing $x$. Write $P[T]=\sum_x P(x)T(0|x)$ and $Q[T]=\sum_x Q(x)T(0|x)$. For $0\le\epsilon<1$,
--   $$
--   \beta_\epsilon(P,Q)=\inf_{T:\ P[T]\ge 1-\epsilon} Q[T],
--   $$
--   the smallest type-II error probability among tests whose type-I error probability is at most $\epsilon$.
--
--   The constant test $T\equiv1$ is feasible, so $0\le\beta_\epsilon(P,Q)\le1$.
--
--   **Formalization Note** Tests are functions into $[0,1]\subset[0,\infty]$ and sums are $[0,\infty]$-valued; the constraint $P[T]\ge1-\epsilon$ is stated with $1-\epsilon$ converted to $[0,\infty]$, which is exact for $0\le\epsilon<1$.
-- source:
--   Hayashi–Tyagi–Watanabe, Strong Converse for a Degraded Wiretap Channel via Active Hypothesis Testing, arXiv:1410.0443v1, §III, p.2 (definition of β_ϵ(P, Q))

import Mathlib

open scoped ENNReal

namespace WiretapFeedback

/-- The optimal type-II error `β_ϵ(P, Q)` of a simple binary hypothesis test, Hayashi–Tyagi–Watanabe,
arXiv:1410.0443v1, §III, p. 2: a (stochastic) test is a function `T(0|·) : 𝒳 → [0, 1]`, the
probability of accepting the null hypothesis; `P[T] = Σ_x P(x) T(0|x)` and
`Q[T] = Σ_x Q(x) T(0|x)`, and
`β_ϵ(P, Q) = inf_{T : P[T] ≥ 1 − ϵ} Q[T]`.

**Formalization Note** The test `T` is any function `α → ℝ≥0∞` bounded by `1` (the value
`T(0|x)`); sums are `ℝ≥0∞`-valued `tsum`s, so no summability condition is needed. The paper
defines `β_ϵ` for `0 ≤ ϵ < 1`; the constraint `P[T] ≥ 1 − ϵ` is written
`ENNReal.ofReal (1 - ϵ) ≤ P[T]`, which is exact on that range. The constant test `T ≡ 1` is
feasible, so the infimum is over a nonempty set and `β_ϵ(P, Q) ≤ 1`. -/
noncomputable def testBeta {α : Type} (ε : ℝ) (P Q : PMF α) : ℝ≥0∞ :=
  ⨅ (T : α → ℝ≥0∞) (_ : ∀ a, T a ≤ 1) (_ : ENNReal.ofReal (1 - ε) ≤ ∑' a, P a * T a),
    ∑' a, Q a * T a

end WiretapFeedback


