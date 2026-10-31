-- Prove2me | Definitions.Def_UnbiasedTimeAvg_levelEstimator
-- name    : UnbiasedTimeAvg_levelEstimator
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:20:32.410684+00:00
-- url     : https://prove2.me/theorems/7e549f8f-4c92-40af-8d8f-3791e7d78dae
-- title:
--   The level estimators $f_{k,l}$
-- statement:
--   For $k\ge1$, a burn-in $b'=b'(k)$ and a level $l\ge0$,
--   $$f_{k,l}:=\frac{1}{k-b'}\sum_{i=b'}^{k-1}f\big(X_{i,k(2^l-1)}\big),\qquad(3.1)$$
--   the time average of the chain started $k(2^l-1)$ steps before time $0$. In particular $f_{k,0}=\frac1{k-b'}\sum_{i=b'}^{k-1}f(X_i)$ (3.2) is a standard estimator with burn-in $b'$. As $l\to\infty$, $\mathbb E f_{k,l}\to\mu$; consecutive levels share their last noise variables, so $f_{k,l+1}-f_{k,l}$ is small.
--
--   **Formalization Note** The shift $k(2^l-1)$ is a natural number (no truncation since $2^l\ge1$).
-- source:
--   N. Kahalé, Unbiased time-average estimators for Markov chains, arXiv:2209.09581v1 (20 Sep 2022), (3.1)–(3.2), p.8

import Mathlib
import Definitions.Def_UnbiasedTimeAvg_coupledChain

namespace UnbiasedTimeAvg

/-- **The level estimators `f_{k,l}`.** Kahalé, arXiv:2209.09581v1, (3.1), p.8: "For `k ≥ 1` and
`l ≥ 0`, let `f_{k,l} := (1/(k − b′(k))) Σ_{i=b′(k)}^{k−1} f(X_{i,k(2^l−1)})`."

`levelEstimator g x₀ U f b' k l` is the time average, over the times `b′ ≤ i ≤ k − 1`, of the chain
started at time `−k(2^l − 1)`. For `l = 0` it is the standard estimator with burn-in `b′` ((3.2)).

**Formalization Note.** `b'` is the value `b′(k)` at the fixed `k`. `k * (2 ^ l - 1)` is a natural
number (no truncation since `2^l ≥ 1`), cast to `ℤ` as the starting shift `m`. -/
noncomputable def levelEstimator {Ω F F' : Type*} (g : F → F' → F) (x₀ : F)
    (U : ℤ → Ω → F') (f : F → ℝ) (b' k l : ℕ) : Ω → ℝ :=
  fun ω => (1 / ((k : ℝ) - b')) *
    ∑ i ∈ Finset.Ico b' k, f (coupledChain g x₀ U i ((k * (2 ^ l - 1) : ℕ) : ℤ) ω)

end UnbiasedTimeAvg


