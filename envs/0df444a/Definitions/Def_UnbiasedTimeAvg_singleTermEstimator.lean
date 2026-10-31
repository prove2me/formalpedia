-- Prove2me | Definitions.Def_UnbiasedTimeAvg_singleTermEstimator
-- name    : UnbiasedTimeAvg_singleTermEstimator
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:21:31.984006+00:00
-- url     : https://prove2.me/theorems/e0b88e66-c8f2-48ee-bcff-f57f7fedf683
-- title:
--   The single term estimator $Z_k=(f_{k,N+1}-f_{k,N})/p_N$
-- statement:
--   Given a probability distribution $(p_l)_{l\ge0}$ and an $\mathbb N$-valued random variable $N$,
--   $$Z_k:=\frac{f_{k,N+1}-f_{k,N}}{p_N}.\qquad(3.3)$$
--   In the paper $N$ is independent of $(U_i)_{i\in\mathbb Z}$ with $\Pr(N=l)=p_l$; under suitable conditions $Z_k$ is an unbiased estimator of the negated bias $\mu-\mathbb E f_{k,0}$.
--
--   **Formalization Note** The definition is the formula only; the law of $N$ and its independence from the noise are hypotheses of the theorems.
-- source:
--   N. Kahalé, Unbiased time-average estimators for Markov chains, arXiv:2209.09581v1 (20 Sep 2022), (3.3), p.8

import Mathlib
import Definitions.Def_UnbiasedTimeAvg_levelEstimator

namespace UnbiasedTimeAvg

/-- **The single term (RMLMC) estimator `Z_k`.** Kahalé, arXiv:2209.09581v1, (3.3), p.8:
`Z_k^{(b′(k))} := (f_{k,N+1} − f_{k,N})/p_N`, "where `N ∈ ℕ` is an integer-valued random variable
independent of `(U_i, i ∈ ℤ)` such that `Pr(N = l) = p_l` for `l ≥ 0`".

`singleTermEstimator g x₀ U f b' k p N ω = (f_{k,N(ω)+1}(ω) − f_{k,N(ω)}(ω)) / p_{N(ω)}`.

**Formalization Note.** The law of `N` and its independence from the noise are hypotheses of the
theorems that use `Z_k`, not part of this definition. -/
noncomputable def singleTermEstimator {Ω F F' : Type*} (g : F → F' → F) (x₀ : F)
    (U : ℤ → Ω → F') (f : F → ℝ) (b' k : ℕ) (p : ℕ → ℝ) (N : Ω → ℕ) : Ω → ℝ :=
  fun ω => (levelEstimator g x₀ U f b' k (N ω + 1) ω - levelEstimator g x₀ U f b' k (N ω) ω) /
    p (N ω)

end UnbiasedTimeAvg


