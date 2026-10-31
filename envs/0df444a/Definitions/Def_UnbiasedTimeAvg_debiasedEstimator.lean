-- Prove2me | Definitions.Def_UnbiasedTimeAvg_debiasedEstimator
-- name    : UnbiasedTimeAvg_debiasedEstimator
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:21:29.444522+00:00
-- url     : https://prove2.me/theorems/1950d393-af82-46d2-b812-3b05b6993792
-- title:
--   The unbiased time-average estimator $\hat f_k=f_{k,0}+q^{-1}QZ'_k$
-- statement:
--   Given $q\in(0,1]$, a copy $Z'_k$ of $Z_k$ independent of $f_{k,0}$, and a binary variable $Q$ independent of $(f_{k,0},Z'_k)$ with $\Pr(Q=1)=q$, the paper sets
--   $$\hat f_k:=f_{k,0}+q^{-1}QZ'_k.\qquad(3.5)$$
--   $\hat f_k$ samples $f_{k,0}$ once and the correction $Z'_k$ with frequency $q$.
--
--   **Formalization Note** $Q$ and $Z'$ are arbitrary real random variables in the definition; their joint law (copy, independence, $\Pr(Q=1)=q$) is assumed in the goal theorem.
-- source:
--   N. Kahalé, Unbiased time-average estimators for Markov chains, arXiv:2209.09581v1 (20 Sep 2022), (3.5), p.9

import Mathlib
import Definitions.Def_UnbiasedTimeAvg_levelEstimator

namespace UnbiasedTimeAvg

/-- **The unbiased time-average estimator `f̂_k`.** Kahalé, arXiv:2209.09581v1, (3.5), p.9: "Given
`q ∈ (0, 1]`, let `Z′_k` be a copy of `Z_k` independent of `f_{k,0}` and let `Q` be a binary
variable independent of `(f_{k,0}, Z′_k)` such that `Pr(Q = 1) = q`. Set
`f̂_k := f_{k,0} + q⁻¹QZ′_k`."

`debiasedEstimator g x₀ U f b' k q Q Z' ω = f_{k,0}(ω) + q⁻¹ Q(ω) Z′(ω)`.

**Formalization Note.** `Q` and `Z′` are arbitrary real random variables here; that `Z′` is a copy
of `Z_k` independent of `f_{k,0}`, that `Q ∈ {0, 1}` with `Pr(Q = 1) = q`, and the independence of
`Q` from the pair, are hypotheses of the theorem using `f̂_k`. -/
noncomputable def debiasedEstimator {Ω F F' : Type*} (g : F → F' → F) (x₀ : F)
    (U : ℤ → Ω → F') (f : F → ℝ) (b' k : ℕ) (q : ℝ) (Q Z' : Ω → ℝ) : Ω → ℝ :=
  fun ω => levelEstimator g x₀ U f b' k 0 ω + q⁻¹ * Q ω * Z' ω

end UnbiasedTimeAvg


