-- Prove2me | Definitions.Def_UnbiasedTimeAvg_AssumptionA1
-- name    : UnbiasedTimeAvg_AssumptionA1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:20:41.312811+00:00
-- url     : https://prove2.me/theorems/54076d82-7a7e-46ef-8b38-4442a537f77a
-- title:
--   Assumption A1 (the coupling assumption)
-- statement:
--   Assumption A1 holds with rate $\nu$ if $\nu$ is a positive non-increasing sequence satisfying (2.4) and, for all $i,m\ge0$,
--   $$\mathbb E\Big[\big(f(X_{i,m})-f(X_i)\big)^2\Big]\le\nu(i).\qquad(2.5)$$
--   In words: restarting the chain $m$ steps earlier, with the same last $i$ noise variables, moves $f(X_i)$ by at most $\sqrt{\nu(i)}$ in $L^2$, uniformly in $m$.
--
--   This is the only assumption on the chain besides the standing model; all bias and variance bounds of the paper are expressed through $\nu$.
--
--   **Formalization Note** (2.5) is stated with the lower Lebesgue integral of the nonnegative square, compared with $\nu(i)$ in $[0,\infty]$, so it means the paper's expectation even before integrability is known.
-- source:
--   N. Kahalé, Unbiased time-average estimators for Markov chains, arXiv:2209.09581v1 (20 Sep 2022), Assumption 1 (A1), (2.4)–(2.5), p.4

import Mathlib
import Definitions.Def_UnbiasedTimeAvg_coupledChain
import Definitions.Def_UnbiasedTimeAvg_A1Sequence

open MeasureTheory

namespace UnbiasedTimeAvg

/-- **Assumption A1 (the coupling assumption).** Kahalé, arXiv:2209.09581v1, Assumption 1 (A1),
p.4: "There is a positive decreasing sequence `(ν(i), i ≥ 0)` such that (2.4) holds and, for
`i, m ≥ 0`, `E((f(X_{i,m}) − f(X_i))²) ≤ ν(i)` (2.5)."

`AssumptionA1 P U g f x₀ ν` says that `ν` is a positive non-increasing sequence satisfying (2.4)
(`A1Sequence ν`) and that, for all `i, m ≥ 0`, the chain started `m` steps earlier is within
`ν(i)` of `X_i` in mean square at time `i`.

**Formalization Note.** (2.5) is written with the lower Lebesgue integral of the nonnegative
function `(f(X_{i,m}) − f(X_i))²`, compared with `ν(i)` in `[0, ∞]`; it is the paper's
expectation whether or not the square is integrable. -/
structure AssumptionA1 {Ω F F' : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (U : ℤ → Ω → F') (g : F → F' → F) (f : F → ℝ) (x₀ : F) (ν : ℕ → ℝ) : Prop where
  seq : A1Sequence ν
  coupling : ∀ i m : ℕ,
    ∫⁻ ω, ENNReal.ofReal ((f (coupledChain g x₀ U i m ω) - f (coupledChain g x₀ U i 0 ω)) ^ 2) ∂P
      ≤ ENNReal.ofReal (ν i)

end UnbiasedTimeAvg


