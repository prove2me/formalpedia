-- Prove2me | Definitions.Def_UnbiasedTimeAvg_A1Sequence
-- name    : UnbiasedTimeAvg_A1Sequence
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:18:37.921147+00:00
-- url     : https://prove2.me/theorems/d9cf51ec-a292-46b6-a984-1eadebc427f9
-- title:
--   The rate sequence $\nu$ of Assumption A1
-- statement:
--   A sequence $(\nu(i))_{i\ge0}$ of reals is an **A1 rate sequence** if
--
--   1. $\nu(i)>0$ for all $i$,
--   2. $\nu$ is non-increasing, and
--   3. $$\sum_{i=0}^\infty\sqrt{\frac{\nu(i)}{i+1}}<\infty.\qquad(2.4)$$
--
--   These are the conditions that Assumption A1 places on $\nu$ itself; Proposition C.1, Lemma F.1 and (3.8) depend on $\nu$ only through them.
--
--   **Formalization Note** The paper says "positive decreasing"; this is read as positive and non-increasing (`Antitone`), the weaker requirement.
-- source:
--   N. Kahalé, Unbiased time-average estimators for Markov chains, arXiv:2209.09581v1 (20 Sep 2022), Assumption 1 (A1) and (2.4), p.4

import Mathlib

namespace UnbiasedTimeAvg

/-- **The rate sequence of Assumption A1.** Kahalé, arXiv:2209.09581v1, Assumption 1 (A1), p.4:
"There is a positive decreasing sequence `(ν(i), i ≥ 0)` such that
`Σ_{i=0}^∞ √(ν(i)/(i + 1)) < ∞` (2.4)".

`A1Sequence ν` says that `ν(i) > 0` for all `i`, that `ν` is non-increasing, and that the series
(2.4) converges.

**Formalization Note.** "Decreasing" is read as non-increasing (`Antitone`): the weaker
requirement, so every theorem assuming it covers the strict reading too. Convergence of the series
of nonnegative terms (2.4) is `Summable`. -/
structure A1Sequence (ν : ℕ → ℝ) : Prop where
  pos : ∀ i, 0 < ν i
  antitone : Antitone ν
  summable_sqrt : Summable (fun i : ℕ => Real.sqrt (ν i / ((i : ℝ) + 1)))

end UnbiasedTimeAvg


