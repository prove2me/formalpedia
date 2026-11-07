-- Prove2me | Definitions.Def_RGMISFast_rankLaw
-- name    : RGMISFast_rankLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:27:00.100417+00:00
-- url     : https://prove2.me/theorems/2724f973-7cf8-4314-9197-ae048b0da2fe
-- title:
--   The i.i.d. Exp(1) rank law on $\mathbb R^V$
-- statement:
--   The ranks $(r(v))_{v\in V}$ are independent with the exponential distribution of parameter $1$:
--   $$
--   \Pr[r(v)>s]=e^{-s}\qquad(s\ge0,\ v\in V).
--   $$
--   This module defines their joint law, the product over $V$ of Exp(1) laws, a probability measure on $\mathbb R^V$.
--
--   Every probability and expectation of the goal theorem is taken under this law.
--
--   **Formalization Note** The factor is Mathlib's `expMeasure 1`, the law with density $e^{-x}$ on $[0,\infty)$. Distinctness and nonnegativity of the ranks hold almost surely and are not imposed.
-- source:
--   Dalirrooyfard, Makarychev, Mitrović, Ramachandran, Randomized Greedy MIS Is Fast at Every Node, STOC 2027 submission (manuscript sha256 e93cdfecc03618969d5f2ecf8171c6f84c528edcc473b2f864299e555f823664), p.3 (PDF p.5) and §2, p.10 (PDF p.12)

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace RGMISFast

/-- The rank law (Dalirrooyfard, Makarychev, Mitrović, Ramachandran, *Randomized Greedy MIS Is
Fast at Every Node*, STOC 2027 submission (manuscript sha256 e93cdfec…), p.3 and §2, p.10): "the
ranks of all vertices are sampled i.i.d. from the exponential distribution with parameter 1",
`Pr[r(v) > s] = e^{−s}`. It is the product over the vertices of `expMeasure 1`, a probability
measure on `V → ℝ`.

**Formalization Note** `ProbabilityTheory.expMeasure 1` is Mathlib's Exp(1) law
(`gammaMeasure 1 1`, density `e^{−x}` on `[0, ∞)`). Ranks are not restricted to be distinct or
nonnegative: both hold almost surely. -/
noncomputable def rankLaw (V : Type*) [Fintype V] : Measure (V → ℝ) :=
  Measure.pi (fun _ : V => expMeasure 1)

end RGMISFast


