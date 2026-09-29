-- Prove2me | Definitions.Def_TraceEstimation_Shared_IsApproximator
-- name    : TraceEstimation_Shared_IsApproximator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:26:46.781621+00:00
-- url     : https://prove2.me/theorems/8b5ac65a-3b61-4c69-b984-83f044c2c6e1
-- title:
--   Definition 4.1 — $(\epsilon,\delta)$-approximator of $\mathrm{trace}(A)$
-- statement:
--   Let $A$ be a real $n \times n$ matrix, let $(\Omega, \mathcal{F}, P)$ be a probability space and let $T : \Omega \to \mathbb{R}$ be a randomized trace estimator. For $\epsilon, \delta \in \mathbb{R}$, the estimator $T$ is an **$(\epsilon,\delta)$-approximator** of $\mathrm{trace}(A)$ if
--
--   $$\Pr\bigl(|T - \mathrm{trace}(A)| \le \epsilon\, \mathrm{trace}(A)\bigr) \ge 1 - \delta .$$
--
--   That is, with probability at least $1-\delta$ the relative error of $T$ is at most $\epsilon$. This is the quality measure in which all sample bounds of the paper are stated: a bound on $M$ that makes the $M$-sample estimator an $(\epsilon,\delta)$-approximator.
--
--   **Formalization Note** The probability is `P.real` of the event $\{\omega : |T(\omega) - \mathrm{trace}(A)| \le \epsilon\,\mathrm{trace}(A)\}$. Definition 4.1 is stated for symmetric positive semi-definite $A$ (with $\epsilon > 0$, $\delta \in (0,1)$); the predicate itself carries no hypothesis on $A$, $\epsilon$ or $\delta$, and the theorems that use it state those they need.
--
--   **Shared definition.** This is the group's single copy of this definition, reviewed once for every chunk that uses it: `01-gaussian` (Theorem 5.2, p. 8:7); `03-rayleigh` (Theorem 6.1, p. 8:10); `04-hutchinson` (Theorem 7.1, pp. 8:10–8:11); `05-unit-vector` (Theorem 8.2, p. 8:12; Theorem 8.4, p. 8:13).
-- source:
--   Avron and Toledo, Randomized algorithms for estimating the trace of an implicit symmetric positive semi-definite matrix, J. ACM 58(2), Article 8 (2011), p. 8:5, Definition 4.1

import Mathlib

namespace TraceEstimation.Shared

open MeasureTheory

/-- Definition 4.1 (Avron–Toledo, p. 8:5): a randomized trace estimator `T`, a real random
variable on a probability space `(Ω, P)`, is an `(ε, δ)`-approximator of `trace(A)` if
`Pr(|T - trace(A)| ≤ ε · trace(A)) ≥ 1 - δ`. -/
def IsApproximator {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (T : Ω → ℝ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (ε δ : ℝ) : Prop :=
  1 - δ ≤ P.real {ω | |T ω - A.trace| ≤ ε * A.trace}

end TraceEstimation.Shared


