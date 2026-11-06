-- Prove2me | Definitions.Def_MetricMinTest_oneStreamStat
-- name    : MetricMinTest_oneStreamStat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:00.30241+00:00
-- url     : https://prove2.me/theorems/d7500157-b93c-452a-86a3-46c8bc22a358
-- title:
--   One-stream statistic $S_n$
-- statement:
--   For observations $X_1,X_2,\dots$, a threshold $a$ and a gap $\eta$,
--   $$S_n=\eta\sum_{t=1}^n(X_t-a)-n\eta^2/2.$$
--
--   **Formalization Note** Observations are indexed from $0$, so the sum runs over the first $n$ of them.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), §A.1, p.21

import Mathlib

namespace MetricMinTest

/-- **One-stream statistic `S_n`** (Appendix A.1). Chen–Fang, *Minimum-Mean Testing under Metric
Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), §A.1, p.21: for a threshold
`a`, a gap `η` and observations `X₁, X₂, …`, `S_n = η ∑_{t=1}^n (X_t − a) − n η²/2`.

**Formalization Note.** Observations are indexed from `0`: `S_n = η ∑_{t<n} (X t − a) − n η²/2`,
the paper's sum over its `X₁, …, X_n`. -/
noncomputable def oneStreamStat (η a : ℝ) (X : ℕ → ℝ) (n : ℕ) : ℝ :=
  η * ∑ t ∈ Finset.range n, (X t - a) - n * η ^ 2 / 2

end MetricMinTest


