-- Prove2me | Definitions.Def_MetricMinTest_signedBernoulli
-- name    : MetricMinTest_signedBernoulli
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:04:58.056071+00:00
-- url     : https://prove2.me/theorems/c542e927-9c50-4ae4-93de-088c62049d02
-- title:
--   Signed Bernoulli law of mean $u$
-- statement:
--   The signed Bernoulli law of mean $u$ is the law of $2Y-1$ for $Y\sim\mathrm{Bernoulli}((1+u)/2)$: mass $(1+u)/2$ at $+1$ and $(1-u)/2$ at $-1$. For $u\in[-1,1]$ it is a probability measure on $[-1,1]$ with mean $u$.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), §2, p.6

import Mathlib

namespace MetricMinTest

/-- **Signed Bernoulli law of mean `u`.** Chen–Fang, *Minimum-Mean Testing under Metric
Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), §2, p.6: "the law of
2Y − 1 for Y ∼ Bernoulli((1 + u)/2)".

**Formalization Note.** The measure `((1 + u)/2) δ₁ + ((1 − u)/2) δ₋₁` on `ℝ`; it is a probability
measure with mean `u` for `u ∈ [−1, 1]`, which is how every use takes it. -/
noncomputable def signedBernoulli (u : ℝ) : MeasureTheory.Measure ℝ :=
  ENNReal.ofReal ((1 + u) / 2) • MeasureTheory.Measure.dirac 1 +
    ENNReal.ofReal ((1 - u) / 2) • MeasureTheory.Measure.dirac (-1)

end MetricMinTest


