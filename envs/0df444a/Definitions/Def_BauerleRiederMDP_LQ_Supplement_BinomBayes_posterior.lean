-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_BinomBayes_posterior
-- name    : BauerleRiederMDP_LQ_Supplement_BinomBayes_posterior
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:03:24.926952+00:00
-- url     : https://prove2.me/theorems/1279885a-3337-4915-b6bd-59e9fb64ea69
-- title:
--   The posterior $\hat{\mu}(\cdot |m, n)$ of the binomial model
-- statement:
--   **The posterior $\hat{\mu}(\cdot |m, n)$ of the binomial model** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §6.1, p.179, PDF 192, with Example 5.4.4): after $n$ periods with $m$ up-movements, $\hat{\mu}(C | m, n) = \int _C \theta ^m (1 - \theta )^{n-m} Q_0(d\theta ) / \int _\Theta  \theta '^m (1 - \theta ')^{n-m} Q_0(d\theta ')$; $D_{Q_0} := {\hat{\mu}(\cdot |m, n) | n \in  \mathbb N _0, m \le  n}$ is the set of all possible posteriors.
--
--   **Formalization Note.** Normalized in $\mathbb R \ge 0\infty $; for $m \le  n$ and $Q_0$ carried by $(0, 1)$ the normalizing constant is in $(0, 1]$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §6.1, p.179, PDF 192, with Example 5.4.4

import Mathlib
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BinomBayes

open MeasureTheory

namespace BauerleRiederMDP.LQ.Supplement

/-- **The posterior `μ̂(·|m, n)` of the binomial model** (Bäuerle & Rieder, *Markov Decision
Processes with Applications to Finance* (2011), §6.1, p.179, PDF 192, with Example 5.4.4): after `n`
periods with `m` up-movements,
`μ̂(C | m, n) = ∫_C θ^m (1 − θ)^{n−m} Q_0(dθ) / ∫_Θ θ′^m (1 − θ′)^{n−m} Q_0(dθ′)`;
`D_{Q_0} := {μ̂(·|m, n) | n ∈ ℕ_0, m ≤ n}` is the set of all possible posteriors.

**Formalization Note.** Normalized in `ℝ≥0∞`; for `m ≤ n` and `Q_0` carried by `(0, 1)` the
normalizing constant is in `(0, 1]`. -/
noncomputable def BinomBayes.posterior (B : BinomBayes) (m n : ℕ) : Measure ℝ :=
  (∫⁻ θ, ENNReal.ofReal (θ ^ m * (1 - θ) ^ (n - m)) ∂B.Q0)⁻¹ •
    B.Q0.withDensity fun θ => ENNReal.ofReal (θ ^ m * (1 - θ) ^ (n - m))

end BauerleRiederMDP.LQ.Supplement


