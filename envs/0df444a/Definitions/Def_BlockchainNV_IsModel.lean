-- Prove2me | Definitions.Def_BlockchainNV_IsModel
-- name    : BlockchainNV_IsModel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:41:17.004302+00:00
-- url     : https://prove2.me/theorems/55f3e404-baec-40e4-a05e-7111da07ae81
-- title:
--   The random model: independent $X\sim N(\mu_X,\sigma_X^2)$ and $\varepsilon\sim N(0,\sigma^2)$
-- statement:
--   Given parameters $\theta$, a measure $P$ on a measurable space $\Omega$ and real random variables $X, \varepsilon$ on $\Omega$, the predicate says that
--
--   1. the freshness state $X$ has law $N(\mu_X, \sigma_X^2)$ under $P$,
--   2. the demand shock $\varepsilon$ has law $N(0, \sigma^2)$ under $P$,
--   3. $X$ and $\varepsilon$ are independent under $P$.
--
--   This is the probabilistic part of the base model of §2: "The random variables $X$ and $\varepsilon$ are independent and normally distributed." Because the laws are probability measures, $P$ is a probability measure.
--
--   **Formalization Note** Mathlib's `gaussianReal m v` is parametrized by the variance $v \ge 0$, so $N(\mu_X,\sigma_X^2)$ is `gaussianReal μX (σX^2).toNNReal`. `HasLaw` includes almost-everywhere measurability of the random variable.
-- source:
--   Keskin, Li, Song, The Blockchain Newsvendor: Value of Freshness Transparency and Smart Contracts, Management Science (2024), doi:10.1287/mnsc.2021.02949, §2, p.7 (PDF p.7)

import Mathlib
import Definitions.Def_BlockchainNV_Params

open MeasureTheory ProbabilityTheory

namespace BlockchainNV

/-- Keskin, Li, Song, *The Blockchain Newsvendor*, Management Science (2024),
doi:10.1287/mnsc.2021.02949, §2, p.7 (PDF p.7): "The random variables `X` and `ε` are independent
and normally distributed. Specifically, `X ∼ N(µ_X, σ_X²)` and `ε ∼ N(0, σ²)`." The freshness
state `X` and the demand shock `ε` are random variables on a probability space `(Ω, P)`.

**Formalization Note.** `gaussianReal m v` is parametrized by the **variance** `v : ℝ≥0`, so
`N(µ_X, σ_X²)` is `gaussianReal µ_X (σ_X²).toNNReal` (`Real.toNNReal` is the identity on the
nonnegative `σ_X²`). `HasLaw` includes a.e.-measurability of the
random variable; since a Gaussian law is a probability measure, `P` is then a probability
measure. -/
def IsModel (θ : Params) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X ε : Ω → ℝ) : Prop :=
  HasLaw X (gaussianReal θ.muX (θ.sigmaX ^ 2).toNNReal) P ∧
    HasLaw ε (gaussianReal 0 (θ.sigma ^ 2).toNNReal) P ∧
    IndepFun X ε P

end BlockchainNV


