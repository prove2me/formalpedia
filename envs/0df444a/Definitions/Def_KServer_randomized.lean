-- Prove2me | Definitions.Def_KServer_randomized
-- name    : KServer_randomized
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-31T13:44:47.731189+00:00
-- url     : https://prove2.me/theorems/c8d13dfc-613a-480f-90bd-b88e6ece169e
-- title:
--   Randomized online k-server algorithms (mixed strategies)
-- statement:
--   A **randomized online $k$-server algorithm** is a mixed strategy: a probability measure $\mu$ on a type of coin-flip outcomes together with a deterministic online algorithm for each outcome, all coins flipped up front — the standard presentation against **oblivious adversaries** — with the cost on each fixed request sequence measurable in the outcome. Its **expected cost** on $\sigma$ is the lower Lebesgue integral $\int^- \mathrm{cost}(A_i, \sigma)\, d\mu(i)$ valued in $[0,\infty]$. The algorithm is **$c$-competitive from $C_0$** if every outcome's algorithm starts at $C_0$ and there is a constant $a$ with $\mathbb{E}[\mathrm{cost}(\sigma)] \le c \cdot \mathrm{OPT}(C_0, \sigma) + a$ for every request sequence $\sigma$.
-- source:
--   A. Borodin, R. El-Yaniv, Online Computation and Competitive Analysis, Cambridge University Press, 1998 (mixed strategies, oblivious adversaries); S. Bubeck, C. Coester, Y. Rabani, The randomized k-server conjecture is false!, STOC 2023, https://arxiv.org/abs/2211.05753, Definition 1

import Mathlib
import Definitions.Def_KServer_model

namespace KServer

open MeasureTheory

/-- A **randomized online `k`-server algorithm** on the metric space `M`, as a
mixed strategy: a probability measure `μ` on an index type `ι` of coin-flip
outcomes together with, for each outcome, a deterministic online algorithm.
The whole random choice is made up front (equivalently, all coins are flipped
before the first request), which is the standard mixed-strategy presentation
of randomized online algorithms against oblivious adversaries. The field
`meas` requires the cost of the drawn algorithm on each fixed request
sequence to be a measurable function of the outcome. -/
structure RandomizedAlgorithm (k : ℕ) (M : Type*) [MetricSpace M] where
  ι : Type
  [ms : MeasurableSpace ι]
  μ : Measure ι
  prob : IsProbabilityMeasure μ
  alg : ι → OnlineAlgorithm k M
  meas : ∀ σ : List M, Measurable fun i => (alg i).cost σ

/-- The **expected cost** of the randomized algorithm `A` on the request
sequence `σ`: the lower Lebesgue integral, over the coin-flip outcomes, of the
(nonnegative) cost of the drawn deterministic algorithm. -/
noncomputable def RandomizedAlgorithm.expCost {k : ℕ} {M : Type*} [MetricSpace M]
    (A : RandomizedAlgorithm k M) (σ : List M) : ENNReal :=
  ∫⁻ i, ENNReal.ofReal ((A.alg i).cost σ) ∂A.μ

/-- The randomized algorithm `A` is **`c`-competitive from `C₀`** (against
oblivious adversaries): every deterministic algorithm in its support starts in
the configuration `C₀`, and there is a constant `a` (independent of the
request sequence) such that on every request sequence the expected cost of `A`
is at most `c` times the optimal offline cost from `C₀`, plus `a`. -/
def RandomizedAlgorithm.IsCompetitiveFrom {k : ℕ} {M : Type*} [MetricSpace M]
    (A : RandomizedAlgorithm k M) (C₀ : Config k M) (c : ℝ) : Prop :=
  (∀ i, (A.alg i).conf [] = C₀) ∧
  ∃ a : ℝ, ∀ σ : List M,
    A.expCost σ ≤ ENNReal.ofReal (c * offlineCost C₀ σ + a)

end KServer


