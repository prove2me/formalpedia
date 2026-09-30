-- Prove2me | Definitions.Def_NonuniformCompetitive_Snoopy_randomized
-- name    : NonuniformCompetitive_Snoopy_randomized
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:47:37.673223+00:00
-- url     : https://prove2.me/theorems/d542e20f-3df9-4bac-a6e0-e41a76d3e6a5
-- title:
--   Randomized snoopy-caching algorithms and competitiveness against an oblivious adversary
-- statement:
--   A **randomized on-line algorithm** $A$ for the single-block snoopy-caching task system with $n$ processors and transfer cost $p$ is a probability distribution on deterministic on-line algorithms: a probability space $(\iota, \mu)$ and a deterministic on-line algorithm $A_\omega$ for each outcome $\omega \in \iota$, such that for every request sequence $\sigma$ the cost $\omega \mapsto C_{A_\omega}(\sigma)$ is measurable. Its expected cost is
--   $$\mathbf{E}C_A(\sigma) = \int_\iota C_{A_\omega}(\sigma)\, d\mu(\omega) \in [0, +\infty].$$
--
--   $A$ is **$c$-competitive against an oblivious adversary from the initial state $s_0$** if every $A_\omega$ starts in $s_0$ and there is a real constant $a$ such that for every admissible request sequence $\sigma$,
--   $$\mathbf{E}C_A(\sigma) \le c\cdot C_{opt}(s_0, \sigma) + a,$$
--   where $C_{opt}(s_0,\sigma)$ is the optimal off-line cost from $s_0$.
--
--   The request sequence is fixed before the coins are flipped, which is the oblivious adversary of §1 (p. 543). The constant $a$ may depend on the instance ($n$, $p$, $s_0$) but not on $\sigma$.
--
--   **Formalization Note** The expected cost is a lower Lebesgue integral in `ℝ≥0∞`, made a genuine expectation by the measurability field. The right-hand side is `ENNReal.ofReal (c * opt + a)` with `opt` the off-line optimum converted to a real number; on admissible sequences the off-line optimum is finite, so this conversion loses nothing. An algorithm that pays $+\infty$ with positive probability on an admissible sequence is not competitive.
-- source:
--   Karlin, Manasse, McGeoch, Owicki, Competitive Randomized Algorithms for Nonuniform Problems, Algorithmica 11 (1994), pp. 542–543, §1 (randomized algorithms, c-competitive against an oblivious adversary)

import Mathlib
import Definitions.Def_NonuniformCompetitive_Snoopy_model

namespace NonuniformCompetitive.Snoopy

open MeasureTheory
open scoped ENNReal

/-- A randomized on-line snoopy-caching algorithm for block-transfer cost `p` (Karlin et al.
1994, §1, p. 542: "a probability distribution on a set of deterministic algorithms"): a
probability measure `μ` on an index type `ι` of coin-flip outcomes, and a deterministic on-line
algorithm for each outcome. All coins are flipped up front, which is the oblivious-adversary
setting. The field `meas` makes the cost on each fixed request sequence a measurable function of
the outcome, so that the lower integral below is the expected cost. -/
structure RandomizedAlgorithm (n p : ℕ) where
  ι : Type
  [ms : MeasurableSpace ι]
  μ : Measure ι
  prob : IsProbabilityMeasure μ
  alg : ι → OnlineAlgorithm n
  meas : ∀ σ : List (Req n), Measurable fun i => (alg i).cost p σ

/-- The expected cost `E C_A(σ)` of the randomized algorithm `A` on the request sequence `σ`. -/
noncomputable def RandomizedAlgorithm.expCost {n p : ℕ} (A : RandomizedAlgorithm n p)
    (σ : List (Req n)) : ℝ≥0∞ :=
  ∫⁻ i, (A.alg i).cost p σ ∂A.μ

/-- `A` is `c`-competitive against an oblivious adversary from the initial state `s₀`
(§1, p. 543): every deterministic algorithm in its support starts in `s₀`, and there is a
constant `a` such that on every admissible request sequence `σ`,
`E C_A(σ) ≤ c · C_opt(σ) + a`, where `C_opt(σ)` is the optimal off-line cost from `s₀`
(finite on admissible sequences) read as a real number. -/
def RandomizedAlgorithm.IsCompetitiveFrom {n p : ℕ} (A : RandomizedAlgorithm n p)
    (s₀ : State n) (c : ℝ) : Prop :=
  (∀ i, (A.alg i).after [] = s₀) ∧
  ∃ a : ℝ, ∀ σ : List (Req n), Admissible σ →
    A.expCost σ ≤ ENNReal.ofReal (c * (offlineCost p s₀ σ).toReal + a)

end NonuniformCompetitive.Snoopy


