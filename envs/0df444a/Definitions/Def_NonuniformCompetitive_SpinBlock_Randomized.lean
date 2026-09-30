-- Prove2me | Definitions.Def_NonuniformCompetitive_SpinBlock_Randomized
-- name    : NonuniformCompetitive_SpinBlock_Randomized
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:51:12.952432+00:00
-- url     : https://prove2.me/theorems/4f23dc2a-4380-466b-a481-5eeef4d34ae8
-- title:
--   Randomized spin-block algorithms and competitiveness against an oblivious adversary
-- statement:
--   A **randomized on-line algorithm** for the spin-block problem with context-switch cost $C$ is, as in §1 of Karlin, Manasse, McGeoch and Owicki, a probability distribution on deterministic on-line algorithms: a probability space $(I,\mu)$ of coin-flip outcomes and, for every outcome $i\in I$, a deterministic on-line algorithm $A_i$. For every input sequence $\sigma$ of lock waits, the cost $i\mapsto C_{A_i}(\sigma)$ is required to be measurable, and the **expected cost** is
--   $$\mathbf{E}C_A(\sigma)=\int_I C_{A_i}(\sigma)\,d\mu(i).$$
--
--   The algorithm is **$c$-competitive against an oblivious adversary** if there is a constant $a\in\mathbb R$ such that for every fixed input sequence $\sigma$,
--   $$\mathbf{E}C_A(\sigma)\le c\cdot C_{opt}(\sigma)+a .$$
--   The adversary is oblivious because $\sigma$ is fixed before the algorithm's coins are drawn.
--
--   These are the notions in which Theorem 10 (optimality of the factor $e/(e-1)$) is stated.
--
--   **Formalization Note** The expected cost is the lower Lebesgue integral of a nonnegative extended-real cost; the measurability field makes it the genuine expectation. The right-hand side $c\cdot C_{opt}(\sigma)+a$ is a real number converted to $[0,\infty]$, so a negative value means the bound requires expected cost $0$. A deterministic algorithm is the special case of a point mass.
-- source:
--   Karlin, Manasse, McGeoch, Owicki, Competitive Randomized Algorithms for Nonuniform Problems, Algorithmica 11 (1994), pp. 542–543, §1 (randomized algorithms, c-competitive against an oblivious adversary)

import Mathlib
import Definitions.Def_NonuniformCompetitive_SpinBlock_Model

open scoped NNReal ENNReal
open MeasureTheory

namespace NonuniformCompetitive.SpinBlock

/-- A **randomized on-line algorithm** for the spin-block problem with context-switch cost `C`,
as a mixed strategy (§1, p. 542: "a probability distribution on a set of deterministic
algorithms"): a probability measure `μ` on an index type `ι` of coin-flip outcomes and, for each
outcome, a deterministic on-line algorithm. The field `meas` requires the cost of the drawn
algorithm on each fixed input sequence to be a measurable function of the outcome, so that the
expected cost below is a genuine expectation. -/
structure RandomizedAlg (C : ℝ) where
  ι : Type
  [ms : MeasurableSpace ι]
  μ : Measure ι
  prob : IsProbabilityMeasure μ
  alg : ι → OnlineAlg
  meas : ∀ σ : List ℝ≥0, Measurable fun i => (alg i).cost C σ

attribute [instance] RandomizedAlg.ms

/-- The **expected cost** `E C_A(σ)` of the randomized algorithm `A` on the input `σ`. -/
noncomputable def RandomizedAlg.expCost {C : ℝ} (A : RandomizedAlg C) (σ : List ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ i, (A.alg i).cost C σ ∂A.μ

/-- The randomized algorithm `A` is **`c`-competitive against an oblivious adversary** (§1,
p. 543): there is a constant `a` such that for every fixed input sequence `σ` of lock waits,
`E C_A(σ) ≤ c · C_opt(σ) + a`. -/
def RandomizedAlg.IsCompetitive {C : ℝ} (A : RandomizedAlg C) (c : ℝ) : Prop :=
  ∃ a : ℝ, ∀ σ : List ℝ≥0, A.expCost σ ≤ ENNReal.ofReal (c * optCost C σ + a)

end NonuniformCompetitive.SpinBlock


