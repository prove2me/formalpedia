-- Prove2me | Definitions.Def_OnlineBudgetAlloc_RandAlg
-- name    : OnlineBudgetAlloc_RandAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:32:08.060808+00:00
-- url     : https://prove2.me/theorems/c4f2c216-865b-42a2-bda1-9f5cdc52ffe9
-- title:
--   Randomized online algorithm and its expected revenue $\mathbb E[\mathrm{ALG}_A(\sigma)]$
-- statement:
--   A **randomized online algorithm** for $N$ advertisers is a probability space $(\Omega, \mu)$ together with a deterministic online algorithm $A_\omega$ for every outcome $\omega \in \Omega$. Every decision is required to be measurable in $\omega$. Its **expected revenue** on an instance $\sigma$ is
--   $$
--   \mathbb E[\mathrm{ALG}_A(\sigma)] = \int_\Omega \mathrm{ALG}_{A_\omega}(\sigma)\, d\mu(\omega).
--   $$
--
--   This is the class of algorithms in Theorem 1. By Yao's principle the paper treats a randomized algorithm as a distribution over deterministic ones (§2, p.2). The definition covers every finitely supported distribution over deterministic algorithms, and every algorithm that flips coins as it goes (take $\omega$ to be its sequence of coins).
--
--   **Formalization Note** $\Omega$ is any type with any probability measure. Measurability is stated as: for each item count, budget vector, bid history and possible decision, the set of $\omega$ producing that decision is measurable. Without this requirement, the integral of a non-measurable revenue would be $0$ and Theorem 1 would hold trivially.
-- source:
--   Panigrahi, Zhang, The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e, arXiv:2610.41136 (held version, sha256 913d8f02…), §2, p.2; Theorem 1, p.2

import Mathlib
import Definitions.Def_OnlineBudgetAlloc_Instance
import Definitions.Def_OnlineBudgetAlloc_revenue
import Definitions.Def_OnlineBudgetAlloc_DetAlg
open MeasureTheory

namespace OnlineBudgetAlloc

/-- A **randomized online algorithm** with `N` advertisers: a random deterministic online
algorithm `A ω`, with `ω` drawn from a probability space `(Ω, μ)` (Panigrahi–Zhang, *The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e*, arXiv:2610.41136 (held version, sha256 913d8f02…), §2, p.2: "By Yao's
minimax principle [Yao77], this implies the same upper bound for randomized algorithms").

**Formalization Note** `Ω` is any type with any probability measure, which covers every finitely
supported distribution over deterministic algorithms and every algorithm that flips coins as it
goes (its coin sequence is `ω`). Each decision `ω ↦ (A ω).decide m B h` must be measurable,
stated as measurability of each of its level sets; without it the expected revenue below would be
a Bochner integral of a non-measurable function, which is `0`. -/
structure RandAlg (N : ℕ) where
  /-- The sample space of the algorithm's randomness. -/
  Ω : Type
  [mΩ : MeasurableSpace Ω]
  /-- The law of the randomness. -/
  μ : Measure Ω
  [isProb : IsProbabilityMeasure μ]
  /-- The deterministic online algorithm run on the outcome `ω`. -/
  A : Ω → DetAlg N
  /-- Every decision is a measurable function of `ω`. -/
  measurable_decide : ∀ (m : ℕ) (B : Fin N → ℝ) (h : List (Fin N → ℝ)) (o : Option (Fin N)),
    MeasurableSet {ω | (A ω).decide m B h = o}

attribute [instance] RandAlg.mΩ RandAlg.isProb

/-- `E[ALG_A(σ)]`: the expected revenue of the randomized online algorithm `R` on the instance
`σ` (Panigrahi–Zhang, *The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e*, arXiv:2610.41136 (held version, sha256 913d8f02…), Theorem 1, p.2). -/
noncomputable def RandAlg.expAlg {N m : ℕ} (R : RandAlg N) (σ : Instance N m) : ℝ :=
  ∫ ω, (R.A ω).alg σ ∂(R.μ)

end OnlineBudgetAlloc


