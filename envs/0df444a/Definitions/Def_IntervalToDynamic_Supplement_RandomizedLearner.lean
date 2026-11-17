-- Prove2me | Definitions.Def_IntervalToDynamic_Supplement_RandomizedLearner
-- name    : IntervalToDynamic_Supplement_RandomizedLearner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T01:37:37.375796+00:00
-- url     : https://prove2.me/theorems/db17dae5-36f1-4527-a6cd-3b1fdb3f3352
-- title:
--   Randomized nonanticipating learner and expected dynamic regret
-- statement:
--   A **randomized online learner** draws a private seed once and, at round $t$, maps that seed together with exactly the losses from rounds $1,\ldots,t-1$ to a decision in $[-1,1]$. For each fixed history the decision is measurable in the seed.
--
--   Given an independent random hard construction with law $\nu$ and learner seed law $\mu$, expected dynamic regret is the integral of the pointwise dynamic regret under the product law $\nu\otimes\mu$. Thus the expectation includes both the random losses and comparators and the learner's internal randomness.
--
--   **Formalization Note** The theorem separately requires integrability of each constructed real-valued regret, preventing the Bochner integral's nonintegrable default value from trivializing a lower bound.
-- source:
--   Wang–Zhao–Zhou, On the Relation Between Interval Regret and Dynamic Regret, arXiv:2609.34423, Theorem 8, p.12 (PDF p.14); proof, pp.39–41 (PDF pp.41–43)

import Mathlib
import Definitions.Def_ModernOnlineLearning_Dynamic_Defs

open MeasureTheory
open ModernOnlineLearning.Dynamic (dynamicRegret)

namespace IntervalToDynamic.Supplement

/-- A possibly randomized, nonanticipating online learner on `[-1,1]`. A seed is drawn once;
at round `t`, `act` receives exactly the losses of rounds `1,...,t-1`. -/
structure RandomizedLearner (Ω : Type*) [MeasurableSpace Ω] where
  act : Ω → List (ℝ → ℝ) → ℝ
  feasible : ∀ ω hist, act ω hist ∈ Set.Icc (-1 : ℝ) 1
  measurable_seed : ∀ hist, Measurable (fun ω => act ω hist)

/-- Decisions produced from a fixed seed and a realized loss sequence. Round zero is unused. -/
def randomizedDecisions {Ω : Type*} [MeasurableSpace Ω] (L : RandomizedLearner Ω)
    (ω : Ω) (f : ℕ → ℝ → ℝ) (t : ℕ) : ℝ :=
  L.act ω ((List.range' 1 (t - 1)).map f)

/-- Expected dynamic regret when the hard construction has law `ν` and the learner's private
seed has law `μ`. The two sources of randomness are independent, hence `ν.prod μ`. -/
noncomputable def expectedDynamicRegret {Ξ Ω : Type*} [MeasurableSpace Ξ] [MeasurableSpace Ω]
    (ν : Measure Ξ) (μ : Measure Ω) (L : RandomizedLearner Ω)
    (f : Ξ → ℕ → ℝ → ℝ) (u : Ξ → ℕ → ℝ) (T : ℕ) : ℝ :=
  ∫ q : Ξ × Ω, dynamicRegret (f q.1) (randomizedDecisions L q.2 (f q.1)) (u q.1) T
    ∂(ν.prod μ)

end IntervalToDynamic.Supplement


