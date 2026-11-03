-- Prove2me | Definitions.Def_levy_foundations_isCompoundPoissonDriver
-- name    : levy_foundations_isCompoundPoissonDriver
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T21:39:48.572358+00:00
-- url     : https://prove2.me/theorems/b87aefb0-b302-4837-a9a2-97d06a411dea
-- title:
--   Jointly independent exponential interarrivals and random marks
-- statement:
--   Jointly independent exponential interarrivals and random marks.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/CompoundPoisson.lean#L88

import Mathlib.Probability.HasLawExists
import Mathlib.Probability.Distributions.Exponential
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace LevyFoundations
/-- A joint i.i.d. interarrival-mark driver for a compound Poisson process. -/
structure IsCompoundPoissonDriver {Ω : Type*} [MeasurableSpace Ω]
    (τ Y : ℕ → Ω → ℝ) (r : ℝ≥0) (ν' : Measure ℝ)
    (μ : Measure Ω) : Prop where
  measurable_interarrival : ∀ n, Measurable (τ n)
  measurable_mark : ∀ n, Measurable (Y n)
  indep : iIndepFun (Sum.elim τ Y) μ
  law_interarrival : ∀ n, HasLaw (τ n) (expMeasure r) μ
  law_mark : ∀ n, HasLaw (Y n) ν' μ
end LevyFoundations


