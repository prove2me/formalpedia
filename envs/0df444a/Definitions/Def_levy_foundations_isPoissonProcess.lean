-- Prove2me | Definitions.Def_levy_foundations_isPoissonProcess
-- name    : levy_foundations_isPoissonProcess
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T21:36:13.367885+00:00
-- url     : https://prove2.me/theorems/df607bb3-6f43-494c-a196-8a39e31fbd77
-- title:
--   Poisson counting process with integer-valued independent differences
-- statement:
--   A counting process starts at zero, has integer-embedded independent increments and Poisson increment laws.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/PoissonProcess.lean#L52

import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
import Mathlib.Probability.Distributions.Poisson.Basic
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace LevyFoundations
/-- A Poisson counting process, with independent differences in its integer embedding. -/
structure IsPoissonProcess {Ω : Type*} [MeasurableSpace Ω]
    (N : ℝ≥0 → Ω → ℕ) (rate : ℝ≥0) (μ : Measure Ω) : Prop where
  start_zero : N 0 = fun _ => 0
  indep_increments : HasIndepIncrements (fun t ω => (N t ω : ℤ)) μ
  increment_poisson : ∀ (s h : ℝ≥0),
    μ.map (fun ω => N (s + h) ω - N s ω) = poissonMeasure (rate * h)
end LevyFoundations


