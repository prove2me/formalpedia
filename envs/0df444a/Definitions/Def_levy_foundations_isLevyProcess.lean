-- Prove2me | Definitions.Def_levy_foundations_isLevyProcess
-- name    : levy_foundations_isLevyProcess
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T10:31:22.264992+00:00
-- url     : https://prove2.me/theorems/8945c6f4-3588-44f2-b3e1-477e7dc089b3
-- title:
--   Lévy process taking values in a topological additive group
-- statement:
--   A process on nonnegative real time with values in any measurable topological additive group is a Lévy process when it starts at zero, has independent and stationary increments, and its sample paths are càdlàg almost everywhere relative to μ. The real-valued case remains available by specialisation.
-- source:
--   Adapted from Shmuel Link, LeanLevy (MIT), frozen commit 7e73fd9b23ad52956ec2756a815889a783131ce4, https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/LevyProcess.lean#L46-L60. Uses Mathlib HasIndepIncrements, definitionally equivalent to source HasIndependentIncrements as proved in LeanLevy/Processes/StochasticProcess.lean. Pending remote compilation.

import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
import Mathlib.Probability.IdentDistrib
import Definitions.Def_levy_foundations_increment
import Definitions.Def_levy_foundations_isCadlag
open scoped NNReal

open MeasureTheory ProbabilityTheory
namespace LevyFoundations
/-- A càdlàg process with stationary and independent increments. -/
structure IsLevyProcess {Ω E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E]
    [TopologicalSpace E] [AddGroup E]
    (X : ℝ≥0 → Ω → E) (μ : Measure Ω) : Prop where
  start_zero : X 0 = fun _ => 0
  indep_increments : HasIndepIncrements X μ
  stationary_increments : ∀ s h : ℝ≥0,
    IdentDistrib (increment X s (s + h)) (increment X 0 h) μ μ
  cadlag_ae : ∀ᵐ ω ∂μ, isCadlag (fun t => X t ω)
end LevyFoundations


