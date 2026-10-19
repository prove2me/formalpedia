-- Prove2me | Definitions.Def_OAI_Probability_CriticalZ3_TrialCounts
-- name    : OAI_Probability_CriticalZ3_TrialCounts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T18:10:38.886391+00:00
-- url     : https://prove2.me/theorems/b36b7d92-a76a-4a8b-bb7f-0db78df0332c
-- title:
--   Counting successful trials
-- statement:
--   For finitely many events $A_i$ on a common space, the success count is
--   $$
--   N(\omega)=\sum_i\mathbf 1_{A_i}(\omega),
--   $$
--   the number of events that occur at $\omega$. If no good success occurs, then either fewer than half the expected number of successes occur, or at least half of that many are bad; bad successes only need a first-moment bound, without mutual independence.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/TrialCounts.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/TrialCounts.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CriticalZ3 mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison
import Definitions.Def_OAI_Probability_CriticalZ3_LatticeGraph
import Definitions.Def_OAI_Probability_CriticalZ3_BoxGeometry
import Definitions.Def_OAI_Probability_CriticalZ3_LatticePaths
import Definitions.Def_OAI_Probability_CriticalZ3_EntryLayers
import Definitions.Def_OAI_Probability_CriticalZ3_SeedTrials
import Definitions.Def_OAI_Probability_CriticalZ3_Conditioning
import Definitions.Def_OAI_Probability_CriticalZ3_ConditionalQuality

namespace OAI

universe uI uOmega

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
namespace ShellEstimates
variable {Ω : Type uOmega} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/- Bad successes only need a first moment; no mutual independence is used. -/
/- If there is no good success, either successes fall below half their mean
or at least half their mean are bad. This is purely deterministic. -/
end ShellEstimates

namespace TrialCounts
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {Ω : Type uOmega} {I : Type uI} [MeasurableSpace Ω] [Fintype I]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]

noncomputable def count (A : I → Set Ω) : Ω → ℝ :=
  fun ω => ∑ i, (A i).indicator (fun _ => (1 : ℝ)) ω

end TrialCounts

end OAI


