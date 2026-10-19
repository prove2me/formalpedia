-- Prove2me | Definitions.Def_OAI_Probability_CriticalZ3_ConditionalQuality
-- name    : OAI_Probability_CriticalZ3_ConditionalQuality
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T18:08:43.263983+00:00
-- url     : https://prove2.me/theorems/1b004a98-64ce-4450-99ab-28fd590b96f4
-- title:
--   Conditional probability given revealed bits
-- statement:
--   For a product Bernoulli law with parameters $p$, a finite set $J$ of revealed bits with values given by $\xi$, and an event $C$, the conditional probability is
--   $$
--   \mathbb P_p(C\mid\omega_J=\xi_J)=\mathbb P_{p'}(C),
--   $$
--   where $p'$ fixes the bits in $J$ to their revealed values and keeps $p_e$ elsewhere. It is evaluated as the probability of $C$ under that modified product law.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/ConditionalQuality.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/ConditionalQuality.lean by skeleton subtraction
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

namespace OAI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace InfiniteConditioning
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {E : Type} [Countable E]

noncomputable def conditionalProbability (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E)
    (C : Set (E → Bool)) (ξ : E → Bool) : ℝ :=
  (ProductCylinder.law (fixedParameter p J ξ)).real C

end InfiniteConditioning

end OAI


