-- Prove2me | Definitions.Def_OAI_Probability_ProjectionMoments_FrameMoments
-- name    : OAI_Probability_ProjectionMoments_FrameMoments
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T16:58:37.217363+00:00
-- url     : https://prove2.me/theorems/7de1d781-704d-4ec7-ad45-46bce2b5d495
-- title:
--   Densities of the zero measure
-- statement:
--   The lower density and the coordinate density of the zero measure vanish identically:
--   $$
--   \underline{f}_0(A,y)=0,\qquad f_0(A,y)=0 .
--   $$
--
--   These are the trivial base cases for the moment estimates of projected densities, where the measure may be cut into pieces some of which are zero.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/FrameMoments.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/FrameMoments.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ProjectionMoments mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Gram__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Smoothing__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Projection__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Support__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Blocks__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Sphere__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Stream__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Caps__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Execution__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Rotational__ProjectionMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_Graph
import Definitions.Def_OAI_Probability_ProjectionMoments_Frames
import Definitions.Def_OAI_Probability_ProjectionMoments_SphereDensity

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments

section
attribute [fun_prop] measurable_ballAverage
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] lemma lowerDensity_zero [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (m : ℕ) (x : (Fin m → E) × Label m) :
    lowerDensity (0 : Measure E) m x = 0 := by
  simp [lowerDensity, ballAverage, vectorSmoothing]

@[simp] lemma coordinateDensity_zero (m : ℕ) (x : (Fin m → E) × (Fin m → ℝ)) :
    coordinateDensity (0 : Measure E) m x = 0 := lowerDensity_zero m _

end ProjectionMoments

end

end OAI


