-- Prove2me | Definitions.Def_OAI_Probability_ProjectionMoments_RieszPotential
-- name    : OAI_Probability_ProjectionMoments_RieszPotential
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T17:01:44.071586+00:00
-- url     : https://prove2.me/theorems/fbc43805-0eab-4e0a-afe0-487fbd2b0cde
-- title:
--   Measurability of Riesz kernels
-- statement:
--   For an exponent $\alpha$ and a point $z$ in a finite-dimensional inner product space, the Riesz kernel is the extended nonnegative function
--   $$
--   k_{\alpha,z}(s)=\|s-z\|^{-\alpha},
--   $$
--   which is measurable in $s$. The Riesz potential of a density $h$ on the sphere is $\sup_z\int h(s)\,k_{\alpha,z}(s)\,d\sigma(s)$, the worst-case potential over all centres.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/RieszPotential.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/RieszPotential.lean by skeleton subtraction
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
import Definitions.Def_OAI_Probability_ProjectionMoments_FrameMoments

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[fun_prop] lemma measurable_rieszKernel [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (α : ℝ) (z : E) : Measurable (rieszKernel α z) := by
  unfold rieszKernel
  fun_prop

end ProjectionMoments

end

end OAI


