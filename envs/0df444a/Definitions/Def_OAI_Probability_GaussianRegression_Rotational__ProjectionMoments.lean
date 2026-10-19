-- Prove2me | Definitions.Def_OAI_Probability_GaussianRegression_Rotational__ProjectionMoments
-- name    : OAI_Probability_GaussianRegression_Rotational__ProjectionMoments
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T16:51:39.262208+00:00
-- url     : https://prove2.me/theorems/ba20c717-ab97-4aa7-a79e-531edfc8f555
-- title:
--   Probability laws for samples and the uniform sphere
-- statement:
--   The basic laws of the streaming regression model are probability measures: the sample law, which makes $T$ independent standard Gaussian vectors in $\mathbb R^d$, and the uniform law on the unit sphere $S^{d-1}$ (for $d\ge1$):
--   $$
--   \mathrm{samples}(\mathbb R^{d\times T})=1,\qquad \mathrm{unif}(S^{d-1})=1 .
--   $$
--
--   These facts underlie the Fubini and rotational-symmetry arguments.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Rotational.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianRegression/Rotational.lean by skeleton subtraction
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

namespace OAI

/-!
Fubini bounds and rotational lower bounds for sequential estimation.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise

noncomputable section

universe u

namespace NoiselessRegression

section FubiniAux
variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
end FubiniAux

instance sampleLaw_probability (d T : ℕ) : IsProbabilityMeasure (sampleLaw d T) := by
  unfold sampleLaw
  infer_instance
instance uniformSphere_probability (d : ℕ) [NeZero d] : IsProbabilityMeasure (uniformSphere d) := by
  change IsProbabilityMeasure (sphereLaw (E := Vector d))
  infer_instance

namespace Learner
end Learner

end NoiselessRegression

end

end OAI


