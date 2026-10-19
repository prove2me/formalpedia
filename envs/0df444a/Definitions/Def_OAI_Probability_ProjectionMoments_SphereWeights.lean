-- Prove2me | Definitions.Def_OAI_Probability_ProjectionMoments_SphereWeights
-- name    : OAI_Probability_ProjectionMoments_SphereWeights
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T17:33:28.62646+00:00
-- url     : https://prove2.me/theorems/546a6bfa-6861-4d21-b931-07bb6fc39218
-- title:
--   Extending sphere weights to the ambient space
-- statement:
--   A weight $f$ on the unit sphere $S^{d-1}$ extends to $\mathbb R^d$ by $0$ off the sphere:
--   $$
--   \tilde f(x)=\begin{cases}f(x)&\|x\|=1,\\0&\text{otherwise}.\end{cases}
--   $$
--
--   On sphere points the extension agrees with $f$, so integrals against the ambient sphere law can be computed with $\tilde f$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/SphereWeights.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/SphereWeights.lean by skeleton subtraction
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
import Definitions.Def_OAI_Probability_ProjectionMoments_RieszPotential
import Definitions.Def_OAI_Probability_ProjectionMoments_Polar
import Definitions.Def_OAI_Probability_ProjectionMoments_BallMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_CapTests
import Definitions.Def_OAI_Probability_ProjectionMoments_CapDuality
import Definitions.Def_OAI_Probability_ProjectionMoments_WeightedCover
import Definitions.Def_OAI_Probability_ProjectionMoments_Stopping
import Definitions.Def_OAI_Probability_ProjectionMoments_BorelRules
import Definitions.Def_OAI_Probability_ProjectionMoments_Kernels
import Definitions.Def_OAI_Probability_ProjectionMoments_Realization
import Definitions.Def_OAI_Probability_ProjectionMoments_StoppingKernel
import Definitions.Def_OAI_Probability_ProjectionMoments_Seeded

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace ProjectionMoments
open NoiselessRegression
variable {d : ℕ}

def extendSphereWeight (f : UnitSphere d → ℝ≥0∞) : Vector d → ℝ≥0∞ :=
  Function.extend Subtype.val f (fun _ => 0)

@[simp] lemma extendSphereWeight_val (f : UnitSphere d → ℝ≥0∞) (s : UnitSphere d) :
    extendSphereWeight f s.val = f s :=
  Subtype.val_injective.extend_apply f (fun _ => 0) s

end ProjectionMoments
end

end

end OAI


