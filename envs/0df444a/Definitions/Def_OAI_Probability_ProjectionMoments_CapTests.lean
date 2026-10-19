-- Prove2me | Definitions.Def_OAI_Probability_ProjectionMoments_CapTests
-- name    : OAI_Probability_ProjectionMoments_CapTests
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T17:09:36.067568+00:00
-- url     : https://prove2.me/theorems/87f42e66-3deb-4ab1-809d-1f6942ce2537
-- title:
--   Cap test measures
-- statement:
--   For a weight $h\ge0$ on a finite-dimensional inner product space $E$, a centre $c$ and a radius $r$, the cap test measure is obtained from the normalized surface measure of the spherical cap $\bar B(c,r)\cap S$ by weighting with $h$ and rescaling to unit size:
--   $$
--   \bigl(x\mapsto r^{-1}(x-c)\bigr)_*\bigl(h\cdot\sigma_{c,r}\bigr),
--   $$
--   where $\sigma_{c,r}$ is the sphere measure restricted to $\bar B(c,r)$ and normalized to mass one.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/CapTests.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/CapTests.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def capTestMeasure (h : E → ℝ≥0∞) (c : E) (r : ℝ) : Measure E :=
  ((capMeasure c r).withDensity h).map (rescale c r)

end ProjectionMoments

end

end OAI


