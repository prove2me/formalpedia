-- Prove2me | Definitions.Def_OAI_Probability_ProjectionMoments_WeightedCover
-- name    : OAI_Probability_ProjectionMoments_WeightedCover
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T17:15:20.324476+00:00
-- url     : https://prove2.me/theorems/d20d0bf3-4ffa-4ad7-9873-d8f74bf41479
-- title:
--   Weighted coefficient budgets
-- statement:
--   For weights $b_i$ indexed by a set $I$ and a bound $K$, the budget set consists of the nonnegative coefficient families whose weighted finite sums stay below $K$:
--   $$
--   \Bigl\{a:\ a_i\ge0,\ \sum_{i\in s}a_ib_i\le K\ \text{for every finite }s\subseteq I\Bigr\}.
--   $$
--
--   It is the set of admissible coefficients for dominating a measure by a combination of smaller cap measures.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/WeightedCover.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/WeightedCover.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open scoped Topology BigOperators Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace ProjectionMoments
namespace Weighted

section
variable {ι : Type*}

def budget (b : ι → ℝ) (K : ℝ) : Set (ι → ℝ) :=
  {a | (∀ i, 0 ≤ a i) ∧ ∀ s : Finset ι, ∑ i ∈ s, a i*b i ≤ K}

end

variable {Ω ι : Type*} [MeasurableSpace Ω]

end Weighted
end ProjectionMoments

end

end OAI


