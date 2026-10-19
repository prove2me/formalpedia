-- Prove2me | Definitions.Def_OAI_Probability_GaussianRegression_Caps__ProjectionMoments
-- name    : OAI_Probability_GaussianRegression_Caps__ProjectionMoments
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T16:47:22.795275+00:00
-- url     : https://prove2.me/theorems/f6db0103-8983-4454-807e-b6fabbae41ae
-- title:
--   Spherical cap weights
-- statement:
--   For a point $y$ in an inner product space and a radius $\varepsilon$, the cap weight is the indicator of the closed ball of radius $\varepsilon$ around $y$:
--   $$
--   w_{y,\varepsilon}(s)=\mathbf 1\{\|s-y\|\le\varepsilon\}.
--   $$
--
--   On the unit sphere these balls are spherical caps, and the cap weights record whether an estimate lands within angular distance about $\varepsilon$ of the truth.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Caps.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianRegression/Caps.lean by skeleton subtraction
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

namespace OAI

/-!
Spherical cap mass bounds along sequential routes.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise

noncomputable section

universe u

namespace NoiselessRegression

section StreamCaps
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] [Nonempty J]

def capWeight (y : E) (ε : ℝ) : E → ℝ≥0∞ :=
  (Metric.closedBall y ε).indicator (fun _ => 1)

end StreamCaps

end NoiselessRegression

end

end OAI


