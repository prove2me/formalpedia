-- Prove2me | Definitions.Def_OAI_Probability_ProjectionMoments_BallMoments
-- name    : OAI_Probability_ProjectionMoments_BallMoments
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T17:07:42.96654+00:00
-- url     : https://prove2.me/theorems/a56f5977-93a7-413d-8736-fce344d42500
-- title:
--   Unit ball laws in label space and normalized densities
-- statement:
--   Normalizations used for moments against the unit ball in $\mathbb R^k$.
--
--   1. **Unit ball.** The volume of the closed unit ball of $\mathbb R^k$ is finite and nonzero, so its normalized restriction of Lebesgue measure is a probability measure:
--   $$
--   \mathrm{vol}(\bar B)^{-1}\,\mathrm{vol}|_{\bar B} .
--   $$
--   2. **Normalized density.** For a measure $\nu$ and a fallback frame $u$, the normalized density of the polar-normalized Gaussian projections of $\nu$ is measurable.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/BallMoments.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/BallMoments.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments

section
attribute [fun_prop] measurable_polarRows
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma unitBallVolume_ne_zero (k : ℕ) : unitBallVolume k ≠ 0 := by
  apply ne_of_gt
  exact (Metric.measure_ball_pos volume 0 one_pos).trans_le (measure_mono Metric.ball_subset_closedBall)
lemma unitBallVolume_ne_top (k : ℕ) : unitBallVolume k ≠ ∞ :=
  (isCompact_closedBall (0 : Label k) (1:ℝ)).measure_ne_top
instance unitBallLaw_probability (k : ℕ) : IsProbabilityMeasure (unitBallLaw k) := by
  constructor
  simp only [unitBallLaw, Measure.smul_apply, Measure.restrict_apply_univ,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel (unitBallVolume_ne_zero k) (unitBallVolume_ne_top k)

@[fun_prop] lemma measurable_normalizedDensity (ν : Measure E) [SFinite ν] (k : ℕ) (u : Fin k → E) :
    Measurable (normalizedDensity ν k u) := by
  exact measurable_const.mul ((measurable_lowerDensity ν k).comp
    (((measurable_polarRows u).comp measurable_fst).prodMk measurable_snd))

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end

end ProjectionMoments

end

end OAI


