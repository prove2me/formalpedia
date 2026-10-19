-- Prove2me | Definitions.Def_OAI_Probability_ProjectionMoments_Graph
-- name    : OAI_Probability_ProjectionMoments_Graph
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T16:54:04.128532+00:00
-- url     : https://prove2.me/theorems/571d32b5-0628-42c9-92a1-87e2d4256717
-- title:
--   Ball averages, lower densities and rescalings of measures
-- statement:
--   Measurability and normalization facts for projected densities of a measure $\nu$ on a finite-dimensional inner product space $E$.
--
--   1. **Measurability.** The vector smoothing of $\nu$ against a measurable profile, the ball kernels, the ball averages of projections, and the lower density are measurable. The lower density is the liminf of averages over small balls of the projection $t\mapsto(\langle t,A_j\rangle)_j$.
--   2. **Rescaling.** For a centre $z$ and radius $R$, rescaling is $x\mapsto R^{-1}(x-z)$ and dilation its inverse $x\mapsto Rx+z$; both are measurable.
--   3. **Normalized rescale.** For constants $K,a$,
--   $$
--   \nu_{z,R}=(KR^a)^{-1}\,(\mathrm{rescale}_{z,R})_*\nu ,
--   $$
--   which moves a measure with mass bound $(K,a)$ to unit scale.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/Graph.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/Graph.lean by skeleton subtraction
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

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace ProjectionMoments

section GaussianGraph
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma measurable_vectorSmoothing (ν : Measure E) [SFinite ν] (m : ℕ)
    (φ : (Fin m → ℝ) → ℝ≥0∞) (hφ : Measurable φ) :
    Measurable (vectorSmoothing ν m φ) := by
  apply Measurable.lintegral_prod_right
  exact hφ.comp (by fun_prop)

end GaussianGraph

lemma measurable_ballKernel (m : ℕ) (η : ℝ) : Measurable (ballKernel m η) := by
  exact (measurable_const.indicator Metric.isClosed_closedBall.measurableSet).comp
    (PiLp.continuous_toLp 2 (fun _ : Fin m => ℝ)).measurable

section BallDensity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] lemma rowMap_apply {m : ℕ} (A : Fin m → E) (t : E) :
    rowMap A t = WithLp.toLp 2 (fun j => ⟪t, A j⟫) := by
  ext j
  simp [rowMap, real_inner_comm]

lemma measurable_ballAverage (ν : Measure E) [SFinite ν] (m : ℕ) (η : ℝ) :
    Measurable (ballAverage ν m η) := by
  exact (measurable_vectorSmoothing ν m (ballKernel m η)
    (measurable_ballKernel m η)).comp
      (measurable_fst.prodMk ((PiLp.continuous_ofLp 2 (fun _ : Fin m => ℝ)).measurable.comp
        measurable_snd))

lemma measurable_lowerDensity (ν : Measure E) [SFinite ν] (m : ℕ) :
    Measurable (lowerDensity ν m) :=
  Measurable.liminf (fun _n => measurable_ballAverage ν m _)

end BallDensity

section Rescaling
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def rescale (z : E) (R : ℝ) (x : E) : E := R⁻¹ • (x-z)
def dilate (z : E) (R : ℝ) (x : E) : E := R • x + z

omit [FiniteDimensional ℝ E] in
@[fun_prop] lemma measurable_rescale (z : E) (R : ℝ) : Measurable (rescale z R) := by
  unfold rescale; fun_prop
omit [FiniteDimensional ℝ E] in
@[fun_prop] lemma measurable_dilate (z : E) (R : ℝ) : Measurable (dilate z R) := by
  unfold dilate; fun_prop

def normalizedRescale (ν : Measure E) (K a : ℝ) (z : E) (R : ℝ) : Measure E :=
  (ENNReal.ofReal (K * R ^ a))⁻¹ • ν.map (rescale z R)

end Rescaling

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end ProjectionMoments
end

end OAI


