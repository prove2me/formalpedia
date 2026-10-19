-- Prove2me | Definitions.Def_OAI_Probability_ProjectionMoments_SphereDensity
-- name    : OAI_Probability_ProjectionMoments_SphereDensity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T16:58:00.236304+00:00
-- url     : https://prove2.me/theorems/47b039c9-c299-450f-ac33-9f930ccb4c4e
-- title:
--   The projection kernel of a measure
-- statement:
--   For an s-finite measure $\nu$ on a finite-dimensional inner product space $E$ and $m$ rows, the projection kernel maps rows $A=(A_1,\dots,A_m)$ to the image of $\nu$ under the coordinate map:
--   $$
--   A\mapsto\bigl(x\mapsto(\langle x,A_i\rangle)_{i\le m}\bigr)_*\nu .
--   $$
--
--   It is a measurable kernel, finite when $\nu$ is finite; the coordinate map is jointly measurable in rows and points.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/SphereDensity.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/SphereDensity.lean by skeleton subtraction
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

-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
private theorem Measurable.of_eval {α δ : Type*} {X : δ → Type*}
    [MeasurableSpace α] [∀ a, MeasurableSpace (X a)] {f : α → ∀ a, X a}
    (hf : ∀ a, Measurable fun c => f c a) : Measurable f :=
  measurable_pi_lambda f hf
end Lean433MeasurableOfEval

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace ProjectionMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

@[fun_prop] lemma measurable_coordinateMap (m : ℕ) :
    Measurable (fun z : (Fin m → E) × E => coordinateMap z.1 z.2) := by
  apply Measurable.of_eval
  intro i
  simp only [coordinateMap_apply]
  fun_prop

def projectionKernel (ν : Measure E) [SFinite ν] (m : ℕ) : Kernel (Fin m → E) (Fin m → ℝ) where
  toFun A := ν.map (coordinateMap A)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    have he (A : Fin m → E) : (ν.map (coordinateMap A)) s =
        ∫⁻ x, s.indicator (fun _ => (1 : ℝ≥0∞)) (coordinateMap A x) ∂ν := by
      rw [← lintegral_map (measurable_const.indicator hs) (by fun_prop)]
      simp [lintegral_indicator hs]
    simp_rw [he]
    apply Measurable.lintegral_prod_right
    exact (measurable_const.indicator hs).comp (measurable_coordinateMap m)

instance projectionKernel_finite (ν : Measure E) [IsFiniteMeasure ν] (m : ℕ) :
    IsFiniteKernel (projectionKernel ν m) := by
  refine ⟨ν Set.univ, measure_lt_top _ _, ?_⟩
  intro A
  change (ν.map (coordinateMap A)) Set.univ ≤ _
  rw [Measure.map_apply (by fun_prop) MeasurableSet.univ, Set.preimage_univ]

end ProjectionMoments
end

end

end OAI


