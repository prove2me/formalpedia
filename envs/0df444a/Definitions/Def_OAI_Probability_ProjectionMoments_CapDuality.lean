-- Prove2me | Definitions.Def_OAI_Probability_ProjectionMoments_CapDuality
-- name    : OAI_Probability_ProjectionMoments_CapDuality
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T17:11:52.078056+00:00
-- url     : https://prove2.me/theorems/bcbabd86-ff0a-4b1b-b614-6eb8062cfef5
-- title:
--   Measurability of radial labels and cap kernel values
-- statement:
--   Measurability facts for labels of polar-normalized projections onto $k$ rows.
--
--   1. **Radial labels.** For rows $X=(X_1,\dots,X_k)$ and a label $y\in\mathbb R^k$, the radial label is $(X^\top X)^{1/2}y$; it is jointly measurable in $(X,y)$.
--   2. **Cap reference labels.** For a centre $c$ and radius $r$, the cap reference label is $(\langle c,X_i\rangle)_i+r\,(X^\top X)^{1/2}z$, which parametrizes projections of the cap around $c$ by points $z$ of the unit ball; it is measurable.
--   3. **Cap kernel values.** For a measurable kernel $K$ on (rows, labels), the cap kernel value at $s$ averages $K$ over Gaussian rows at the true labels:
--   $$
--   \int K\bigl(X,(\langle s,X_i\rangle)_i\bigr)\,d\gamma^{\otimes k}(X),
--   $$
--   which is measurable in $s$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/CapDuality.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/CapDuality.lean by skeleton subtraction
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

-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
private theorem Measurable.of_eval {α δ : Type*} {X : δ → Type*}
    [MeasurableSpace α] [∀ a, MeasurableSpace (X a)] {f : α → ∀ a, X a}
    (hf : ∀ a, Measurable fun c => f c a) : Measurable f :=
  measurable_pi_lambda f hf
end Lean433MeasurableOfEval

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace Matrix
open MeasureTheory
open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

@[fun_prop] lemma measurable_radialLabel {k : ℕ} :
    Measurable (fun z : (Fin k → E) × Label k => radialLabel z.1 z.2) := by
  have hH : Measurable (fun z : (Fin k → E) × Label k => polarRadial z.1) := (continuous_polarRadial (E := E) (k := k)).measurable.comp measurable_fst
  apply (MeasurableEquiv.toLp 2 (Fin k → ℝ)).measurable.comp
  apply Measurable.of_eval
  intro i
  change Measurable (fun z : (Fin k → E) × Label k => ∑ j, polarRadial z.1 i j * z.2.ofLp j)
  apply Finset.measurable_sum
  intro j hj
  exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hH)).mul (by fun_prop)

@[fun_prop] lemma measurable_capReferenceLabel {k : ℕ} (c : E) (r : ℝ) :
    Measurable (fun z : (Fin k → E) × Label k => capReferenceLabel c r z.1 z.2) := by
  unfold capReferenceLabel
  exact (show Measurable (fun z : (Fin k → E) × Label k => rowMap z.1 c) by
    simp only [rowMap_apply]; fun_prop).add (measurable_radialLabel.const_smul r)

@[fun_prop] lemma measurable_capKernelValue {k : ℕ} {K : (Fin k → E) × Label k → ℝ≥0∞}
    (hK : Measurable K) : Measurable (capKernelValue K) := by
  apply Measurable.lintegral_prod_right
  exact hK.comp (measurable_snd.prodMk (by simp only [rowMap_apply]; fun_prop))

end

end ProjectionMoments

end

end OAI


