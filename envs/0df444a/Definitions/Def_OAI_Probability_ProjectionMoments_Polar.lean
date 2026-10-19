-- Prove2me | Definitions.Def_OAI_Probability_ProjectionMoments_Polar
-- name    : OAI_Probability_ProjectionMoments_Polar
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T17:03:57.952103+00:00
-- url     : https://prove2.me/theorems/c86f16bd-ce6c-4969-8c5b-7c3924672b55
-- title:
--   Polar normalization of Gaussian rows
-- statement:
--   Measurability facts for the polar normalization of a family of $k$ rows in an inner product space.
--
--   1. **Matrix spaces.** Real $k\times k$ matrices carry the product measurable and Borel structures, and matrix inversion is measurable.
--   2. **Mixing rows.** Multiplying a family of rows by a $k\times k$ matrix mixes them; the identity matrix leaves them unchanged. The polar radial part, the square root of the Gram matrix, is continuous.
--   3. **Polar rows.** The raw polar rows $X\mapsto(X^\top X)^{-1/2}X$ and the polar rows used with a fallback family $u$ are measurable, and the set of linearly independent families is measurable:
--   $$
--   \{X:\ X_1,\dots,X_k\ \text{linearly independent}\}\ \text{is measurable}.
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/Polar.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/Polar.lean by skeleton subtraction
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
open scoped ENNReal NNReal RealInnerProductSpace Topology MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

instance realMatrixMeasurableSpace (k : ℕ) : MeasurableSpace (Matrix (Fin k) (Fin k) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin k → Fin k → ℝ))
instance realMatrixBorelSpace (k : ℕ) : BorelSpace (Matrix (Fin k) (Fin k) ℝ) :=
  inferInstanceAs (BorelSpace (Fin k → Fin k → ℝ))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] lemma mixRows_one [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {k : ℕ} (X : Fin k → E) : mixRows 1 X = X := by
  ext i
  simp [mixRows, Matrix.one_apply]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma continuous_polarRadial [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {k : ℕ} : Continuous (polarRadial (E := E) (k := k)) := by
  apply CFC.continuousOn_sqrt.comp_continuous
  · exact continuous_matrix (fun i j => by simp only [Matrix.gram_apply]; fun_prop)
  · intro X
    exact (Matrix.posSemidef_gram ℝ X).nonneg

lemma measurable_matrix_inverse {k : ℕ} :
    Measurable (fun M : Matrix (Fin k) (Fin k) ℝ => M⁻¹) := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv]
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.adjugate_apply]
  fun_prop

lemma measurable_rawPolarRows {k : ℕ} : Measurable (rawPolarRows (E := E) (k := k)) := by
  have hH := measurable_matrix_inverse.comp (continuous_polarRadial (E := E) (k := k)).measurable
  apply Measurable.of_eval
  intro i
  change Measurable (fun X : Fin k → E => ∑ j, (polarRadial X)⁻¹ i j • X j)
  apply Finset.measurable_sum
  intro j hj
  have hh : Measurable (fun X : Fin k → E => (polarRadial X)⁻¹ i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hH)
  exact hh.smul (measurable_pi_apply j)

lemma measurableSet_linearIndependent {k : ℕ} :
    MeasurableSet {X : Fin k → E | LinearIndependent ℝ X} := by
  simp only [← Matrix.det_gram_ne_zero_iff_linearIndependent]
  have hg : Continuous (fun X : Fin k → E => Matrix.gram ℝ X) :=
    continuous_matrix (fun i j => by simp only [Matrix.gram_apply]; fun_prop)
  exact (isClosed_eq hg.matrix_det continuous_const).measurableSet.compl

lemma measurable_polarRows {k : ℕ} (u : Fin k → E) : Measurable (polarRows u) := by
  classical
  exact Measurable.ite measurableSet_linearIndependent measurable_rawPolarRows measurable_const

end

end ProjectionMoments

end

end OAI


