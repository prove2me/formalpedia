-- Prove2me | Definitions.Def_OAI_Probability_ProjectionMoments_Frames
-- name    : OAI_Probability_ProjectionMoments_Frames
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T16:55:50.516479+00:00
-- url     : https://prove2.me/theorems/6b3263c7-cc66-4775-8527-cf793798e129
-- title:
--   Rotation-invariant frame laws and moments of projected densities
-- statement:
--   Orthonormal frames, rotations and moments of the densities of projections of a measure $\nu$ on a finite-dimensional inner product space $E$.
--
--   1. **Rotations.** The Haar probability measure on the rotation group acts on families of rows by rotating each row; this action is measurable. The frame law of a family $u$ is the image of Haar measure under $O\mapsto Ou$.
--   2. **Coordinate maps.** For rows $A_1,\dots,A_m$, the coordinate map is $x\mapsto(\langle x,A_i\rangle)_i$, and the row Jacobian is $\prod_i\|g_i\|$ for the Gram–Schmidt vectors $g_i$.
--   3. **Moments.** The coordinate density of $\nu$ is measurable. Its label moment and orbit moment are
--   $$
--   \int f(A,y)^{n+1}\,dy\quad\text{and}\quad\int\int f(OA,y)^{n+1}\,dy\,dO .
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/Frames.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/Frames.lean by skeleton subtraction
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

-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace ProjectionMoments
attribute [fun_prop] measurable_lowerDensity

section Rotations
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

instance rotationLaw_probability : IsProbabilityMeasure (rotationLaw E) := by
  constructor
  simp only [rotationLaw, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel ((ne_of_gt (isOpen_univ.measure_pos (Measure.haar : Measure (Rotation E)) Set.univ_nonempty))) (measure_ne_top _ _)

instance rotationLaw_haar : (rotationLaw E).IsHaarMeasure := by
  unfold rotationLaw
  apply Measure.IsHaarMeasure.smul _
  · exact ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)
  · exact ENNReal.inv_ne_top.mpr (ne_of_gt (isOpen_univ.measure_pos (Measure.haar : Measure (Rotation E)) Set.univ_nonempty))

instance rotationLaw_right : (rotationLaw E).IsMulRightInvariant := by
  constructor
  intro Q
  let μ := (rotationLaw E).map (fun O => O * Q)
  have hprob : IsProbabilityMeasure μ :=
    Measure.isProbabilityMeasure_map (continuous_mul_right Q).measurable.aemeasurable
  have he := Measure.isMulInvariant_eq_smul_of_compactSpace μ (rotationLaw E)
  have hc := congrArg (fun ν : Measure (Rotation E) => ν Set.univ) he
  simp only [Measure.smul_apply, measure_univ, ENNReal.smul_def, smul_eq_mul, mul_one] at hc
  have hc' : Measure.haarScalarFactor μ (rotationLaw E) = 1 :=
    ENNReal.coe_injective hc.symm
  simpa [hc'] using he

variable {E}

variable [MeasurableSpace E] [BorelSpace E]

lemma measurable_rotateRows {ι : Type*} [Fintype ι] :
    Measurable (fun z : Rotation E × (ι → E) => rotateRows z.1 z.2) := by
  apply Continuous.measurable
  apply continuous_pi
  intro i
  exact (continuous_subtype_val.comp continuous_fst).clm_apply (continuous_apply i |>.comp continuous_snd)

@[fun_prop] lemma measurable_rotateRows_left {ι : Type*} [Fintype ι] (v : ι → E) :
    Measurable (fun O : Rotation E => rotateRows O v) :=
  measurable_rotateRows.comp (measurable_id.prodMk measurable_const)

@[fun_prop] lemma measurable_rotateRows_right {ι : Type*} [Fintype ι] (O : Rotation E) :
    Measurable (fun v : ι → E => rotateRows O v) :=
  measurable_rotateRows.comp (measurable_const.prodMk measurable_id)

end Rotations

section Triangular
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] lemma coordinateMap_apply [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {m : ℕ} (A : Fin m → E) (x : E) (i : Fin m) :
    coordinateMap A x i = ⟪x, A i⟫ := by
  change WithLp.ofLp (rowMap A x) i = _
  rw [rowMap_apply]

def rowJacobian {m : ℕ} (A : Fin m → E) : ℝ :=
  ∏ i, ‖gramSchmidt ℝ A i‖

end Triangular

section CoordinateDensity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

@[fun_prop] lemma measurable_coordinateDensity (ν : Measure E) [SFinite ν] (m : ℕ) :
    Measurable (coordinateDensity ν m) := by
  exact (measurable_lowerDensity ν m).comp (by fun_prop)

def labelMoment (ν : Measure E) (m n : ℕ) (A : Fin m → E) : ℝ≥0∞ :=
  ∫⁻ y, coordinateDensity ν m (A,y)^(n+1)

@[fun_prop] lemma measurable_labelMoment (ν : Measure E) [SFinite ν] (m n : ℕ) :
    Measurable (labelMoment ν m n) := by
  exact Measurable.lintegral_prod_right (by fun_prop)

end CoordinateDensity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

instance frameLaw_probability {m : ℕ} (u : Fin m → E) : IsProbabilityMeasure (frameLaw u) :=
  Measure.isProbabilityMeasure_map (μ := rotationLaw E) (measurable_rotateRows_left u).aemeasurable

def orbitMoment (ν : Measure E) (m n : ℕ) (A : Fin m → E) : ℝ≥0∞ :=
  ∫⁻ O, labelMoment ν m n (rotateRows O A) ∂rotationLaw E

@[fun_prop] lemma measurable_orbitMoment (ν : Measure E) [SFinite ν] (m n : ℕ) :
    Measurable (orbitMoment ν m n) := by
  apply Measurable.lintegral_prod_right
  exact (measurable_labelMoment ν m n).comp (measurable_rotateRows.comp measurable_swap)

end ProjectionMoments
end

end OAI


