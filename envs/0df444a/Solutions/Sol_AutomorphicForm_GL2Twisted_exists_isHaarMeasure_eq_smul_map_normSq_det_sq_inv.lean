-- Prove2me | solution 1 for AutomorphicForm.GL2Twisted.exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/6025d732-2f29-5aa8-9314-5c0715784879

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Constructions
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Comap
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Complex
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.RingTheory.TensorProduct.Maps
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_GL2Twisted_exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv

set_option autoImplicit false

namespace TwistedHaar
namespace MatrixBorel

private scoped instance matrixMeasurableSpace {K : Type*} [MeasurableSpace K] :
    MeasurableSpace (Matrix (Fin 2) (Fin 2) K) :=
  inferInstanceAs (MeasurableSpace ((Fin 2) → (Fin 2) → K))

end TwistedHaar.MatrixBorel
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Twisted_exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv.TwistedHaar P2MW.S_AutomorphicForm_GL2Twisted_exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv.TwistedHaar.MatrixBorel"
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Twisted_exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv.TwistedHaar"

namespace TwistedHaar
namespace MatrixBorel

open Set Filter Function MeasureTheory Matrix Topology
open scoped ENNReal NNReal BigOperators Classical

noncomputable section

section BorelBridge

private scoped instance matrixFin2BorelSpace {R : Type*} [TopologicalSpace R] [MeasurableSpace R]
    [BorelSpace R] [SecondCountableTopology R] :
    BorelSpace (Matrix (Fin 2) (Fin 2) R) :=
  inferInstanceAs (BorelSpace ((Fin 2) → (Fin 2) → R))

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [ContinuousInv₀ K]

private theorem gl2_isEmbedding_val :
    IsEmbedding (Units.val : GL (Fin 2) K → Matrix (Fin 2) (Fin 2) K) := by
  refine Units.isEmbedding_val_mk' (f := Inv.inv) ?_ ?_
  · intro A hA
    have hdet : IsUnit (Matrix.det A) := (Matrix.isUnit_iff_isUnit_det A).mp hA
    have hdet0 : Matrix.det A ≠ 0 := hdet.ne_zero
    have hcont : ContinuousAt Ring.inverse (Matrix.det A) := by
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ hdet0
    exact (continuousAt_matrix_inv A hcont).continuousWithinAt
  · intro u
    exact (Matrix.coe_units_inv u).symm

variable [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]

private scoped instance gl2CommittedBorelSpace : BorelSpace (GL (Fin 2) K) := by
  have hval : IsEmbedding (Units.val : GL (Fin 2) K → Matrix (Fin 2) (Fin 2) K) :=
    gl2_isEmbedding_val
  have hmat : (matrixMeasurableSpace : MeasurableSpace (Matrix (Fin 2) (Fin 2) K))
      = borel (Matrix (Fin 2) (Fin 2) K) := BorelSpace.measurable_eq
  refine ⟨?_⟩

  have h1 : (Units.instMeasurableSpace : MeasurableSpace (GL (Fin 2) K))
      = MeasurableSpace.comap Units.val (borel (Matrix (Fin 2) (Fin 2) K)) := by
    rw [← hmat]
    rfl

  have h2 : MeasurableSpace.comap (Units.val : GL (Fin 2) K → Matrix (Fin 2) (Fin 2) K)
        (borel (Matrix (Fin 2) (Fin 2) K))
      = @borel (GL (Fin 2) K)
          (TopologicalSpace.induced (Units.val : GL (Fin 2) K → Matrix (Fin 2) (Fin 2) K)
            inferInstance) :=
    borel_comap.symm

  have h3 : (TopologicalSpace.induced (Units.val : GL (Fin 2) K → Matrix (Fin 2) (Fin 2) K)
        (inferInstance : TopologicalSpace (Matrix (Fin 2) (Fin 2) K)))
      = (inferInstance : TopologicalSpace (GL (Fin 2) K)) :=
    hval.toIsInducing.eq_induced.symm
  calc (inferInstance : MeasurableSpace (GL (Fin 2) K))
      = MeasurableSpace.comap Units.val (borel (Matrix (Fin 2) (Fin 2) K)) := h1
    _ = @borel (GL (Fin 2) K)
          (TopologicalSpace.induced (Units.val : GL (Fin 2) K → Matrix (Fin 2) (Fin 2) K)
            inferInstance) := h2
    _ = borel (GL (Fin 2) K) := by rw [h3]

end BorelBridge
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Twisted_exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv.TwistedHaar P2MW.S_AutomorphicForm_GL2Twisted_exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv.TwistedHaar.MatrixBorel"

end
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Twisted_exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv.TwistedHaar P2MW.S_AutomorphicForm_GL2Twisted_exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv.TwistedHaar.MatrixBorel"

end TwistedHaar.MatrixBorel
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Twisted_exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv.TwistedHaar P2MW.S_AutomorphicForm_GL2Twisted_exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv.TwistedHaar.MatrixBorel"
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Twisted_exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv.TwistedHaar P2MW.S_AutomorphicForm_GL2Twisted_exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv.TwistedHaar.MatrixBorel"

namespace TwistedHaar
namespace GL2ComplexFurniture

open Topology

private theorem continuousOn_matrixInv_isUnit' :
    ContinuousOn (fun A : Matrix (Fin 2) (Fin 2) ℂ => A⁻¹) {A | IsUnit A} := by
  have h : (fun A : Matrix (Fin 2) (Fin 2) ℂ => A⁻¹) = fun A => (A.det)⁻¹ • A.adjugate := by
    funext A
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  refine ContinuousOn.fun_smul ?_ ((continuous_id (X := Matrix (Fin 2) (Fin 2) ℂ)).matrix_adjugate).continuousOn
  exact ((continuous_id (X := Matrix (Fin 2) (Fin 2) ℂ)).matrix_det).continuousOn.inv₀ fun A hA =>
    ((Matrix.isUnit_iff_isUnit_det A).mp hA).ne_zero

private theorem isEmbedding_glVal' : IsEmbedding (Units.val : GL (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ) :=
  Units.isEmbedding_val_mk' continuousOn_matrixInv_isUnit' fun u => (Matrix.coe_units_inv u).symm

private theorem isOpen_range_glVal' : IsOpen (Set.range (Units.val : GL (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ)) := by
  have h : Set.range (Units.val : GL (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ) =
      (fun A : Matrix (Fin 2) (Fin 2) ℂ => A.det) ⁻¹' {x | x ≠ 0} := by
    ext A
    constructor
    · rintro ⟨u, rfl⟩
      exact ((Matrix.isUnit_iff_isUnit_det _).mp u.isUnit).ne_zero
    · intro hA
      exact (Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hA)
  rw [h]
  exact isOpen_ne.preimage (Continuous.matrix_det continuous_id)

private theorem isOpenEmbedding_glVal' : IsOpenEmbedding (Units.val : GL (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ) :=
  ⟨isEmbedding_glVal', isOpen_range_glVal'⟩

private theorem locallyCompactSpace_gl' : LocallyCompactSpace (GL (Fin 2) ℂ) := by
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → ℂ))
  exact isOpenEmbedding_glVal'.locallyCompactSpace

private theorem secondCountableTopology_gl' : SecondCountableTopology (GL (Fin 2) ℂ) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  exact isEmbedding_glVal'.secondCountableTopology

private scoped instance : LocallyCompactSpace (GL (Fin 2) ℂ) := locallyCompactSpace_gl'
private scoped instance : SecondCountableTopology (GL (Fin 2) ℂ) := secondCountableTopology_gl'

end TwistedHaar.GL2ComplexFurniture
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Twisted_exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv.TwistedHaar P2MW.S_AutomorphicForm_GL2Twisted_exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv.TwistedHaar.MatrixBorel P2MW.S_AutomorphicForm_GL2Twisted_exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv.TwistedHaar.GL2ComplexFurniture"
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Twisted_exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv.TwistedHaar P2MW.S_AutomorphicForm_GL2Twisted_exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv.TwistedHaar.MatrixBorel"

open Set Function MeasureTheory Matrix Topology
open scoped ENNReal NNReal MatrixGroups

namespace TwistedHaar
namespace GL2ComplexEntryModel

open TwistedHaar.MatrixBorel

noncomputable section

private def gl2MatrixLebesgue : Measure (Matrix (Fin 2) (Fin 2) ℂ) :=
  (volume : Measure ((Fin 2) → (Fin 2) → ℂ))

private theorem gl2MatrixLebesgue_def :
    gl2MatrixLebesgue = (volume : Measure ((Fin 2) → (Fin 2) → ℂ)) := rfl

private scoped instance gl2PiVolume_isAddHaarMeasure₁ :
    Measure.IsAddHaarMeasure (volume : Measure ((Fin 2) → ℂ)) :=
  Measure.pi.isAddHaarMeasure _

private scoped instance gl2PiVolume_isAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure ((Fin 2) → (Fin 2) → ℂ)) :=
  Measure.pi.isAddHaarMeasure _

private scoped instance gl2MatrixLebesgue_isOpenPosMeasure : gl2MatrixLebesgue.IsOpenPosMeasure :=
  inferInstanceAs (Measure.IsOpenPosMeasure (volume : Measure ((Fin 2) → (Fin 2) → ℂ)))

private scoped instance gl2MatrixLebesgue_isFiniteMeasureOnCompacts :
    IsFiniteMeasureOnCompacts gl2MatrixLebesgue :=
  inferInstanceAs (IsFiniteMeasureOnCompacts (volume : Measure ((Fin 2) → (Fin 2) → ℂ)))

private scoped instance gl2MatrixLebesgue_sigmaFinite : SigmaFinite gl2MatrixLebesgue :=
  inferInstanceAs (SigmaFinite (volume : Measure ((Fin 2) → (Fin 2) → ℂ)))

private theorem gl2_measurable_det : Measurable fun A : Matrix (Fin 2) (Fin 2) ℂ => A.det :=
  continuous_id.matrix_det.measurable

private theorem gl2_val_det_ne_zero (g : GL (Fin 2) ℂ) :
    ((g : Matrix (Fin 2) (Fin 2) ℂ)).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero

private theorem gl2_val_det_mul_inv_det (g : GL (Fin 2) ℂ) :
    ((g : Matrix (Fin 2) (Fin 2) ℂ)).det
      * (((g⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)).det = 1 := by
  rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]

private theorem gl2_isOpen_unitLocus : IsOpen {A : Matrix (Fin 2) (Fin 2) ℂ | IsUnit A} := by
  have h : {A : Matrix (Fin 2) (Fin 2) ℂ | IsUnit A}
      = (fun A : Matrix (Fin 2) (Fin 2) ℂ => A.det) ⁻¹' {x : ℂ | x ≠ 0} := by
    ext A
    simp [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  rw [h]
  exact (isOpen_compl_iff.mpr isClosed_singleton).preimage continuous_id.matrix_det

private theorem gl2_range_val :
    Set.range (Units.val : GL (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ)
      = {A : Matrix (Fin 2) (Fin 2) ℂ | IsUnit A} := by
  ext A
  constructor
  · rintro ⟨u, rfl⟩
    exact u.isUnit
  · intro hA
    exact ⟨hA.unit, rfl⟩

private theorem gl2_measurableSet_range_val :
    MeasurableSet (Set.range (Units.val : GL (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ)) := by
  rw [gl2_range_val]
  exact gl2_isOpen_unitLocus.measurableSet

private theorem gl2_measurableEmbedding_val :
    MeasurableEmbedding (Units.val : GL (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ) :=
  (gl2_isEmbedding_val (K := ℂ)).measurableEmbedding gl2_measurableSet_range_val

private theorem gl2_isOpenEmbedding_val :
    IsOpenEmbedding (Units.val : GL (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ) :=
  { toIsEmbedding := gl2_isEmbedding_val (K := ℂ)
    isOpen_range := by rw [gl2_range_val]; exact gl2_isOpen_unitLocus }

private def gl2DetSqDensity (A : Matrix (Fin 2) (Fin 2) ℂ) : ℝ≥0∞ :=
  (ENNReal.ofReal (Complex.normSq A.det ^ 2))⁻¹

private theorem gl2DetSqDensity_def (A : Matrix (Fin 2) (Fin 2) ℂ) :
    gl2DetSqDensity A = (ENNReal.ofReal (Complex.normSq A.det ^ 2))⁻¹ := rfl

private theorem gl2_measurable_detSqDensity : Measurable gl2DetSqDensity := by
  have hcont : Continuous fun A : Matrix (Fin 2) (Fin 2) ℂ => Complex.normSq A.det ^ 2 :=
    (Complex.continuous_normSq.comp continuous_id.matrix_det).pow 2
  exact (ENNReal.measurable_ofReal.comp hcont.measurable).inv

private theorem gl2DetSqDensity_ne_zero (A : Matrix (Fin 2) (Fin 2) ℂ) :
    gl2DetSqDensity A ≠ 0 := by
  rw [gl2DetSqDensity_def]
  exact ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top

private theorem gl2DetSqDensity_one : gl2DetSqDensity (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  rw [gl2DetSqDensity_def, Matrix.det_one, Complex.normSq_one, one_pow, ENNReal.ofReal_one, inv_one]

private theorem gl2DetSqDensity_lt_top_of_isUnit {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : IsUnit A) :
    gl2DetSqDensity A < ∞ := by
  rw [gl2DetSqDensity_def]
  have hdet : A.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp hA).ne_zero
  exact ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr (pow_pos (Complex.normSq_pos.mpr hdet) 2))

private theorem gl2_detSq_factor_mul {a b : ℂ} (hab : a * b = 1) (x : ℂ) :
    (ENNReal.ofReal (Complex.normSq a ^ 2))⁻¹
        * (ENNReal.ofReal (Complex.normSq b ^ 2 * Complex.normSq x ^ 2))⁻¹
      = (ENNReal.ofReal (Complex.normSq x ^ 2))⁻¹ := by
  have ha : a ≠ 0 := left_ne_zero_of_mul_eq_one hab
  have habs : Complex.normSq a * Complex.normSq b = 1 := by rw [← Complex.normSq_mul, hab, Complex.normSq_one]
  have h1 : (ENNReal.ofReal (Complex.normSq a ^ 2)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (pow_pos (Complex.normSq_pos.mpr ha) 2)).ne'
  rw [← ENNReal.mul_inv (Or.inl h1) (Or.inl ENNReal.ofReal_ne_top),
    ← ENNReal.ofReal_mul (sq_nonneg _)]
  congr 2
  calc Complex.normSq a ^ 2 * (Complex.normSq b ^ 2 * Complex.normSq x ^ 2)
      = (Complex.normSq a * Complex.normSq b) ^ 2 * Complex.normSq x ^ 2 := by ring
    _ = Complex.normSq x ^ 2 := by rw [habs]; ring

private theorem gl2_detSq_factor_mul' {a b : ℂ} (hab : a * b = 1) (x : ℂ) :
    (ENNReal.ofReal (Complex.normSq a ^ 2))⁻¹
        * (ENNReal.ofReal (Complex.normSq x ^ 2 * Complex.normSq b ^ 2))⁻¹
      = (ENNReal.ofReal (Complex.normSq x ^ 2))⁻¹ := by
  rw [mul_comm (Complex.normSq x ^ 2) (Complex.normSq b ^ 2)]
  exact gl2_detSq_factor_mul hab x

private def transposeLM : (Fin 2 → Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → Fin 2 → ℂ) where
  toFun A := fun i j => A j i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem transposeLM_apply (A : Matrix (Fin 2) (Fin 2) ℂ) : transposeLM A = A.transpose := rfl

private theorem transposeLM_comp_self : transposeLM.comp transposeLM = LinearMap.id := by
  ext A i j
  rfl

private theorem transposeLM_det_mul_self : transposeLM.det * transposeLM.det = 1 := by
  rw [← LinearMap.det_comp, transposeLM_comp_self, LinearMap.det_id]

private noncomputable def mulRightLM (T : Matrix (Fin 2) (Fin 2) ℂ) :
    (Fin 2 → Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → Fin 2 → ℂ) :=
  LinearMap.pi fun i : Fin 2 =>
    (Matrix.toLin' T.transpose).comp (LinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => Fin 2 → ℂ) i)

private theorem mulRightLM_apply (T A : Matrix (Fin 2) (Fin 2) ℂ) : mulRightLM T A = A * T := by
  funext i k
  simp [mulRightLM, LinearMap.pi_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply,
    Matrix.transpose_apply, mul_comm]

private theorem mulRightLM_det (T : Matrix (Fin 2) (Fin 2) ℂ) : (mulRightLM T).det = T.det ^ 2 := by
  unfold mulRightLM
  rw [LinearMap.det_pi]
  simp [LinearMap.det_toLin', Finset.prod_const]

private noncomputable def mulLeftLM (T : Matrix (Fin 2) (Fin 2) ℂ) :
    (Fin 2 → Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → Fin 2 → ℂ) :=
  transposeLM.comp ((mulRightLM T.transpose).comp transposeLM)

private theorem mulLeftLM_apply (T A : Matrix (Fin 2) (Fin 2) ℂ) : mulLeftLM T A = T * A := by
  have h1 : mulLeftLM T A = transposeLM (mulRightLM T.transpose (transposeLM A)) := rfl
  rw [h1, transposeLM_apply A, mulRightLM_apply T.transpose A.transpose,
    transposeLM_apply (A.transpose * T.transpose), Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.transpose_transpose]

private theorem mulLeftLM_det (T : Matrix (Fin 2) (Fin 2) ℂ) : (mulLeftLM T).det = T.det ^ 2 := by
  unfold mulLeftLM
  rw [LinearMap.det_comp, LinearMap.det_comp, mulRightLM_det, Matrix.det_transpose]
  calc transposeLM.det * (T.det ^ 2 * transposeLM.det)
      = (transposeLM.det * transposeLM.det) * T.det ^ 2 := by ring
    _ = T.det ^ 2 := by rw [transposeLM_det_mul_self, one_mul]

private noncomputable def twistLM (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    (Fin 2 → Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → Fin 2 → ℂ) :=
  (mulRightLM B).comp (mulLeftLM A)

private theorem twistLM_apply (A B X : Matrix (Fin 2) (Fin 2) ℂ) : twistLM A B X = A * X * B := by
  have h1 : twistLM A B X = mulRightLM B (mulLeftLM A X) := rfl
  rw [h1, mulLeftLM_apply, mulRightLM_apply]

private theorem twistLM_det (A B : Matrix (Fin 2) (Fin 2) ℂ) : (twistLM A B).det = (A.det * B.det) ^ 2 := by
  unfold twistLM
  rw [LinearMap.det_comp, mulRightLM_det, mulLeftLM_det]
  ring

private theorem twistLM_restrictScalars_det (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    ((twistLM A B).restrictScalars ℝ).det = Complex.normSq (A.det * B.det) ^ 2 := by
  rw [LinearMap.det_restrictScalars, twistLM_det, Algebra.norm_complex_apply, map_pow]

private theorem mulRightLM_det_restrictScalars (T : Matrix (Fin 2) (Fin 2) ℂ) :
    ((mulRightLM T).restrictScalars ℝ).det = Complex.normSq T.det ^ 2 := by
  rw [LinearMap.det_restrictScalars, mulRightLM_det, map_pow, Algebra.norm_complex_apply]

private theorem mulLeftLM_det_restrictScalars (T : Matrix (Fin 2) (Fin 2) ℂ) :
    ((mulLeftLM T).restrictScalars ℝ).det = Complex.normSq T.det ^ 2 := by
  rw [LinearMap.det_restrictScalars, mulLeftLM_det, map_pow, Algebra.norm_complex_apply]

private theorem gl2_jacobian_scalar_eq {T : Matrix (Fin 2) (Fin 2) ℂ} (hT : T.det ≠ 0) :
    ENNReal.ofReal |(Complex.normSq T.det ^ 2)⁻¹| = (ENNReal.ofReal (Complex.normSq T.det ^ 2))⁻¹ := by
  rw [abs_inv, abs_of_nonneg (sq_nonneg _),
    ENNReal.ofReal_inv_of_pos (pow_pos (Complex.normSq_pos.mpr hT) 2)]

private theorem gl2MatrixLebesgue_map_mul_right {T : Matrix (Fin 2) (Fin 2) ℂ} (hT : T.det ≠ 0) :
    gl2MatrixLebesgue.map (fun A : Matrix (Fin 2) (Fin 2) ℂ => A * T)
      = (ENNReal.ofReal (Complex.normSq T.det ^ 2))⁻¹ • gl2MatrixLebesgue := by
  have hdet : ((mulRightLM T).restrictScalars ℝ).det ≠ 0 := by
    rw [mulRightLM_det_restrictScalars]; exact pow_ne_zero 2 (Complex.normSq_pos.mpr hT).ne'
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar
    (volume : Measure ((Fin 2) → (Fin 2) → ℂ)) hdet
  rw [mulRightLM_det_restrictScalars] at h
  rw [gl2_jacobian_scalar_eq hT] at h
  have hcoe : (fun A : Matrix (Fin 2) (Fin 2) ℂ => A * T) = ⇑((mulRightLM T).restrictScalars ℝ) := by
    funext A
    rw [LinearMap.restrictScalars_apply, mulRightLM_apply]
  rw [gl2MatrixLebesgue_def, hcoe]
  exact h

private theorem gl2MatrixLebesgue_map_mul_left {T : Matrix (Fin 2) (Fin 2) ℂ} (hT : T.det ≠ 0) :
    gl2MatrixLebesgue.map (fun A : Matrix (Fin 2) (Fin 2) ℂ => T * A)
      = (ENNReal.ofReal (Complex.normSq T.det ^ 2))⁻¹ • gl2MatrixLebesgue := by
  have hdet : ((mulLeftLM T).restrictScalars ℝ).det ≠ 0 := by
    rw [mulLeftLM_det_restrictScalars]; exact pow_ne_zero 2 (Complex.normSq_pos.mpr hT).ne'
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar
    (volume : Measure ((Fin 2) → (Fin 2) → ℂ)) hdet
  rw [mulLeftLM_det_restrictScalars] at h
  rw [gl2_jacobian_scalar_eq hT] at h
  have hcoe : (fun A : Matrix (Fin 2) (Fin 2) ℂ => T * A) = ⇑((mulLeftLM T).restrictScalars ℝ) := by
    funext A
    rw [LinearMap.restrictScalars_apply, mulLeftLM_apply]
  rw [gl2MatrixLebesgue_def, hcoe]
  exact h

private def gl2DetSqMatrixMeasure : Measure (Matrix (Fin 2) (Fin 2) ℂ) :=
  gl2MatrixLebesgue.withDensity gl2DetSqDensity

private theorem gl2DetSqMatrixMeasure_def :
    gl2DetSqMatrixMeasure = gl2MatrixLebesgue.withDensity gl2DetSqDensity := rfl

private theorem gl2DetSqMatrixMeasure_apply {s : Set (Matrix (Fin 2) (Fin 2) ℂ)}
    (hs : MeasurableSet s) :
    gl2DetSqMatrixMeasure s = ∫⁻ A in s, gl2DetSqDensity A ∂gl2MatrixLebesgue :=
  withDensity_apply _ hs

private theorem gl2_map_withDensity_comp {φ : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ}
    (hφ : Measurable φ) {g : Matrix (Fin 2) (Fin 2) ℂ → ℝ≥0∞} (hg : Measurable g) :
    (gl2MatrixLebesgue.withDensity (g ∘ φ)).map φ = (gl2MatrixLebesgue.map φ).withDensity g := by
  ext s hs
  rw [Measure.map_apply hφ hs, withDensity_apply _ (hφ hs), withDensity_apply _ hs,
    setLIntegral_map hs hg hφ]
  rfl

private theorem gl2DetSqMatrixMeasure_map_eq
    {φ ψ : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ}
    (hφ : Measurable φ) (hψ : Measurable ψ) (hinv : ∀ A, ψ (φ A) = A)
    {c : ℝ≥0∞} (hc : c ≠ ∞)
    (hmap : gl2MatrixLebesgue.map φ = c • gl2MatrixLebesgue)
    (hpt : ∀ B, c * gl2DetSqDensity (ψ B) = gl2DetSqDensity B) :
    gl2DetSqMatrixMeasure.map φ = gl2DetSqMatrixMeasure := by
  have hδψ : Measurable (gl2DetSqDensity ∘ ψ) := gl2_measurable_detSqDensity.comp hψ
  have hcomp : gl2DetSqDensity = (gl2DetSqDensity ∘ ψ) ∘ φ := by
    funext A
    simp only [Function.comp_apply, hinv]
  calc gl2DetSqMatrixMeasure.map φ
      = (gl2MatrixLebesgue.withDensity ((gl2DetSqDensity ∘ ψ) ∘ φ)).map φ := by
        rw [gl2DetSqMatrixMeasure_def, ← hcomp]
    _ = (gl2MatrixLebesgue.map φ).withDensity (gl2DetSqDensity ∘ ψ) :=
        gl2_map_withDensity_comp hφ hδψ
    _ = (c • gl2MatrixLebesgue).withDensity (gl2DetSqDensity ∘ ψ) := by rw [hmap]
    _ = c • gl2MatrixLebesgue.withDensity (gl2DetSqDensity ∘ ψ) :=
        withDensity_smul_measure c _
    _ = gl2MatrixLebesgue.withDensity (c • (gl2DetSqDensity ∘ ψ)) :=
        (withDensity_smul' c _ hc).symm
    _ = gl2MatrixLebesgue.withDensity gl2DetSqDensity := by
        congr 1
        funext B
        simpa using hpt B
    _ = gl2DetSqMatrixMeasure := rfl

private theorem gl2_jacobian_const_ne_top (g : GL (Fin 2) ℂ) :
    ((ENNReal.ofReal (Complex.normSq ((g : Matrix (Fin 2) (Fin 2) ℂ)).det ^ 2))⁻¹ : ℝ≥0∞) ≠ ∞ := by
  have hdet : ((g : Matrix (Fin 2) (Fin 2) ℂ)).det ≠ 0 := gl2_val_det_ne_zero g
  exact (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr (pow_pos (Complex.normSq_pos.mpr hdet) 2))).ne

private theorem gl2DetSqMatrixMeasure_map_mul_left (g : GL (Fin 2) ℂ) :
    gl2DetSqMatrixMeasure.map
        (fun A : Matrix (Fin 2) (Fin 2) ℂ => (g : Matrix (Fin 2) (Fin 2) ℂ) * A)
      = gl2DetSqMatrixMeasure := by
  have hdet : ((g : Matrix (Fin 2) (Fin 2) ℂ)).det ≠ 0 := gl2_val_det_ne_zero g
  have hφ : Measurable (fun A : Matrix (Fin 2) (Fin 2) ℂ =>
      (g : Matrix (Fin 2) (Fin 2) ℂ) * A) :=
    (continuous_const.matrix_mul continuous_id).measurable
  have hψ : Measurable (fun A : Matrix (Fin 2) (Fin 2) ℂ =>
      ((g⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * A) :=
    (continuous_const.matrix_mul continuous_id).measurable
  have hinv : ∀ A : Matrix (Fin 2) (Fin 2) ℂ,
      ((g⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
        * ((g : Matrix (Fin 2) (Fin 2) ℂ) * A) = A := fun A => by
    rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  have hpt : ∀ B : Matrix (Fin 2) (Fin 2) ℂ,
      ((ENNReal.ofReal (Complex.normSq ((g : Matrix (Fin 2) (Fin 2) ℂ)).det ^ 2))⁻¹ : ℝ≥0∞)
        * gl2DetSqDensity (((g⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * B)
        = gl2DetSqDensity B := fun B => by
    rw [gl2DetSqDensity_def, gl2DetSqDensity_def, Matrix.det_mul, Complex.normSq_mul, mul_pow]
    exact gl2_detSq_factor_mul (gl2_val_det_mul_inv_det g) B.det
  exact gl2DetSqMatrixMeasure_map_eq hφ hψ hinv (gl2_jacobian_const_ne_top g)
    (gl2MatrixLebesgue_map_mul_left hdet) hpt

private theorem gl2DetSqMatrixMeasure_map_mul_right (g : GL (Fin 2) ℂ) :
    gl2DetSqMatrixMeasure.map
        (fun A : Matrix (Fin 2) (Fin 2) ℂ => A * (g : Matrix (Fin 2) (Fin 2) ℂ))
      = gl2DetSqMatrixMeasure := by
  have hdet : ((g : Matrix (Fin 2) (Fin 2) ℂ)).det ≠ 0 := gl2_val_det_ne_zero g
  have hφ : Measurable (fun A : Matrix (Fin 2) (Fin 2) ℂ =>
      A * (g : Matrix (Fin 2) (Fin 2) ℂ)) :=
    (continuous_id.matrix_mul continuous_const).measurable
  have hψ : Measurable (fun A : Matrix (Fin 2) (Fin 2) ℂ =>
      A * ((g⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) :=
    (continuous_id.matrix_mul continuous_const).measurable
  have hinv : ∀ A : Matrix (Fin 2) (Fin 2) ℂ,
      (A * (g : Matrix (Fin 2) (Fin 2) ℂ))
        * ((g⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = A := fun A => by
    rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  have hpt : ∀ B : Matrix (Fin 2) (Fin 2) ℂ,
      ((ENNReal.ofReal (Complex.normSq ((g : Matrix (Fin 2) (Fin 2) ℂ)).det ^ 2))⁻¹ : ℝ≥0∞)
        * gl2DetSqDensity (B * ((g⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ))
        = gl2DetSqDensity B := fun B => by
    rw [gl2DetSqDensity_def, gl2DetSqDensity_def, Matrix.det_mul, Complex.normSq_mul, mul_pow]
    exact gl2_detSq_factor_mul' (gl2_val_det_mul_inv_det g) B.det
  exact gl2DetSqMatrixMeasure_map_eq hφ hψ hinv (gl2_jacobian_const_ne_top g)
    (gl2MatrixLebesgue_map_mul_right hdet) hpt

private def gl2DetSqHaarModel : Measure (GL (Fin 2) ℂ) :=
  gl2DetSqMatrixMeasure.comap Units.val

private theorem gl2DetSqHaarModel_def :
    gl2DetSqHaarModel = gl2DetSqMatrixMeasure.comap Units.val := rfl

private theorem gl2DetSqHaarModel_apply {s : Set (GL (Fin 2) ℂ)} (hs : MeasurableSet s) :
    gl2DetSqHaarModel s = gl2DetSqMatrixMeasure (Units.val '' s) :=
  Measure.comap_apply _ (fun _ _ h => Units.ext h)
    (fun _ ht => gl2_measurableEmbedding_val.measurableSet_image.mpr ht) _ hs

private theorem gl2_val_image_preimage_mul_left (g : GL (Fin 2) ℂ) (s : Set (GL (Fin 2) ℂ)) :
    (Units.val : GL (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ) '' ((fun x => g * x) ⁻¹' s)
      = (fun A : Matrix (Fin 2) (Fin 2) ℂ => (g : Matrix (Fin 2) (Fin 2) ℂ) * A) ⁻¹'
          (Units.val '' s) := by
  ext A
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨g * h, hh, by rw [Units.val_mul]⟩
  · rintro ⟨k, hk, hval⟩
    refine ⟨g⁻¹ * k, ?_, ?_⟩
    · show g * (g⁻¹ * k) ∈ s
      rwa [← mul_assoc, mul_inv_cancel, one_mul]
    · show ((g⁻¹ * k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = A
      rw [Units.val_mul, hval, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        one_mul]

private theorem gl2_val_image_preimage_mul_right (g : GL (Fin 2) ℂ) (s : Set (GL (Fin 2) ℂ)) :
    (Units.val : GL (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ) '' ((fun x => x * g) ⁻¹' s)
      = (fun A : Matrix (Fin 2) (Fin 2) ℂ => A * (g : Matrix (Fin 2) (Fin 2) ℂ)) ⁻¹'
          (Units.val '' s) := by
  ext A
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h * g, hh, by rw [Units.val_mul]⟩
  · rintro ⟨k, hk, hval⟩
    refine ⟨k * g⁻¹, ?_, ?_⟩
    · show (k * g⁻¹) * g ∈ s
      rwa [mul_assoc, inv_mul_cancel, mul_one]
    · show ((k * g⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = A
      rw [Units.val_mul, hval, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        mul_one]

private theorem gl2DetSqHaarModel_map_mul_left (g : GL (Fin 2) ℂ) :
    gl2DetSqHaarModel.map (fun x => g * x) = gl2DetSqHaarModel := by
  ext s hs
  have hsval : MeasurableSet (Units.val '' s) :=
    gl2_measurableEmbedding_val.measurableSet_image.mpr hs
  have hmeasM : Measurable (fun A : Matrix (Fin 2) (Fin 2) ℂ =>
      (g : Matrix (Fin 2) (Fin 2) ℂ) * A) :=
    (continuous_const.matrix_mul continuous_id).measurable
  rw [Measure.map_apply (measurable_const_mul g) hs,
    gl2DetSqHaarModel_apply ((measurable_const_mul g) hs), gl2DetSqHaarModel_apply hs,
    gl2_val_image_preimage_mul_left g s,
    ← Measure.map_apply hmeasM hsval,
    gl2DetSqMatrixMeasure_map_mul_left g]

private theorem gl2DetSqHaarModel_map_mul_right (g : GL (Fin 2) ℂ) :
    gl2DetSqHaarModel.map (fun x => x * g) = gl2DetSqHaarModel := by
  ext s hs
  have hsval : MeasurableSet (Units.val '' s) :=
    gl2_measurableEmbedding_val.measurableSet_image.mpr hs
  have hmeasM : Measurable (fun A : Matrix (Fin 2) (Fin 2) ℂ =>
      A * (g : Matrix (Fin 2) (Fin 2) ℂ)) :=
    (continuous_id.matrix_mul continuous_const).measurable
  rw [Measure.map_apply (measurable_mul_const g) hs,
    gl2DetSqHaarModel_apply ((measurable_mul_const g) hs), gl2DetSqHaarModel_apply hs,
    gl2_val_image_preimage_mul_right g s,
    ← Measure.map_apply hmeasM hsval,
    gl2DetSqMatrixMeasure_map_mul_right g]

private scoped instance gl2DetSqHaarModel_isMulLeftInvariant :
    gl2DetSqHaarModel.IsMulLeftInvariant :=
  ⟨gl2DetSqHaarModel_map_mul_left⟩

private scoped instance gl2DetSqHaarModel_isMulRightInvariant :
    gl2DetSqHaarModel.IsMulRightInvariant :=
  ⟨gl2DetSqHaarModel_map_mul_right⟩

private theorem gl2DetSqMatrixMeasure_pos_of_isOpen {V : Set (Matrix (Fin 2) (Fin 2) ℂ)}
    (hV : IsOpen V) (hne : V.Nonempty) : 0 < gl2DetSqMatrixMeasure V := by
  rw [pos_iff_ne_zero]
  intro h0
  rw [gl2DetSqMatrixMeasure_apply hV.measurableSet] at h0
  have hae : ∀ᵐ A ∂gl2MatrixLebesgue, A ∈ V → gl2DetSqDensity A = 0 :=
    (setLIntegral_eq_zero_iff hV.measurableSet gl2_measurable_detSqDensity).mp h0
  have hVzero : gl2MatrixLebesgue V = 0 := by
    have h2 : {A : Matrix (Fin 2) (Fin 2) ℂ | ¬ (A ∈ V → gl2DetSqDensity A = 0)} = V := by
      ext A
      simp [gl2DetSqDensity_ne_zero A]
    have h3 := ae_iff.mp hae
    rwa [h2] at h3
  exact absurd hVzero (hV.measure_pos gl2MatrixLebesgue hne).ne'

private theorem gl2DetSqHaarModel_pos_of_isOpen {U : Set (GL (Fin 2) ℂ)} (hU : IsOpen U)
    (hne : U.Nonempty) : 0 < gl2DetSqHaarModel U := by
  rw [gl2DetSqHaarModel_apply hU.measurableSet]
  exact gl2DetSqMatrixMeasure_pos_of_isOpen (gl2_isOpenEmbedding_val.isOpenMap U hU)
    (hne.image _)

private scoped instance gl2DetSqHaarModel_isOpenPosMeasure : gl2DetSqHaarModel.IsOpenPosMeasure :=
  ⟨fun _ hU hne => (gl2DetSqHaarModel_pos_of_isOpen hU hne).ne'⟩

private theorem gl2DetSqMatrixMeasure_lt_top_of_isCompact {K : Set (Matrix (Fin 2) (Fin 2) ℂ)}
    (hK : IsCompact K) (hKunit : ∀ A ∈ K, IsUnit A) : gl2DetSqMatrixMeasure K < ∞ := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · rw [gl2DetSqMatrixMeasure_def]
    simp
  obtain ⟨A₀, hA₀K, hA₀min⟩ := hK.exists_isMinOn hne
    ((Complex.continuous_normSq.comp continuous_id.matrix_det).continuousOn)
  have hA₀det : A₀.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp (hKunit A₀ hA₀K)).ne_zero
  have hε : (0 : ℝ) < Complex.normSq A₀.det := Complex.normSq_pos.mpr hA₀det
  have hbound : ∀ A ∈ K, gl2DetSqDensity A ≤ (ENNReal.ofReal (Complex.normSq A₀.det ^ 2))⁻¹ := by
    intro A hA
    rw [gl2DetSqDensity_def]
    refine ENNReal.inv_le_inv' (ENNReal.ofReal_le_ofReal ?_)
    have h1 : Complex.normSq A₀.det ≤ Complex.normSq A.det := hA₀min hA
    exact pow_le_pow_left₀ (Complex.normSq_nonneg _) h1 2
  calc gl2DetSqMatrixMeasure K
      = ∫⁻ A in K, gl2DetSqDensity A ∂gl2MatrixLebesgue :=
        gl2DetSqMatrixMeasure_apply hK.measurableSet
    _ ≤ ∫⁻ _ in K, (ENNReal.ofReal (Complex.normSq A₀.det ^ 2))⁻¹ ∂gl2MatrixLebesgue :=
        setLIntegral_mono measurable_const hbound
    _ = (ENNReal.ofReal (Complex.normSq A₀.det ^ 2))⁻¹ * gl2MatrixLebesgue K := setLIntegral_const _ _
    _ < ∞ := ENNReal.mul_lt_top
        (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr (pow_pos hε 2)))
        hK.measure_lt_top

private theorem gl2DetSqHaarModel_lt_top_of_isCompact {K : Set (GL (Fin 2) ℂ)} (hK : IsCompact K) :
    gl2DetSqHaarModel K < ∞ := by
  have hKM : IsCompact ((Units.val : GL (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ) '' K) :=
    hK.image Units.continuous_val
  have hKunit : ∀ A ∈ (Units.val : GL (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ) '' K, IsUnit A := by
    rintro A ⟨u, _, rfl⟩
    exact u.isUnit
  rw [gl2DetSqHaarModel_apply hK.isClosed.measurableSet]
  exact gl2DetSqMatrixMeasure_lt_top_of_isCompact hKM hKunit

private scoped instance gl2DetSqHaarModel_isFiniteMeasureOnCompacts :
    IsFiniteMeasureOnCompacts gl2DetSqHaarModel :=
  ⟨fun _ hK => gl2DetSqHaarModel_lt_top_of_isCompact hK⟩

private theorem gl2DetSqHaarModel_isHaarMeasure : gl2DetSqHaarModel.IsHaarMeasure := by
  constructor

private scoped instance gl2DetSqHaarModel_isHaarMeasure' : gl2DetSqHaarModel.IsHaarMeasure :=
  gl2DetSqHaarModel_isHaarMeasure

private abbrev glCommittedMeasurableSpace : MeasurableSpace (GL (Fin 2) ℂ) := Units.instMeasurableSpace

private theorem glCommittedMeasurableSpace_eq_borel :
    glCommittedMeasurableSpace = borel (GL (Fin 2) ℂ) :=
  BorelSpace.measurable_eq

private theorem gl2DetSqHaarModel_eq_map_entryModel :
    gl2DetSqHaarModel = Measure.map
        (fun A : Fin 2 → Fin 2 → ℂ =>
          if h : (Matrix.of A).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of A) h
          else 1)
        ((volume.restrict {A : Fin 2 → Fin 2 → ℂ | (Matrix.of A).det ≠ 0}).withDensity
          fun A => ENNReal.ofReal ((Complex.normSq (Matrix.of A).det ^ 2)⁻¹)) := by
  have hof : Measurable (fun A : Fin 2 → Fin 2 → ℂ => (Matrix.of A : Matrix (Fin 2) (Fin 2) ℂ)) :=
    fun _ h => h
  have hdetm : Measurable fun A : Fin 2 → Fin 2 → ℂ => (Matrix.of A).det := gl2_measurable_det.comp hof
  have hS : MeasurableSet {A : Fin 2 → Fin 2 → ℂ | (Matrix.of A).det ≠ 0} :=
    hdetm (measurableSet_singleton (0 : ℂ)).compl
  have hφ : Measurable (fun A : Fin 2 → Fin 2 → ℂ =>
      if h : (Matrix.of A).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of A) h
      else 1) := by
    rw [← gl2_measurableEmbedding_val.measurable_comp_iff]
    have h : (Units.val ∘ fun A : Fin 2 → Fin 2 → ℂ =>
        if h : (Matrix.of A).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of A) h
        else 1) = fun A => if (Matrix.of A).det ≠ 0 then Matrix.of A else 1 := by
      funext A
      simp only [Function.comp_apply]
      split_ifs with h <;> rfl
    rw [h]
    exact Measurable.ite hS hof measurable_const
  ext s hs
  have himg : MeasurableSet ((Units.val : GL (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ) '' s) :=
    gl2_measurableEmbedding_val.measurableSet_image.mpr hs
  rw [gl2DetSqHaarModel_apply hs, gl2DetSqMatrixMeasure_apply himg, Measure.map_apply hφ hs,
    withDensity_apply _ (hφ hs), Measure.restrict_restrict (hφ hs)]
  have hset : (fun A : Fin 2 → Fin 2 → ℂ => (Matrix.of A : Matrix (Fin 2) (Fin 2) ℂ)) ⁻¹'
      ((Units.val : GL (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ) '' s) =
      (fun A : Fin 2 → Fin 2 → ℂ =>
        if h : (Matrix.of A).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of A) h
        else 1) ⁻¹' s ∩ {A : Fin 2 → Fin 2 → ℂ | (Matrix.of A).det ≠ 0} := by
    ext A
    constructor
    · rintro ⟨g, hg, hgA⟩
      have hgA' : (g : Matrix (Fin 2) (Fin 2) ℂ) = Matrix.of A := hgA
      have hdet : (Matrix.of A).det ≠ 0 := by
        rw [← hgA']
        exact gl2_val_det_ne_zero g
      refine ⟨?_, hdet⟩
      show (if h : (Matrix.of A).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of A) h
        else 1) ∈ s
      rw [dif_pos hdet, show Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of A) hdet = g from
        Units.ext hgA'.symm]
      exact hg
    · rintro ⟨hA, hdet⟩
      have hdet' : (Matrix.of A).det ≠ 0 := hdet
      refine ⟨(if h : (Matrix.of A).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of A) h
        else 1), hA, ?_⟩
      rw [dif_pos hdet']
      rfl
  change ∫⁻ A in (fun A : Fin 2 → Fin 2 → ℂ => (Matrix.of A : Matrix (Fin 2) (Fin 2) ℂ)) ⁻¹'
      ((Units.val : GL (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ) '' s),
      gl2DetSqDensity (Matrix.of A) ∂(volume : Measure (Fin 2 → Fin 2 → ℂ)) = _
  rw [hset]
  refine setLIntegral_congr_fun ((hφ hs).inter hS) fun A hA => ?_
  have hdet : (Matrix.of A).det ≠ 0 := hA.2
  simp only [gl2DetSqDensity_def]
  rw [ENNReal.ofReal_inv_of_pos (pow_pos (Complex.normSq_pos.mpr hdet) 2)]

private theorem exists_pos_smul_map_entryModel (μ : Measure (GL (Fin 2) ℂ)) [μ.IsHaarMeasure] :
    ∃ c : NNReal, 0 < c ∧
      μ = c • Measure.map
        (fun A : Fin 2 → Fin 2 → ℂ =>
          if h : (Matrix.of A).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of A) h
          else 1)
        ((volume.restrict {A : Fin 2 → Fin 2 → ℂ | (Matrix.of A).det ≠ 0}).withDensity
          fun A => ENNReal.ofReal ((Complex.normSq (Matrix.of A).det ^ 2)⁻¹)) := by
  rw [← gl2DetSqHaarModel_eq_map_entryModel]
  exact ⟨μ.haarScalarFactor gl2DetSqHaarModel, Measure.haarScalarFactor_pos_of_isHaarMeasure _ _,
    Measure.isMulLeftInvariant_eq_smul _ _⟩

end
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Twisted_exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv.TwistedHaar P2MW.S_AutomorphicForm_GL2Twisted_exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv.TwistedHaar.MatrixBorel P2MW.S_AutomorphicForm_GL2Twisted_exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv.TwistedHaar.GL2ComplexFurniture"

end TwistedHaar.GL2ComplexEntryModel
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Twisted_exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv.TwistedHaar P2MW.S_AutomorphicForm_GL2Twisted_exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv.TwistedHaar.MatrixBorel P2MW.S_AutomorphicForm_GL2Twisted_exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv.TwistedHaar.GL2ComplexFurniture P2MW.S_AutomorphicForm_GL2Twisted_exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv.TwistedHaar.GL2ComplexEntryModel"
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Twisted_exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv.TwistedHaar P2MW.S_AutomorphicForm_GL2Twisted_exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv.TwistedHaar.MatrixBorel P2MW.S_AutomorphicForm_GL2Twisted_exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv.TwistedHaar.GL2ComplexFurniture"

open scoped TensorProduct TensorProduct.RightActions

noncomputable section

namespace TwistedHaar
namespace RidTransport

open MeasureTheory

private def ridE : ℂ ⊗[ℝ] ℝ ≃+* ℂ :=
  @AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
    (Algebra.TensorProduct.rid ℝ ℝ ℂ)

private theorem ridE_tmul (z : ℂ) (a : ℝ) : ridE (z ⊗ₜ[ℝ] a) = a • z := rfl

private def ridL : (ℂ ⊗[ℝ] ℝ) ≃ₗ[ℝ] ℂ :=
  { ridE with
    map_smul' := fun r x => by
      show ridE (r • x) = r • ridE x
      rw [TensorProduct.RightActions.smul_def]
      induction x using TensorProduct.induction_on with
      | zero => simp only [map_zero, smul_zero]
      | tmul z a =>
          rw [TensorProduct.comm_tmul, TensorProduct.smul_tmul', TensorProduct.comm_symm_tmul, ridE_tmul, ridE_tmul,
            smul_eq_mul, mul_smul]
      | add x y hx hy => simp only [map_add, smul_add, hx, hy] }

private theorem ridL_apply (x : ℂ ⊗[ℝ] ℝ) : ridL x = ridE x := rfl

private theorem ridL_symm_apply (z : ℂ) : ridL.symm z = ridE.symm z := rfl

private theorem continuous_ridE : Continuous ridE := by
  have h : Continuous ridL.toLinearMap := IsModuleTopology.continuous_of_linearMap ridL.toLinearMap
  exact h

private theorem continuous_ridE_symm : Continuous ridE.symm := by
  haveI : IsModuleTopology ℝ ℂ := isModuleTopologyOfFiniteDimensional
  haveI : ContinuousAdd (ℂ ⊗[ℝ] ℝ) := IsModuleTopology.toContinuousAdd ℝ (ℂ ⊗[ℝ] ℝ)
  have h : Continuous ridL.symm.toLinearMap :=
    IsModuleTopology.continuous_of_linearMap ridL.symm.toLinearMap
  exact h

private theorem continuous_glMap {R S : Type*} [CommRing R] [CommRing S] [TopologicalSpace R]
    [TopologicalSpace S] {f : R →+* S} (hf : Continuous f) :
    Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) f) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Units.continuous_val.matrix_map hf
  · exact Units.continuous_coe_inv.matrix_map hf

private def glRid : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) ≃* GL (Fin 2) ℂ where
  toFun := Matrix.GeneralLinearGroup.map ridE.toRingHom
  invFun := Matrix.GeneralLinearGroup.map ridE.symm.toRingHom
  left_inv g := by
    ext i j
    simp [Matrix.GeneralLinearGroup.map_apply]
  right_inv g := by
    ext i j
    simp [Matrix.GeneralLinearGroup.map_apply]
  map_mul' x y := map_mul _ x y

private theorem glRid_apply (g : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) :
    glRid g = Matrix.GeneralLinearGroup.map ridE.toRingHom g := rfl

private theorem glRid_symm_apply (g : GL (Fin 2) ℂ) :
    glRid.symm g = Matrix.GeneralLinearGroup.map ridE.symm.toRingHom g := rfl

private theorem continuous_glRid : Continuous glRid :=
  continuous_glMap continuous_ridE

private theorem continuous_glRid_symm : Continuous glRid.symm :=
  continuous_glMap continuous_ridE_symm

private theorem isHaarMeasure_map_glRid
    (μ : @Measure (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (AutomorphicForm.glBorelOf (ℂ ⊗[ℝ] ℝ)))
    (hμ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.glBorelOf (ℂ ⊗[ℝ] ℝ)) μ)
    [MeasurableSpace (GL (Fin 2) ℂ)] [BorelSpace (GL (Fin 2) ℂ)] :
    Measure.IsHaarMeasure (@Measure.map _ _ (AutomorphicForm.glBorelOf (ℂ ⊗[ℝ] ℝ)) _ glRid μ) := by
  letI : MeasurableSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := AutomorphicForm.glBorelOf _
  haveI : BorelSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := AutomorphicForm.borelSpace_glBorelOf _
  haveI : IsTopologicalRing (ℂ ⊗[ℝ] ℝ) := AutomorphicForm.isTopologicalRing_tensor ℝ ℂ ℝ
  haveI : IsTopologicalGroup (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) :=
    AutomorphicForm.isTopologicalGroup_tensorGL ℝ ℂ ℝ
  haveI := hμ
  exact MulEquiv.isHaarMeasure_map μ glRid continuous_glRid continuous_glRid_symm

open TwistedHaar.GL2ComplexEntryModel in
private theorem measurable_entryChart :
    Measurable (fun A : Fin 2 → Fin 2 → ℂ =>
      if h : (Matrix.of A).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of A) h else 1) := by
  have hof : Measurable (fun A : Fin 2 → Fin 2 → ℂ => (Matrix.of A : Matrix (Fin 2) (Fin 2) ℂ)) :=
    fun _ h => h
  have hdetm : Measurable fun A : Fin 2 → Fin 2 → ℂ => (Matrix.of A).det := gl2_measurable_det.comp hof
  have hS : MeasurableSet {A : Fin 2 → Fin 2 → ℂ | (Matrix.of A).det ≠ 0} :=
    hdetm (measurableSet_singleton (0 : ℂ)).compl
  rw [← gl2_measurableEmbedding_val.measurable_comp_iff]
  have h : (Units.val ∘ fun A : Fin 2 → Fin 2 → ℂ =>
      if h : (Matrix.of A).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of A) h
      else 1) = fun A => if (Matrix.of A).det ≠ 0 then Matrix.of A else 1 := by
    funext A
    simp only [Function.comp_apply]
    split_ifs with h <;> rfl
  rw [h]
  exact Measurable.ite hS hof measurable_const

private theorem exists_pos_smul_map_ridEntryModel
    (μ : @Measure (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (AutomorphicForm.glBorelOf (ℂ ⊗[ℝ] ℝ)))
    (hμ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.glBorelOf (ℂ ⊗[ℝ] ℝ)) μ) :
    ∃ c : NNReal, 0 < c ∧
      μ = c • @Measure.map _ _ _ (AutomorphicForm.glBorelOf (ℂ ⊗[ℝ] ℝ))
        (fun A : Fin 2 → Fin 2 → ℂ =>
          if h : (Matrix.of A).det ≠ 0 then
            Matrix.GeneralLinearGroup.map
              (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                (Algebra.TensorProduct.rid ℝ ℝ ℂ)).symm.toRingHom
              (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of A) h)
          else 1)
        ((volume.restrict {A : Fin 2 → Fin 2 → ℂ | (Matrix.of A).det ≠ 0}).withDensity
          fun A => ENNReal.ofReal ((Complex.normSq (Matrix.of A).det ^ 2)⁻¹)) := by
  letI : MeasurableSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := AutomorphicForm.glBorelOf _
  haveI : BorelSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := AutomorphicForm.borelSpace_glBorelOf _
  haveI : IsTopologicalRing (ℂ ⊗[ℝ] ℝ) := AutomorphicForm.isTopologicalRing_tensor ℝ ℂ ℝ
  haveI : IsTopologicalGroup (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) :=
    AutomorphicForm.isTopologicalGroup_tensorGL ℝ ℂ ℝ
  haveI := hμ
  haveI : (Measure.map glRid μ).IsHaarMeasure :=
    MulEquiv.isHaarMeasure_map μ glRid continuous_glRid continuous_glRid_symm
  obtain ⟨c, hc, hν⟩ :=
    TwistedHaar.GL2ComplexEntryModel.exists_pos_smul_map_entryModel (Measure.map glRid μ)
  refine ⟨c, hc, ?_⟩
  have hms : Measurable ⇑glRid.symm := continuous_glRid_symm.measurable
  have hm : Measurable ⇑glRid := continuous_glRid.measurable
  have h1 : μ = (Measure.map glRid μ).map glRid.symm := by
    rw [Measure.map_map hms hm]
    have hid : (⇑glRid.symm ∘ ⇑glRid) = id := by
      funext g
      exact glRid.symm_apply_apply g
    rw [hid, Measure.map_id]
  have hcomp : (⇑glRid.symm ∘ fun A : Fin 2 → Fin 2 → ℂ =>
      if h : (Matrix.of A).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of A) h else 1)
      = fun A : Fin 2 → Fin 2 → ℂ =>
          if h : (Matrix.of A).det ≠ 0 then
            Matrix.GeneralLinearGroup.map
              (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                (Algebra.TensorProduct.rid ℝ ℝ ℂ)).symm.toRingHom
              (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of A) h)
          else 1 := by
    funext A
    simp only [Function.comp_apply]
    by_cases h : (Matrix.of A).det ≠ 0
    · simp only [dif_pos h]
      rfl
    · simp only [dif_neg h, map_one]
  rw [h1, hν, Measure.map_smul, Measure.map_map hms measurable_entryChart, hcomp]

end TwistedHaar.RidTransport
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Twisted_exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv.TwistedHaar P2MW.S_AutomorphicForm_GL2Twisted_exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv.TwistedHaar.MatrixBorel P2MW.S_AutomorphicForm_GL2Twisted_exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv.TwistedHaar.GL2ComplexFurniture P2MW.S_AutomorphicForm_GL2Twisted_exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv.TwistedHaar.GL2ComplexEntryModel"
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Twisted_exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv.TwistedHaar P2MW.S_AutomorphicForm_GL2Twisted_exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv.TwistedHaar.MatrixBorel P2MW.S_AutomorphicForm_GL2Twisted_exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv.TwistedHaar.GL2ComplexFurniture P2MW.S_AutomorphicForm_GL2Twisted_exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv.TwistedHaar.GL2ComplexEntryModel"

end
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Twisted_exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv.TwistedHaar P2MW.S_AutomorphicForm_GL2Twisted_exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv.TwistedHaar.MatrixBorel P2MW.S_AutomorphicForm_GL2Twisted_exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv.TwistedHaar.GL2ComplexFurniture P2MW.S_AutomorphicForm_GL2Twisted_exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv.TwistedHaar.GL2ComplexEntryModel"

open MeasureTheory
open scoped TensorProduct TensorProduct.RightActions
open AutomorphicForm in

theorem solution
    (μ : @Measure (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ)))
    (hμ : @Measure.IsHaarMeasure _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) μ) :
    ∃ c : NNReal, 0 < c ∧
      μ = c • @Measure.map _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ))
        (fun A : Fin 2 → Fin 2 → ℂ =>
          if h : (Matrix.of A).det ≠ 0 then
            Matrix.GeneralLinearGroup.map
              (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                (Algebra.TensorProduct.rid ℝ ℝ ℂ)).symm.toRingHom
              (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of A) h)
          else 1)
        ((volume.restrict {A : Fin 2 → Fin 2 → ℂ | (Matrix.of A).det ≠ 0}).withDensity
          fun A => ENNReal.ofReal ((Complex.normSq (Matrix.of A).det ^ 2)⁻¹)) := by
  obtain ⟨c, hc, h⟩ := TwistedHaar.RidTransport.exists_pos_smul_map_ridEntryModel μ hμ
  exact ⟨c, hc, h⟩

end S_AutomorphicForm_GL2Twisted_exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv
end P2MW
export P2MW.S_AutomorphicForm_GL2Twisted_exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv (solution)
