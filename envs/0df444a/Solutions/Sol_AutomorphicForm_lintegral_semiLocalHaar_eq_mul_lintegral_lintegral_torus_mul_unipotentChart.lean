-- Prove2me | solution 1 for AutomorphicForm.lintegral_semiLocalHaar_eq_mul_lintegral_lintegral_torus_mul_unipotentChart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/43648b82-e048-5895-8eb3-96b8455ae7d6

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_NumberField_AdicCompletion_lintegral_tensor_comp_splitTorusProductChart_mul_norm_algebraNorm_eq_lintegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_lintegral_semiLocalHaar_eq_mul_lintegral_lintegral_torus_mul_unipotentChart
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain MeasureTheory Set Function
open scoped ENNReal NNReal TensorProduct TensorProduct.RightActions

noncomputable section

namespace KcSemiLocalTorusChart

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {v : HeightOneSpectrum (𝓞 K)}

local notation "F" => v.adicCompletion K
local notation "E" => L ⊗[K] v.adicCompletion K
local notation "Q" => (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K)
local notation "P" => Fin 4 → L ⊗[K] v.adicCompletion K
local notation "G" => GL (Fin 2) (L ⊗[K] v.adicCompletion K)
local notation "GF" => GL (Fin 2) (v.adicCompletion K)

attribute [local instance 9999] Algebra.toModule

theorem isTopologicalRing_E : IsTopologicalRing E := AutomorphicForm.isTopologicalRing_tensor K L F
theorem t2Space_E : T2Space E := AutomorphicForm.t2Space_tensor K L F
theorem locallyCompactSpace_E : LocallyCompactSpace E := AutomorphicForm.locallyCompactSpace_tensor K L F
theorem continuousSMul_E : ContinuousSMul F E := IsModuleTopology.toContinuousSMul F E
theorem isScalarTower_FEE : IsScalarTower F E E :=
  @IsScalarTower.right F E _ _ (TensorProduct.RightActions.instAlgebra_definitions K (v.adicCompletion K) L)
theorem smulCommClass_FEE : SMulCommClass F E E :=
  @Algebra.to_smulCommClass F E _ _ (TensorProduct.RightActions.instAlgebra_definitions K (v.adicCompletion K) L)
theorem finite_KL : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L

attribute [local instance] isTopologicalRing_E t2Space_E locallyCompactSpace_E continuousSMul_E
  isScalarTower_FEE smulCommClass_FEE finite_KL

def triv : E ≃L[F] (Fin (Module.finrank F E) → F) :=
  let e : E ≃ₗ[F] (Fin (Module.finrank F E) → F) := (Module.finBasis F E).equivFun
  { e with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }

theorem secondCountableTopology_E : SecondCountableTopology E :=
  (triv (K := K) (L := L) (v := v)).toHomeomorph.secondCountableTopology

attribute [local instance] secondCountableTopology_E

theorem continuous_algebraNorm : Continuous (Algebra.norm F : E → F) := by
  classical
  let b := Module.finBasis F E
  have h1 : Continuous fun x : E => Algebra.leftMulMatrix b x :=
    IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix b).toLinearMap
  have h2 : (Algebra.norm F : E → F) = fun x => (Algebra.leftMulMatrix b x).det := by
    funext x; exact Algebra.norm_eq_matrix_det b x
  rw [h2]
  exact h1.matrix_det

theorem isUnit_iff_norm_ne_zero (x : E) : IsUnit x ↔ Algebra.norm F x ≠ 0 := by
  constructor
  · intro hx h0
    obtain ⟨u, rfl⟩ := hx
    have h1 : Algebra.norm F ((u : E)) * Algebra.norm F ((u⁻¹ : Eˣ) : E) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  · intro h
    have hdet : LinearMap.det (Algebra.lmul F E x) ≠ 0 := by
      rwa [← Algebra.norm_apply]
    have hbij : Function.Bijective (Algebra.lmul F E x) := by
      have hu : IsUnit (Algebra.lmul F E x) :=
        (LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)
      exact (Module.End.isUnit_iff _).1 hu
    obtain ⟨y, hy⟩ := hbij.2 1
    have hy' : x * y = 1 := by
      rw [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply'] at hy; exact hy
    exact IsUnit.of_mul_eq_one y hy'

theorem isClosed_nonunits : IsClosed {x : E | ¬ IsUnit x} := by
  have : {x : E | ¬ IsUnit x} = (Algebra.norm F : E → F) ⁻¹' {0} := by
    ext x
    simp only [mem_setOf_eq, mem_preimage, mem_singleton_iff, isUnit_iff_norm_ne_zero, not_not]
  rw [this]
  exact isClosed_singleton.preimage continuous_algebraNorm

theorem isOpen_units : IsOpen {x : E | IsUnit x} := by
  have : {x : E | IsUnit x} = {x : E | ¬ IsUnit x}ᶜ := by ext; simp
  rw [this]; exact isClosed_nonunits.isOpen_compl

section Inverse

open scoped Classical in

def adjLin : Matrix (Fin (Module.finrank F E)) (Fin (Module.finrank F E)) F →ₗ[F] E :=
  (LinearMap.applyₗ (1 : E)) ∘ₗ
    (Matrix.toLin (Module.finBasis F E) (Module.finBasis F E)).toLinearMap

open scoped Classical in

def adjE (y : E) : E := adjLin (K := K) (L := L) (v := v) (Algebra.leftMulMatrix (Module.finBasis F E) y).adjugate

theorem adjE_eq (y : E) :
    adjE y = Matrix.toLin (Module.finBasis F E) (Module.finBasis F E)
      (Algebra.leftMulMatrix (Module.finBasis F E) y).adjugate 1 := rfl

theorem mul_adjE (y : E) : y * adjE y = algebraMap F E (Algebra.norm F y) := by
  classical
  set b := Module.finBasis F E with hb
  have h1 : Matrix.toLin b b (Algebra.leftMulMatrix b y) = Algebra.lmul F E y := by
    rw [Algebra.leftMulMatrix_apply, Matrix.toLin_toMatrix]
  have h2 : Matrix.toLin b b (Algebra.leftMulMatrix b y * (Algebra.leftMulMatrix b y).adjugate) =
      (Algebra.lmul F E y) ∘ₗ Matrix.toLin b b (Algebra.leftMulMatrix b y).adjugate := by
    rw [Matrix.toLin_mul b b b, h1]
  have h3 : y * adjE y = Matrix.toLin b b
      (Algebra.leftMulMatrix b y * (Algebra.leftMulMatrix b y).adjugate) 1 := by
    rw [h2, LinearMap.comp_apply, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', adjE_eq]
  rw [h3, Matrix.mul_adjugate, map_smul, Matrix.toLin_one, LinearMap.smul_apply, LinearMap.id_apply,
    Algebra.norm_eq_matrix_det b, Algebra.algebraMap_eq_smul_one]

theorem continuous_adjE : Continuous (adjE : E → E) := by
  classical
  have h1 : Continuous fun y : E => Algebra.leftMulMatrix (Module.finBasis F E) y :=
    IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix (Module.finBasis F E)).toLinearMap
  haveI : IsModuleTopology F (Matrix (Fin (Module.finrank F E)) (Fin (Module.finrank F E)) F) :=
    inferInstanceAs (IsModuleTopology F (Fin (Module.finrank F E) → Fin (Module.finrank F E) → F))
  have h2 : Continuous (adjLin (K := K) (L := L) (v := v)) := IsModuleTopology.continuous_of_linearMap _
  exact h2.comp h1.matrix_adjugate

theorem ringInverse_eq {y : E} (hy : IsUnit y) :
    Ring.inverse y = (Algebra.norm F y)⁻¹ • adjE y := by
  have hN : Algebra.norm F y ≠ 0 := (isUnit_iff_norm_ne_zero y).1 hy
  have hmul := mul_adjE (K := K) (L := L) (v := v) y
  have h1 : Ring.inverse y * (y * adjE y) = adjE y := by
    rw [← mul_assoc, Ring.inverse_mul_cancel _ hy, one_mul]
  rw [hmul, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one] at h1
  rw [← h1, smul_smul, inv_mul_cancel₀ hN, one_smul]

theorem continuous_ringInverse_comp {X : Type*} [TopologicalSpace X] {f : X → E}
    (hf : Continuous f) (hu : ∀ x, IsUnit (f x)) :
    Continuous fun x => Ring.inverse (f x) := by
  have : (fun x => Ring.inverse (f x)) = fun x => (Algebra.norm F (f x))⁻¹ • adjE (f x) := by
    funext x; exact ringInverse_eq (hu x)
  rw [this]
  refine Continuous.fun_smul ?_ (continuous_adjE.comp hf)
  refine Continuous.inv₀ (continuous_algebraNorm.comp hf) fun x => ?_
  exact (isUnit_iff_norm_ne_zero _).1 (hu x)

end Inverse

theorem t2Space_GL : T2Space G := AutomorphicForm.t2Space_tensorGL K L F

theorem secondCountableTopology_GL : SecondCountableTopology G := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) E) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → E))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) E)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem locallyCompactSpace_GL : LocallyCompactSpace G := AutomorphicForm.locallyCompactSpace_tensorGL K L F

theorem isTopologicalGroup_GL : IsTopologicalGroup G := AutomorphicForm.isTopologicalGroup_tensorGL K L F

@[reducible] def measurableSpace_GL : MeasurableSpace G := AutomorphicForm.glBorelOf E

attribute [local instance] t2Space_GL secondCountableTopology_GL locallyCompactSpace_GL
  isTopologicalGroup_GL measurableSpace_GL

theorem borelSpace_GL : BorelSpace G := AutomorphicForm.borelSpace_glBorelOf E

private theorem _root_.KcSemiLocalTorusChart.isHaarMeasure_semiLocalHaar : (AutomorphicForm.semiLocalHaar K L v).IsHaarMeasure :=
  AutomorphicForm.isHaarMeasure_semiLocalHaar K L v

p2m_export "KcSemiLocalTorusChart" "isHaarMeasure_semiLocalHaar"
attribute [local instance] borelSpace_GL isHaarMeasure_semiLocalHaar

theorem measurableMul_GL : MeasurableMul₂ G := inferInstance
theorem measurableInv_GL : MeasurableInv G := inferInstance

attribute [local instance] measurableMul_GL measurableInv_GL

theorem continuous_GL_of {X : Type*} [TopologicalSpace X] {f : X → G}
    (hval : ∀ i j, Continuous fun x => ((f x : G) : Matrix (Fin 2) (Fin 2) E) i j)
    (hinv : ∀ i j, Continuous fun x => (((f x)⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) i j) :
    Continuous f := by
  rw [Units.continuous_iff]
  exact ⟨continuous_matrix fun i j => hval i j, continuous_matrix fun i j => hinv i j⟩

section Charts

open scoped Classical

def mat (x : P) : Matrix (Fin 2) (Fin 2) E := !![x 0, x 1; x 2, x 3]

theorem det_mat (x : P) : (mat x).det = x 0 * x 3 - x 1 * x 2 := by
  simp [mat, Matrix.det_fin_two_of]

theorem continuous_mat : Continuous (mat : P → Matrix (Fin 2) (Fin 2) E) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j
  · exact continuous_apply 0
  · exact continuous_apply 1
  · exact continuous_apply 2
  · exact continuous_apply 3

theorem continuous_det_mat : Continuous fun x : P => (mat x).det := continuous_mat.matrix_det

def good : Set P := {x | IsUnit (mat x).det}

theorem isOpen_good : IsOpen (good : Set P) :=
  (isOpen_units (K := K) (L := L) (v := v)).preimage continuous_det_mat

def chart (x : P) : G :=
  if h : IsUnit (mat x).det then Matrix.GeneralLinearGroup.mk'' (mat x) h else 1

theorem chart_of_mem {x : P} (h : IsUnit (mat x).det) :
    chart x = Matrix.GeneralLinearGroup.mk'' (mat x) h := by
  simp [chart, h]

theorem coe_chart_of_mem {x : P} (h : IsUnit (mat x).det) :
    ((chart x : G) : Matrix (Fin 2) (Fin 2) E) = mat x := by
  rw [chart_of_mem h]; rfl

theorem coe_chart_inv_of_mem {x : P} (h : IsUnit (mat x).det) :
    (((chart x)⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) = Ring.inverse (mat x).det • (mat x).adjugate := by
  rw [Matrix.coe_units_inv, coe_chart_of_mem h, Matrix.inv_def]

theorem continuous_chart_restrict : Continuous ((good : Set P).domRestrict (chart : P → G)) := by
  have hent : ∀ i j, Continuous fun x : (good : Set P) => mat (x : P) i j := fun i j =>
    (continuous_mat.matrix_elem i j).comp continuous_subtype_val
  refine continuous_GL_of (fun i j => ?_) (fun i j => ?_)
  · have : (fun x : (good : Set P) => (((good : Set P).domRestrict chart x : G) : Matrix (Fin 2) (Fin 2) E) i j)
        = fun x : (good : Set P) => mat (x : P) i j := by
      funext x; rw [Set.domRestrict_apply, coe_chart_of_mem x.2]
    rw [this]; exact hent i j
  · have : (fun x : (good : Set P) =>
        ((((good : Set P).domRestrict chart x)⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) i j)
        = fun x : (good : Set P) => Ring.inverse (mat (x : P)).det * (mat (x : P)).adjugate i j := by
      funext x
      rw [Set.domRestrict_apply, coe_chart_inv_of_mem x.2, Matrix.smul_apply, smul_eq_mul]
    rw [this]
    have hdet : Continuous fun x : (good : Set P) => (mat (x : P)).det :=
      continuous_det_mat.comp continuous_subtype_val
    have hri : Continuous fun x : (good : Set P) => Ring.inverse (mat (x : P)).det :=
      continuous_ringInverse_comp hdet fun x => x.2
    refine hri.mul ?_
    have hadj : Continuous fun x : (good : Set P) => (mat (x : P)).adjugate :=
      (continuous_mat.comp continuous_subtype_val).matrix_adjugate
    exact hadj.matrix_elem i j

section Meas

variable [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]

theorem borelSpace_P : BorelSpace P := inferInstance
theorem borelSpace_Q : BorelSpace Q := inferInstance

theorem measurableSet_good : MeasurableSet (good : Set P) := isOpen_good.measurableSet

theorem measurable_chart : Measurable (chart : P → G) := by
  refine measurable_of_restrict_of_restrict_compl measurableSet_good ?_ ?_
  · exact continuous_chart_restrict.measurable
  · have : (goodᶜ : Set P).domRestrict (chart : P → G) = fun _ => 1 := by
      funext x
      have hx : ¬ IsUnit (mat (x : P)).det := x.2
      simp [Set.domRestrict_apply, chart, hx]
    rw [this]; exact measurable_const

end Meas

def tm (p : Q) : Matrix (Fin 2) (Fin 2) E := !![p.1, 0; 0, p.2]

theorem det_tm (p : Q) : (tm p).det = p.1 * p.2 := by
  simp [tm, Matrix.det_fin_two_of]

def ι4 (p : Q) : P := ![p.1, 0, 0, p.2]

theorem mat_ι4 (p : Q) : mat (ι4 p) = tm p := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem continuous_ι4 : Continuous (ι4 : Q → P) := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact continuous_fst
  · exact continuous_const
  · exact continuous_const
  · exact continuous_snd

def uGL (p : Q) : G := chart (ι4 p)

theorem uGL_of_mem {p : Q} (h : IsUnit (tm p).det) : uGL p = Matrix.GeneralLinearGroup.mk'' (tm p) h := by
  have h' : IsUnit (mat (ι4 p)).det := by rw [mat_ι4]; exact h
  apply Units.ext
  rw [uGL, coe_chart_of_mem h']
  exact mat_ι4 p

theorem coe_uGL_of_mem {p : Q} (h : IsUnit (tm p).det) : ((uGL p : G) : Matrix (Fin 2) (Fin 2) E) = tm p := by
  rw [uGL_of_mem h]; rfl

theorem uGL_of_not {p : Q} (h : ¬ IsUnit (tm p).det) : uGL p = 1 := by
  have h' : ¬ IsUnit (mat (ι4 p)).det := by rw [mat_ι4]; exact h
  simp [uGL, chart, h']

def goodT : Set Q := {p | IsUnit (tm p).det}

theorem mem_goodT_iff (p : Q) : p ∈ goodT ↔ IsUnit p.1 ∧ IsUnit p.2 := by
  simp only [goodT, mem_setOf_eq, det_tm, IsUnit.mul_iff]

theorem isOpen_goodT : IsOpen (goodT : Set Q) := by
  have : (goodT : Set Q) = (fun p : Q => p.1 * p.2) ⁻¹' {x : E | IsUnit x} := by
    ext p; simp [goodT, det_tm]
  rw [this]
  exact isOpen_units.preimage (continuous_fst.mul continuous_snd)

section Meas

variable [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]

theorem measurable_uGL : Measurable (uGL : Q → G) := measurable_chart.comp continuous_ι4.measurable

theorem measurableSet_goodT : MeasurableSet (goodT : Set Q) := isOpen_goodT.measurableSet

end Meas

def sm (q : Q) : Matrix (Fin 2) (Fin 2) E := !![1 + q.1 * q.2, q.1; q.2, 1]
def smi (q : Q) : Matrix (Fin 2) (Fin 2) E := !![1, -q.1; -q.2, 1 + q.1 * q.2]

theorem det_sm (q : Q) : (sm q).det = 1 := by
  simp [sm, Matrix.det_fin_two_of]

theorem sm_mul_smi (q : Q) : sm q * smi q = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sm, smi, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem smi_mul_sm (q : Q) : smi q * sm q = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sm, smi, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

def sGL (q : Q) : G := ⟨sm q, smi q, sm_mul_smi q, smi_mul_sm q⟩

theorem coe_sGL (q : Q) : ((sGL q : G) : Matrix (Fin 2) (Fin 2) E) = sm q := rfl

theorem mk''_sm (q : Q) (h : IsUnit (sm q).det) : Matrix.GeneralLinearGroup.mk'' (sm q) h = sGL q :=
  Units.ext rfl

theorem isUnit_det_sm (q : Q) : IsUnit (sm q).det := by rw [det_sm]; exact isUnit_one

theorem continuous_sGL : Continuous (sGL : Q → G) := by
  rw [Units.continuous_iff]
  constructor
  · change Continuous fun q : Q => sm q
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j
    · exact continuous_const.add (continuous_fst.mul continuous_snd)
    · exact continuous_fst
    · exact continuous_snd
    · exact continuous_const
  · change Continuous fun q : Q => smi q
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j
    · exact continuous_const
    · exact continuous_fst.neg
    · exact continuous_snd.neg
    · exact continuous_const.add (continuous_fst.mul continuous_snd)

section Meas

variable [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]

theorem measurable_sGL : Measurable (sGL : Q → G) := continuous_sGL.measurable

end Meas

end Charts

section Coords

variable [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
variable (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure]

open scoped Classical

attribute [local instance] borelSpace_P borelSpace_Q

local notation "π" => Measure.pi fun _ : Fin 4 => ν
local notation "ν²" => Measure.prod ν ν

def ghI (H : G → ℝ≥0∞) (x : P) : ℝ≥0∞ :=
  (if h : IsUnit (mat x).det then H (Matrix.GeneralLinearGroup.mk'' _ h) else 0) *
    ENNReal.ofReal ((‖Algebra.norm F (mat x).det‖ ^ 2)⁻¹)

theorem ghI_eq (H : G → ℝ≥0∞) (x : P) :
    ghI H x = (if IsUnit (mat x).det then H (chart x) else 0) *
      ENNReal.ofReal ((‖Algebra.norm F (mat x).det‖ ^ 2)⁻¹) := by
  unfold ghI
  by_cases h : IsUnit (mat x).det
  · rw [dif_pos h, if_pos h, chart_of_mem h]
  · rw [dif_neg h, if_neg h]

theorem measurable_ghI {H : G → ℝ≥0∞} (hH : Measurable H) : Measurable (ghI H : P → ℝ≥0∞) := by
  have h1 : Measurable fun x : P => (if IsUnit (mat x).det then H (chart x) else 0) :=
    Measurable.ite measurableSet_good (hH.comp measurable_chart) measurable_const
  have hc1 : Continuous fun x : P => Algebra.norm F (mat x).det := continuous_algebraNorm.comp continuous_det_mat
  have hc : Continuous fun x : P => ‖Algebra.norm F (mat x).det‖ ^ 2 := hc1.norm.pow 2
  have h2 : Measurable fun x : P => ENNReal.ofReal ((‖Algebra.norm F (mat x).det‖ ^ 2)⁻¹) :=
    ENNReal.measurable_ofReal.comp hc.measurable.inv
  have : (ghI H : P → ℝ≥0∞) = fun x : P => (if IsUnit (mat x).det then H (chart x) else 0) *
      ENNReal.ofReal ((‖Algebra.norm F (mat x).det‖ ^ 2)⁻¹) := funext (ghI_eq H)
  rw [this]
  exact h1.mul h2

def GHyp (cG : ℝ≥0∞) : Prop :=
  ∀ H : G → ℝ≥0∞, Measurable H → ∫⁻ g, H g ∂(AutomorphicForm.semiLocalHaar K L v) = cG * ∫⁻ x, ghI H x ∂π

def Dr (p : Q) : ℝ := if p ∈ goodT then ‖Algebra.norm F (p.1 * p.2)‖⁻¹ else 0

def D (p : Q) : ℝ≥0∞ := ENNReal.ofReal (Dr p)

theorem Dr_nonneg (p : Q) : 0 ≤ Dr (K := K) (L := L) (v := v) p := by
  unfold Dr; split_ifs
  · exact inv_nonneg.2 (norm_nonneg _)
  · exact le_rfl

theorem Dr_of_mem {p : Q} (hp : p ∈ goodT) : Dr (K := K) (L := L) (v := v) p = ‖Algebra.norm F (p.1 * p.2)‖⁻¹ := by
  simp [Dr, hp]

theorem Dr_of_not {p : Q} (hp : p ∉ goodT) : Dr (K := K) (L := L) (v := v) p = 0 := by
  simp [Dr, hp]

theorem D_of_mem {p : Q} (hp : p ∈ goodT) : D (K := K) (L := L) (v := v) p = ENNReal.ofReal ‖Algebra.norm F (p.1 * p.2)‖⁻¹ := by
  rw [D, Dr_of_mem hp]

theorem D_of_not {p : Q} (hp : p ∉ goodT) : D (K := K) (L := L) (v := v) p = 0 := by
  rw [D, Dr_of_not hp, ENNReal.ofReal_zero]

theorem measurable_Dr : Measurable (Dr : Q → ℝ) := by
  refine Measurable.ite measurableSet_goodT ?_ measurable_const
  exact ((continuous_algebraNorm.comp (continuous_fst.mul continuous_snd)).norm).measurable.inv

theorem measurable_D : Measurable (D : Q → ℝ≥0∞) := ENNReal.measurable_ofReal.comp measurable_Dr

theorem D_lt_top (p : Q) : D (K := K) (L := L) (v := v) p < ⊤ := ENNReal.ofReal_lt_top

theorem D_toReal (p : Q) : (D (K := K) (L := L) (v := v) p).toReal = Dr p := ENNReal.toReal_ofReal (Dr_nonneg p)

def thI (H : G → ℝ≥0∞) (p : Q) : ℝ≥0∞ := H (uGL p) * D p

theorem measurable_thI {H : G → ℝ≥0∞} (hH : Measurable H) : Measurable (thI H : Q → ℝ≥0∞) :=
  (hH.comp measurable_uGL).mul measurable_D

def pm (q : P) : P := ![q 0 + q 0 * q 1 * q 2, q 0 * q 1, q 3 * q 2, q 3]

def pJ (q : P) : ℝ≥0∞ := ENNReal.ofReal ‖Algebra.norm F (q 0 * q 3)‖

theorem mat_pm (q : P) : mat (pm q) = tm (q 0, q 3) * sm (q 1, q 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mat, pm, tm, sm, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem det_mat_pm (q : P) : (mat (pm q)).det = q 0 * q 3 := by
  rw [mat_pm, Matrix.det_mul, det_tm, det_sm, mul_one]

def e4 : P ≃ᵐ Q × Q where
  toFun x := ((x 1, x 2), (x 0, x 3))
  invFun z := ![z.2.1, z.1.1, z.1.2, z.2.2]
  left_inv x := by
    funext i; fin_cases i <;> rfl
  right_inv z := by
    rcases z with ⟨⟨a, b⟩, ⟨p, r⟩⟩; rfl
  measurable_toFun :=
    ((measurable_pi_apply 1).prodMk (measurable_pi_apply 2)).prodMk
      ((measurable_pi_apply 0).prodMk (measurable_pi_apply 3))
  measurable_invFun := by
    refine measurable_pi_iff.2 fun i => ?_
    fin_cases i
    · exact measurable_fst.comp measurable_snd
    · exact measurable_fst.comp measurable_fst
    · exact measurable_snd.comp measurable_fst
    · exact measurable_snd.comp measurable_snd

theorem e4_apply (x : P) : e4 x = ((x 1, x 2), (x 0, x 3)) := rfl

theorem e4_symm_apply (z : Q × Q) : e4.symm z = ![z.2.1, z.1.1, z.1.2, z.2.2] := rfl

theorem measurePreserving_e4 : MeasurePreserving (e4 : P → Q × Q) π ((ν²).prod (ν²)) := by
  have hpi : (π : Measure P) = Measure.map (e4 : P ≃ᵐ Q × Q).symm ((ν²).prod (ν²)) := by
    refine Measure.pi_eq fun s hs => ?_
    rw [MeasurableEquiv.map_apply]
    have hpre : ((e4 : P ≃ᵐ Q × Q).symm) ⁻¹' (Set.pi univ s) = (s 1 ×ˢ s 2) ×ˢ (s 0 ×ˢ s 3) := by
      ext z
      simp only [Set.mem_preimage, Set.mem_univ_pi, e4_symm_apply, Set.mem_prod]
      constructor
      · intro h
        exact ⟨⟨by simpa using h 1, by simpa using h 2⟩, by simpa using h 0, by simpa using h 3⟩
      · rintro ⟨⟨h1, h2⟩, h0, h3⟩ i
        fin_cases i
        · simpa using h0
        · simpa using h1
        · simpa using h2
        · simpa using h3
    rw [hpre, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod, Fin.prod_univ_four]
    ring
  refine ⟨(e4 : P ≃ᵐ Q × Q).measurable, ?_⟩
  rw [hpi, MeasurableEquiv.map_map_symm]

def Xi (Φ : G → ℝ≥0∞) (z : Q × Q) : ℝ≥0∞ := thI (fun g => Φ (g * sGL z.1)) z.2

theorem Xi_eq (Φ : G → ℝ≥0∞) (z : Q × Q) : Xi Φ z = Φ (uGL z.2 * sGL z.1) * D z.2 := rfl

theorem measurable_Xi {Φ : G → ℝ≥0∞} (hΦ : Measurable Φ) : Measurable (Xi Φ : Q × Q → ℝ≥0∞) := by
  have : (Xi Φ : Q × Q → ℝ≥0∞) = fun z : Q × Q => Φ (uGL z.2 * sGL z.1) * D z.2 := funext (Xi_eq Φ)
  rw [this]
  exact (hΦ.comp ((measurable_uGL.comp measurable_snd).mul (measurable_sGL.comp measurable_fst))).mul
    (measurable_D.comp measurable_snd)

theorem chart_pm {q : P} (h : IsUnit (mat (pm q)).det) : chart (pm q) = uGL (q 0, q 3) * sGL (q 1, q 2) := by
  have hT : IsUnit (tm (q 0, q 3)).det := by rw [det_tm, ← det_mat_pm]; exact h
  apply Units.ext
  rw [coe_chart_of_mem h, Units.val_mul, coe_uGL_of_mem hT, coe_sGL]
  exact mat_pm q

theorem key_pointwise (Φ : G → ℝ≥0∞) (q : P) : ghI Φ (pm q) * pJ q = Xi Φ (e4 q) := by
  rw [e4_apply, Xi_eq, ghI_eq]
  simp only
  by_cases h : IsUnit (q 0 * q 3)
  · have hdet : IsUnit (mat (pm q)).det := by rw [det_mat_pm]; exact h
    have hgood : ((q 0, q 3) : Q) ∈ goodT := by
      show IsUnit (tm (q 0, q 3)).det
      rw [det_tm]; exact h
    rw [if_pos hdet, chart_pm hdet, D_of_mem hgood, det_mat_pm]
    have hn : 0 < ‖Algebra.norm F (q 0 * q 3)‖ := norm_pos_iff.2 ((isUnit_iff_norm_ne_zero _).1 h)
    rw [pJ, mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    field_simp
  · have hdet : ¬ IsUnit (mat (pm q)).det := by rw [det_mat_pm]; exact h
    have hgood : ((q 0, q 3) : Q) ∉ goodT := by
      show ¬ IsUnit (tm (q 0, q 3)).det
      rw [det_tm]; exact h
    rw [if_neg hdet, D_of_not hgood, zero_mul, zero_mul, mul_zero]

variable {cG : ℝ≥0∞}

theorem haar_coords (hG : GHyp ν cG) {Φ : G → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ g, Φ g ∂(AutomorphicForm.semiLocalHaar K L v) =
      cG * ∫⁻ q, ∫⁻ p, Φ (uGL p * sGL q) * D p ∂ν² ∂ν² := by
  have hW := NumberField.AdicCompletion.lintegral_tensor_comp_splitTorusProductChart_mul_norm_algebraNorm_eq_lintegral
    K L v ν (ghI Φ) (measurable_ghI hΦ)
  calc ∫⁻ g, Φ g ∂(AutomorphicForm.semiLocalHaar K L v) = cG * ∫⁻ x, ghI Φ x ∂π := hG Φ hΦ
    _ = cG * ∫⁻ q, ghI Φ (pm q) * pJ q ∂π := by rw [← hW]; rfl
    _ = cG * ∫⁻ q, Xi Φ (e4 q) ∂π := by simp_rw [key_pointwise]
    _ = cG * ∫⁻ z, Xi Φ z ∂((ν²).prod (ν²)) := by
        rw [(measurePreserving_e4 ν).lintegral_comp (measurable_Xi hΦ)]
    _ = cG * ∫⁻ q, ∫⁻ p, Xi Φ (q, p) ∂ν² ∂ν² := by
        rw [lintegral_prod _ (measurable_Xi hΦ).aemeasurable]
    _ = cG * ∫⁻ q, ∫⁻ p, Φ (uGL p * sGL q) * D p ∂ν² ∂ν² := by rfl

end Coords

end KcSemiLocalTorusChart

end

open scoped Classical in
open KcSemiLocalTorusChart in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure]
    (cG : ENNReal)
    (hG : ∀ H : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ENNReal,
        Measurable[AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)] H →
        (letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
         ∫⁻ g, H g ∂(AutomorphicForm.semiLocalHaar K L v)) =
          cG * ∫⁻ x : Fin 4 → L ⊗[K] v.adicCompletion K,
            (if h : IsUnit (!![x 0, x 1; x 2, x 3] :
                Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).det then
                H (Matrix.GeneralLinearGroup.mk'' _ h) else 0) *
              ENNReal.ofReal
                ((‖Algebra.norm (v.adicCompletion K) (!![x 0, x 1; x 2, x 3] :
                    Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).det‖ ^ 2)⁻¹)
            ∂(Measure.pi fun _ : Fin 4 => ν))
    (Φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ENNReal)
    (hΦ : Measurable[AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)] Φ) :
    (letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
     ∫⁻ g, Φ g ∂(AutomorphicForm.semiLocalHaar K L v)) =
      cG * ∫⁻ q : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K),
        ∫⁻ p : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K),
          (if h : IsUnit (!![p.1, 0; 0, p.2] : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).det then
              if h' : IsUnit (!![1 + q.1 * q.2, q.1; q.2, 1] :
                  Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).det then
                Φ (Matrix.GeneralLinearGroup.mk'' _ h * Matrix.GeneralLinearGroup.mk'' _ h')
              else 0
            else 0) *
            ENNReal.ofReal ‖Algebra.norm (v.adicCompletion K) (p.1 * p.2)‖⁻¹ ∂(ν.prod ν) ∂(ν.prod ν) := by
  rw [haar_coords ν hG hΦ]
  congr 1
  refine lintegral_congr fun q => lintegral_congr fun p => ?_
  by_cases h : IsUnit (!![p.1, 0; 0, p.2] : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).det
  · have h1 : IsUnit (tm p).det := h
    have h2 : IsUnit (!![1 + q.1 * q.2, q.1; q.2, 1] : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).det :=
      isUnit_det_sm q
    rw [dif_pos h, dif_pos h2]
    show Φ (uGL p * sGL q) * D p =
      Φ (Matrix.GeneralLinearGroup.mk'' (tm p) h1 * Matrix.GeneralLinearGroup.mk'' (sm q) h2) *
        ENNReal.ofReal ‖Algebra.norm (v.adicCompletion K) (p.1 * p.2)‖⁻¹
    rw [uGL_of_mem h1, mk''_sm, D_of_mem (show p ∈ goodT from h1)]
  · rw [dif_neg h, D_of_not (show p ∉ goodT from h), zero_mul, mul_zero]

end S_AutomorphicForm_lintegral_semiLocalHaar_eq_mul_lintegral_lintegral_torus_mul_unipotentChart
end P2MW
export P2MW.S_AutomorphicForm_lintegral_semiLocalHaar_eq_mul_lintegral_lintegral_torus_mul_unipotentChart (solution)
