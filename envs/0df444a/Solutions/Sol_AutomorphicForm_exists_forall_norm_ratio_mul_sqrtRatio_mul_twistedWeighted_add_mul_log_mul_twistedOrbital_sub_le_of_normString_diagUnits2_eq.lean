-- Prove2me | solution 1 for AutomorphicForm.exists_forall_norm_ratio_mul_sqrtRatio_mul_twistedWeighted_add_mul_log_mul_twistedOrbital_sub_le_of_normString_diagUnits2_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/428e5ccd-5817-5a11-a38c-d4879a57a6a0

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_LocalWeightedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_WindingDatum
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_UnramifiedWhittaker_ZetaIntegrand
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq
import Theorems.Thm_AutomorphicForm_exists_torusSection_forall_normString_diagUnits2_eq
import Theorems.Thm_AutomorphicForm_exists_forall_norm_mul_integral_comp_sigmaTensor_sub_smul_mul_semiLocalWeight_add_sub_integral_mul_log_norm_trace_le
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_image_pow_mem_nhds_one_units_adicCompletion
import Theorems.Thm_AutomorphicForm_exists_units_mul_sigmaTensor_eq_of_norm_eq_one
import Theorems.Thm_AutomorphicForm_IsTwistedOrbitalIntegralOn_unique_of_isRegularSemisimple_normString
import Theorems.Thm_IsLocallyConstant_exists_isOpen_one_mem_forall_mul_eq_of_hasCompactSupport
import Theorems.Thm_AutomorphicForm_eq_of_isTwistedWeightedOrbitalIntegral_of_isTwistedWeightedOrbitalIntegral_of_normString_eq_toTensorGL_diagonal
import Definitions.Def_AutomorphicForm_ConstantTerm
import Theorems.Thm_NumberField_AdicCompletion_map_linearMap_eq_norm_det_inv_smul_of_isAddHaarMeasure
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Theorems.Thm_AutomorphicForm_mem_semiLocalIntegralSet_iff_and_semiLocalHaar_doubleCoset_localEmbed_eq_localHaar_and_map_baseChangeAlgEquiv_eq_smul_pi
import Theorems.Thm_Algebra_TensorProduct_algebraMap_norm_eq_prod_map_algEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_norm_ratio_mul_sqrtRatio_mul_twistedWeighted_add_mul_log_mul_twistedOrbital_sub_le_of_normString_diagUnits2_eq
p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped TensorProduct TensorProduct.RightActions Pointwise

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 320000

open NumberField IsDedekindDomain MeasureTheory Set Function
open scoped ENNReal NNReal TensorProduct TensorProduct.RightActions Pointwise

noncomputable section

namespace KcSemiLocalIwasawaHaar

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {v : HeightOneSpectrum (𝓞 K)}

local notation "F" => v.adicCompletion K
local notation "E" => L ⊗[K] v.adicCompletion K
local notation "Q" => (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K)
local notation "G" => GL (Fin 2) (L ⊗[K] v.adicCompletion K)

attribute [local instance 9999] Algebra.toModule

theorem isTopologicalRing_E : IsTopologicalRing E := AutomorphicForm.isTopologicalRing_tensor K L F
theorem t2Space_E : T2Space E := AutomorphicForm.t2Space_tensor K L F
theorem locallyCompactSpace_E : LocallyCompactSpace E := AutomorphicForm.locallyCompactSpace_tensor K L F
theorem continuousSMul_E : ContinuousSMul F E := IsModuleTopology.toContinuousSMul (R := F) (A := E)
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
  exact Continuous.smul (Continuous.inv₀ (continuous_algebraNorm.comp hf) fun x =>
    (isUnit_iff_norm_ne_zero _).1 (hu x)) (continuous_adjE.comp hf)

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

private theorem _root_.KcSemiLocalIwasawaHaar.isHaarMeasure_semiLocalHaar : (AutomorphicForm.semiLocalHaar K L v).IsHaarMeasure :=
  AutomorphicForm.isHaarMeasure_semiLocalHaar K L v

p2m_export "KcSemiLocalIwasawaHaar" "isHaarMeasure_semiLocalHaar"
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

local notation "μG" => AutomorphicForm.semiLocalHaar K L v
local notation "𝒦" => AutomorphicForm.semiLocalIntegralSet K L v
local notation "𝒪" => AutomorphicForm.semiLocalIntegers K L v

section Charts

open scoped Classical

def tm (p : Q) : Matrix (Fin 2) (Fin 2) E := !![p.1, 0; 0, p.2]

theorem det_tm (p : Q) : (tm p).det = p.1 * p.2 := by
  simp [tm, Matrix.det_fin_two_of]

theorem continuous_tm : Continuous (tm : Q → Matrix (Fin 2) (Fin 2) E) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j
  · exact continuous_fst
  · exact continuous_const
  · exact continuous_const
  · exact continuous_snd

theorem continuous_det_tm : Continuous fun p : Q => (tm p).det := continuous_tm.matrix_det

def goodT : Set Q := {p | IsUnit (tm p).det}

theorem mem_goodT_iff (p : Q) : p ∈ goodT ↔ IsUnit p.1 ∧ IsUnit p.2 := by
  simp only [goodT, mem_setOf_eq, det_tm, IsUnit.mul_iff]

theorem isOpen_goodT : IsOpen (goodT : Set Q) :=
  (isOpen_units (K := K) (L := L) (v := v)).preimage continuous_det_tm

theorem one_mem_goodT : ((1, 1) : Q) ∈ goodT := by
  rw [mem_goodT_iff]; exact ⟨isUnit_one, isUnit_one⟩

def uGL (p : Q) : G := if h : IsUnit (tm p).det then Matrix.GeneralLinearGroup.mk'' (tm p) h else 1

theorem uGL_of_mem {p : Q} (h : IsUnit (tm p).det) : uGL p = Matrix.GeneralLinearGroup.mk'' (tm p) h := by
  simp [uGL, h]

theorem coe_uGL_of_mem {p : Q} (h : IsUnit (tm p).det) : ((uGL p : G) : Matrix (Fin 2) (Fin 2) E) = tm p := by
  rw [uGL_of_mem h]; rfl

theorem uGL_of_not {p : Q} (h : ¬ IsUnit (tm p).det) : uGL p = 1 := by
  simp [uGL, h]

theorem coe_uGL_inv_of_mem {p : Q} (h : IsUnit (tm p).det) :
    (((uGL p)⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) = Ring.inverse (tm p).det • (tm p).adjugate := by
  rw [Matrix.coe_units_inv, coe_uGL_of_mem h, Matrix.inv_def]

theorem continuous_uGL_restrict : Continuous ((goodT : Set Q).domRestrict (uGL : Q → G)) := by
  have hent : ∀ i j, Continuous fun x : (goodT : Set Q) => tm (x : Q) i j := fun i j =>
    (continuous_tm.matrix_elem i j).comp continuous_subtype_val
  refine continuous_GL_of (fun i j => ?_) (fun i j => ?_)
  · have : (fun x : (goodT : Set Q) => (((goodT : Set Q).domRestrict uGL x : G) : Matrix (Fin 2) (Fin 2) E) i j)
        = fun x : (goodT : Set Q) => tm (x : Q) i j := by
      funext x; rw [Set.domRestrict_apply, coe_uGL_of_mem x.2]
    rw [this]; exact hent i j
  · have : (fun x : (goodT : Set Q) =>
        ((((goodT : Set Q).domRestrict uGL x)⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) i j)
        = fun x : (goodT : Set Q) => Ring.inverse (tm (x : Q)).det * (tm (x : Q)).adjugate i j := by
      funext x
      rw [Set.domRestrict_apply, coe_uGL_inv_of_mem x.2, Matrix.smul_apply, smul_eq_mul]
    rw [this]
    have hdet : Continuous fun x : (goodT : Set Q) => (tm (x : Q)).det :=
      continuous_det_tm.comp continuous_subtype_val
    have hri : Continuous fun x : (goodT : Set Q) => Ring.inverse (tm (x : Q)).det :=
      continuous_ringInverse_comp hdet fun x => x.2
    refine hri.mul ?_
    have hadj : Continuous fun x : (goodT : Set Q) => (tm (x : Q)).adjugate :=
      (continuous_tm.comp continuous_subtype_val).matrix_adjugate
    exact hadj.matrix_elem i j

theorem uGL_mul_uGL {a q : Q} (ha : a ∈ goodT) (hq : q ∈ goodT) :
    uGL a * uGL q = uGL (a.1 * q.1, a.2 * q.2) := by
  have haq : ((a.1 * q.1, a.2 * q.2) : Q) ∈ goodT := by
    rw [mem_goodT_iff] at ha hq ⊢
    exact ⟨ha.1.mul hq.1, ha.2.mul hq.2⟩
  apply Units.ext
  rw [Units.val_mul, coe_uGL_of_mem (show IsUnit (tm a).det from ha),
    coe_uGL_of_mem (show IsUnit (tm q).det from hq),
    coe_uGL_of_mem (show IsUnit (tm ((a.1 * q.1, a.2 * q.2) : Q)).det from haq)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tm, Matrix.mul_apply, Fin.sum_univ_two]

def nGL (x : E) : G := AutomorphicForm.unipotentGL2 x

theorem coe_nGL (x : E) : ((nGL x : G) : Matrix (Fin 2) (Fin 2) E) = !![1, x; 0, 1] := rfl

theorem nGL_add (x y : E) : nGL (x + y) = nGL x * nGL y := AutomorphicForm.unipotentGL2_add x y

theorem nGL_zero : nGL (0 : E) = 1 := AutomorphicForm.unipotentGL2_zero

theorem nGL_neg (x : E) : nGL (-x) = (nGL x)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← nGL_add, neg_add_cancel, nGL_zero]

theorem coe_nGL_inv (x : E) : (((nGL x)⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) = !![1, -x; 0, 1] := by
  rw [← nGL_neg]; rfl

theorem continuous_nGL : Continuous (nGL : E → G) := by
  refine continuous_GL_of (fun i j => ?_) (fun i j => ?_)
  · simp only [coe_nGL]
    fin_cases i <;> fin_cases j
    · exact continuous_const
    · exact continuous_id
    · exact continuous_const
    · exact continuous_const
  · simp only [coe_nGL_inv]
    fin_cases i <;> fin_cases j
    · exact continuous_const
    · exact continuous_neg
    · exact continuous_const
    · exact continuous_const

theorem nGL_mul_uGL {q : Q} (hq : q ∈ goodT) (c : E) :
    nGL c * uGL q = uGL q * nGL (Ring.inverse q.1 * c * q.2) := by
  have h1 : IsUnit q.1 := ((mem_goodT_iff q).1 hq).1
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_uGL_of_mem (show IsUnit (tm q).det from hq), coe_nGL, coe_nGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tm, Matrix.mul_apply, Fin.sum_univ_two]
  rw [← mul_assoc, ← mul_assoc, Ring.mul_inverse_cancel _ h1, one_mul]

def ι (z : Q × E) : G := uGL z.1 * nGL z.2

theorem ι_apply (p : Q) (x : E) : ι (p, x) = uGL p * nGL x := rfl

theorem coe_ι_of_mem {p : Q} (hp : p ∈ goodT) (x : E) :
    ((ι (p, x) : G) : Matrix (Fin 2) (Fin 2) E) = !![p.1, p.1 * x; 0, p.2] := by
  rw [ι_apply, Units.val_mul, coe_uGL_of_mem (show IsUnit (tm p).det from hp), coe_nGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tm, Matrix.mul_apply, Fin.sum_univ_two]

theorem coe_ι_inv_of_mem {p : Q} (hp : p ∈ goodT) (x : E) :
    (((ι (p, x))⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) =
      !![Ring.inverse p.1, -x * Ring.inverse p.2; 0, Ring.inverse p.2] := by
  have h1 : IsUnit p.1 := ((mem_goodT_iff p).1 hp).1
  have h2 : IsUnit p.2 := ((mem_goodT_iff p).1 hp).2

  have hmul : ((ι (p, x) : G) : Matrix (Fin 2) (Fin 2) E) *
      !![Ring.inverse p.1, -x * Ring.inverse p.2; 0, Ring.inverse p.2] = 1 := by
    rw [coe_ι_of_mem hp]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Ring.mul_inverse_cancel _ h1, Ring.mul_inverse_cancel _ h2]
    ring_nf
  have hinv : (((ι (p, x))⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) * ((ι (p, x) : G) : Matrix (Fin 2) (Fin 2) E) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc (((ι (p, x))⁻¹ : G) : Matrix (Fin 2) (Fin 2) E)
      = (((ι (p, x))⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) *
          (((ι (p, x) : G) : Matrix (Fin 2) (Fin 2) E) *
            !![Ring.inverse p.1, -x * Ring.inverse p.2; 0, Ring.inverse p.2]) := by rw [hmul, mul_one]
    _ = !![Ring.inverse p.1, -x * Ring.inverse p.2; 0, Ring.inverse p.2] := by
          rw [← mul_assoc, hinv, one_mul]

end Charts

section Kgroup

theorem intg_zero_mem : (0 : E) ∈ 𝒪 := AutomorphicForm.zero_mem_semiLocalIntegers K L v
theorem intg_one_mem : (1 : E) ∈ 𝒪 := AutomorphicForm.one_mem_semiLocalIntegers K L v

theorem intg_add_mem {a b : E} (ha : a ∈ 𝒪) (hb : b ∈ 𝒪) : a + b ∈ 𝒪 := by
  obtain ⟨x, rfl⟩ := ha; obtain ⟨y, rfl⟩ := hb; exact ⟨x + y, map_add _ _ _⟩

theorem intg_mul_mem {a b : E} (ha : a ∈ 𝒪) (hb : b ∈ 𝒪) : a * b ∈ 𝒪 := by
  obtain ⟨x, rfl⟩ := ha; obtain ⟨y, rfl⟩ := hb; exact ⟨x * y, map_mul _ _ _⟩

theorem intg_neg_mem {a : E} (ha : a ∈ 𝒪) : -a ∈ 𝒪 := by
  obtain ⟨x, rfl⟩ := ha; exact ⟨-x, map_neg _ _⟩

theorem isCompact_intg : IsCompact (𝒪 : Set E) := AutomorphicForm.isCompact_semiLocalIntegers K L v
theorem isOpen_intg : IsOpen (𝒪 : Set E) := AutomorphicForm.isOpen_semiLocalIntegers K L v

theorem mem_K_iff (g : G) : g ∈ 𝒦 ↔ (∀ i j, (g : Matrix (Fin 2) (Fin 2) E) i j ∈ 𝒪) ∧
    ∀ i j, ((g⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) i j ∈ 𝒪 := Iff.rfl

theorem matrix_mul_mem {A B : Matrix (Fin 2) (Fin 2) E} (hA : ∀ i j, A i j ∈ 𝒪) (hB : ∀ i j, B i j ∈ 𝒪)
    (i j : Fin 2) : (A * B) i j ∈ 𝒪 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact intg_add_mem (intg_mul_mem (hA _ _) (hB _ _)) (intg_mul_mem (hA _ _) (hB _ _))

theorem K_mul_mem {g h : G} (hg : g ∈ 𝒦) (hh : h ∈ 𝒦) : g * h ∈ 𝒦 := by
  rw [mem_K_iff] at hg hh ⊢
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [Units.val_mul]; exact matrix_mul_mem hg.1 hh.1 i j
  · rw [mul_inv_rev, Units.val_mul]; exact matrix_mul_mem hh.2 hg.2 i j

theorem K_inv_mem {g : G} (hg : g ∈ 𝒦) : g⁻¹ ∈ 𝒦 := by
  rw [mem_K_iff] at hg ⊢
  refine ⟨hg.2, fun i j => ?_⟩
  rw [inv_inv]; exact hg.1 i j

theorem K_one_mem : (1 : G) ∈ 𝒦 := AutomorphicForm.one_mem_semiLocalIntegralSet K L v

def Kgrp : Subgroup G where
  carrier := 𝒦
  mul_mem' := K_mul_mem
  one_mem' := K_one_mem
  inv_mem' := K_inv_mem

theorem mem_Kgrp {g : G} : g ∈ (Kgrp : Subgroup G) ↔ g ∈ 𝒦 := Iff.rfl

theorem K_mul_mem_iff_right {g k : G} (hk : k ∈ 𝒦) : g * k ∈ 𝒦 ↔ g ∈ 𝒦 :=
  (Kgrp (K := K) (L := L) (v := v)).mul_mem_cancel_right (mem_Kgrp.2 hk)

theorem K_mul_mem_iff_left {g k : G} (hk : k ∈ 𝒦) : k * g ∈ 𝒦 ↔ g ∈ 𝒦 :=
  (Kgrp (K := K) (L := L) (v := v)).mul_mem_cancel_left (mem_Kgrp.2 hk)

theorem K_inv_mem_iff {g : G} : g⁻¹ ∈ 𝒦 ↔ g ∈ 𝒦 := (Kgrp (K := K) (L := L) (v := v)).inv_mem_iff

theorem isOpen_K : IsOpen (𝒦 : Set G) := AutomorphicForm.isOpen_semiLocalIntegralSet K L v
theorem isCompact_K : IsCompact (𝒦 : Set G) := AutomorphicForm.isCompact_semiLocalIntegralSet K L v

end Kgroup

section Iwasawa

theorem exists_integral_mul_inv_upper {R Γ₀ : Type*} [Field R] [LinearOrderedCommGroupWithZero Γ₀]
    (w : Valuation R Γ₀) (g : GL (Fin 2) R) :
    ∃ k : GL (Fin 2) R, (∀ i j, w ((k : Matrix (Fin 2) (Fin 2) R) i j) ≤ 1) ∧
      (∀ i j, w (((k⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) i j) ≤ 1) ∧
      ((g * k⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 := by
  set γ : R := (g : Matrix (Fin 2) (Fin 2) R) 1 0 with hγ
  set δ : R := (g : Matrix (Fin 2) (Fin 2) R) 1 1 with hδ
  have hdet : (g : Matrix (Fin 2) (Fin 2) R).det ≠ 0 := by
    have := (Matrix.GeneralLinearGroup.det g).ne_zero
    rwa [Matrix.GeneralLinearGroup.val_det_apply] at this
  have hne : ¬ (γ = 0 ∧ δ = 0) := by
    rintro ⟨h1, h2⟩
    apply hdet
    rw [Matrix.det_fin_two, ← hγ, ← hδ, h1, h2, mul_zero, mul_zero, sub_zero]
  rcases le_total (w γ) (w δ) with h | h
  ·
    have hδ0 : δ ≠ 0 := by
      intro h0
      rw [h0, map_zero, le_zero_iff, Valuation.zero_iff] at h
      exact hne ⟨h, h0⟩
    set t : R := γ / δ with ht
    have hwt : w t ≤ 1 := by
      rw [ht, map_div₀]
      exact div_le_one_of_le₀ h zero_le
    let k : GL (Fin 2) R :=
      ⟨!![1, 0; t, 1], !![1, 0; -t, 1],
        by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
        by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩
    refine ⟨k, fun i j => ?_, fun i j => ?_, ?_⟩
    · fin_cases i <;> fin_cases j <;> simp [k, hwt]
    · show w ((!![1, 0; -t, 1] : Matrix (Fin 2) (Fin 2) R) i j) ≤ 1
      fin_cases i <;> fin_cases j <;> simp [Valuation.map_neg, hwt]
    · show ((g : Matrix (Fin 2) (Fin 2) R) * !![1, 0; -t, 1]) 1 0 = 0
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← hγ, ← hδ, ht]
      field_simp
      ring
  ·
    have hγ0 : γ ≠ 0 := by
      intro h0
      rw [h0, map_zero, le_zero_iff, Valuation.zero_iff] at h
      exact hne ⟨h0, h⟩
    set t : R := δ / γ with ht
    have hwt : w t ≤ 1 := by
      rw [ht, map_div₀]
      exact div_le_one_of_le₀ h zero_le
    let k : GL (Fin 2) R :=
      ⟨!![0, 1; 1, t], !![-t, 1; 1, 0],
        by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
        by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩
    refine ⟨k, fun i j => ?_, fun i j => ?_, ?_⟩
    · fin_cases i <;> fin_cases j <;> simp [k, hwt]
    · show w ((!![-t, 1; 1, 0] : Matrix (Fin 2) (Fin 2) R) i j) ≤ 1
      fin_cases i <;> fin_cases j <;> simp [Valuation.map_neg, hwt]
    · show ((g : Matrix (Fin 2) (Fin 2) R) * !![-t, 1; 1, 0]) 1 0 = 0
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← hγ, ← hδ, ht]
      field_simp
      ring

local notation "W" => HeightOneSpectrum.Extension (𝓞 L) v

def π (w : W) : E →+* w.1.adicCompletion L :=
  (Pi.evalRingHom (fun w' : W => w'.1.adicCompletion L) w).comp
    (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v :
      E →+* Π w' : W, w'.1.adicCompletion L)

theorem π_apply (w : W) (x : E) :
    π w x = HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x w := rfl

theorem π_symm_apply (w : W) (y : Π w' : W, w'.1.adicCompletion L) :
    π (K := K) (L := L) (v := v) w ((HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).symm y) =
      y w := by
  rw [π_apply, AlgEquiv.apply_symm_apply]

theorem eq_of_forall_π_eq {x y : E} (h : ∀ w : W, π w x = π w y) : x = y := by
  apply (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).injective
  funext w; exact h w

theorem isUnit_of_forall_π_ne_zero {x : E} (h : ∀ w : W, π w x ≠ 0) : IsUnit x := by
  set e := HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v with he
  have hu : IsUnit (e x) := by
    rw [Pi.isUnit_iff]
    intro w; exact isUnit_iff_ne_zero.2 (h w)
  have := hu.map e.symm
  rwa [AlgEquiv.symm_apply_apply] at this

theorem mem_K_iff_forall_π (g : G) :
    g ∈ 𝒦 ↔ ∀ w : W, Matrix.GeneralLinearGroup.map (π w) g ∈ AutomorphicForm.localIntegralSet L w.1 := by
  haveI : Finite W := HeightOneSpectrum.Extension.finite (𝓞 K) K L (𝓞 L) v
  haveI : Fintype W := Fintype.ofFinite W
  exact (AutomorphicForm.mem_semiLocalIntegralSet_iff_and_semiLocalHaar_doubleCoset_localEmbed_eq_localHaar_and_map_baseChangeAlgEquiv_eq_smul_pi
    K L v).1 g

theorem GLmap_apply {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (g : GL (Fin 2) R) (i j : Fin 2) :
    ((Matrix.GeneralLinearGroup.map f g : GL (Fin 2) S) : Matrix (Fin 2) (Fin 2) S) i j =
      f ((g : Matrix (Fin 2) (Fin 2) R) i j) := rfl

theorem iwasawa (g : G) : ∃ a : Q, a ∈ goodT ∧ ∃ c : E, ∃ k : G, k ∈ 𝒦 ∧ g = uGL a * nGL c * k := by
  classical
  haveI : Finite W := HeightOneSpectrum.Extension.finite (𝓞 K) K L (𝓞 L) v

  have hloc : ∀ w : W, ∃ kw : GL (Fin 2) (w.1.adicCompletion L),
      kw ∈ AutomorphicForm.localIntegralSet L w.1 ∧
      ((Matrix.GeneralLinearGroup.map (π w) g * kw⁻¹ : GL (Fin 2) (w.1.adicCompletion L)) :
        Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) 1 0 = 0 := by
    intro w
    obtain ⟨kw, h1, h2, h3⟩ := exists_integral_mul_inv_upper (Valued.v (R := w.1.adicCompletion L))
      (Matrix.GeneralLinearGroup.map (π w) g)
    refine ⟨kw, ?_, h3⟩
    rw [AutomorphicForm.mem_localIntegralSet]
    exact ⟨fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (h1 i j),
      fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (h2 i j)⟩
  choose kw hkw hup using hloc

  set e := HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v with he
  let M : Matrix (Fin 2) (Fin 2) (Π w : W, w.1.adicCompletion L) := fun i j w =>
    ((kw w : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) _) i j
  let M' : Matrix (Fin 2) (Fin 2) (Π w : W, w.1.adicCompletion L) := fun i j w =>
    (((kw w)⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) _) i j
  have hMM' : M * M' = 1 := by
    ext i j w
    have h := congrArg (fun m : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L) => m i j)
      (show ((kw w : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) _) * (((kw w)⁻¹ : GL (Fin 2) _) : Matrix _ _ _) = 1
        by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
    simp only [Matrix.mul_apply, Fin.sum_univ_two] at h ⊢
    simpa [M, M', Matrix.one_apply, ite_apply, Pi.one_apply, Pi.zero_apply] using h
  have hM'M : M' * M = 1 := by
    ext i j w
    have h := congrArg (fun m : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L) => m i j)
      (show (((kw w)⁻¹ : GL (Fin 2) _) : Matrix _ _ _) * ((kw w : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) _) = 1
        by rw [← Units.val_mul, inv_mul_cancel, Units.val_one])
    simp only [Matrix.mul_apply, Fin.sum_univ_two] at h ⊢
    simpa [M, M', Matrix.one_apply, ite_apply, Pi.one_apply, Pi.zero_apply] using h
  let kPi : GL (Fin 2) (Π w : W, w.1.adicCompletion L) := ⟨M, M', hMM', hM'M⟩
  let k : G := Matrix.GeneralLinearGroup.map (e.symm : (Π w : W, w.1.adicCompletion L) →+* E) kPi
  have hkw' : ∀ w : W, Matrix.GeneralLinearGroup.map (π w) k = kw w := by
    intro w
    apply Units.ext
    ext i j
    rw [GLmap_apply]
    show π w (e.symm (M i j)) = _
    rw [he, π_symm_apply]
  have hk : k ∈ 𝒦 := by
    rw [mem_K_iff_forall_π]
    intro w; rw [hkw' w]; exact hkw w

  obtain ⟨b, hb⟩ : ∃ b : G, g * k⁻¹ = b := ⟨_, rfl⟩
  have hb10 : (b : Matrix (Fin 2) (Fin 2) E) 1 0 = 0 := by
    apply eq_of_forall_π_eq
    intro w
    rw [map_zero, ← GLmap_apply (π w) b 1 0, ← hb, map_mul, map_inv, hkw' w]
    exact hup w
  have hbdet : IsUnit ((b : Matrix (Fin 2) (Fin 2) E) 0 0 * (b : Matrix (Fin 2) (Fin 2) E) 1 1) := by
    have h1 : IsUnit (b : Matrix (Fin 2) (Fin 2) E).det :=
      ⟨Matrix.GeneralLinearGroup.det b, Matrix.GeneralLinearGroup.val_det_apply b⟩
    rw [Matrix.det_fin_two, hb10, mul_zero, sub_zero] at h1
    exact h1
  set a : Q := ((b : Matrix (Fin 2) (Fin 2) E) 0 0, (b : Matrix (Fin 2) (Fin 2) E) 1 1) with ha
  have hagood : a ∈ goodT := by
    rw [mem_goodT_iff]; exact IsUnit.mul_iff.1 hbdet
  set c : E := Ring.inverse ((b : Matrix (Fin 2) (Fin 2) E) 0 0) * (b : Matrix (Fin 2) (Fin 2) E) 0 1 with hc
  have hbeq : b = uGL a * nGL c := by
    apply Units.ext
    rw [Units.val_mul, coe_uGL_of_mem (show IsUnit (tm a).det from hagood), coe_nGL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [tm, Matrix.mul_apply, Fin.sum_univ_two, ha, hb10]
    rw [hc, ← mul_assoc, Ring.mul_inverse_cancel _ (IsUnit.mul_iff.1 hbdet).1, one_mul]
  refine ⟨a, hagood, c, k, hk, ?_⟩
  rw [← hbeq, ← hb, inv_mul_cancel_right]

end Iwasawa
end KcSemiLocalIwasawaHaar

end

section R2G
open MeasureTheory NumberField IsDedekindDomain
open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped TensorProduct TensorProduct.RightActions

namespace TwLogExpR2

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {v : HeightOneSpectrum (𝓞 K)}

local notation "F" => v.adicCompletion K
local notation "E" => L ⊗[K] v.adicCompletion K
local notation "G" => GL (Fin 2) (L ⊗[K] v.adicCompletion K)
local notation "𝒦" => AutomorphicForm.semiLocalIntegralSet K L v

attribute [local instance 9999] Algebra.toModule

theorem secondCountableTopology_E' [FiniteDimensional K L] : SecondCountableTopology E := by
  let e : E ≃ₗ[F] (Fin (Module.finrank F E) → F) := (Module.finBasis F E).equivFun
  let e' : E ≃L[F] (Fin (Module.finrank F E) → F) :=
    { e with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }
  exact e'.toHomeomorph.secondCountableTopology

theorem secondCountableTopology_GL' [FiniteDimensional K L] : SecondCountableTopology G := by
  haveI := secondCountableTopology_E' (K := K) (L := L) (v := v)
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) E) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → E))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) E)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

private noncomputable def _root_.TwLogExpR2.gslice (σ : L ≃ₐ[K] L) (φ : G → ℂ) (P Q : Eˣ) (z : E) : ℂ :=
  letI := AutomorphicForm.glBorelOf E
  ∫ k in 𝒦, φ (k⁻¹ * (diagUnits2 P Q * AutomorphicForm.unipotentGL2 z) *
    AutomorphicForm.sigmaGL K L F σ k) ∂(AutomorphicForm.semiLocalHaar K L v)

p2m_export "TwLogExpR2" "gslice"

private theorem _root_.TwLogExpR2.norm_gslice_le (σ : L ≃ₐ[K] L) [FiniteDimensional K L] (φ : G → ℂ) (M : ℝ) (hφM : ∀ g, ‖φ g‖ ≤ M)
    (P Q : Eˣ) (z : E) : ‖gslice (K := K) (L := L) (v := v) σ φ P Q z‖ ≤ M := by
  letI := AutomorphicForm.glBorelOf E
  unfold gslice
  have h1 : AutomorphicForm.semiLocalHaar K L v 𝒦 = 1 := AutomorphicForm.semiLocalHaar_semiLocalIntegralSet K L v
  have hlt : AutomorphicForm.semiLocalHaar K L v 𝒦 < ⊤ := by rw [h1]; exact ENNReal.one_lt_top
  refine (norm_setIntegral_le_of_norm_le_const hlt fun k _ => hφM _).trans ?_
  rw [Measure.real, h1, ENNReal.toReal_one, mul_one]

p2m_export "TwLogExpR2" "norm_gslice_le"

private theorem _root_.TwLogExpR2.gslice_eq_zero_of_not (σ : L ≃ₐ[K] L) [FiniteDimensional K L] (φ : G → ℂ) (Pc : Set Eˣ) (Z₀ : Set E)
    (hsupp : ∀ (P Q : Eˣ) (z : E) (k : G), k ∈ 𝒦 →
      φ (k⁻¹ * (diagUnits2 P Q * AutomorphicForm.unipotentGL2 z) * AutomorphicForm.sigmaGL K L F σ k) ≠ 0 →
      P ∈ Pc ∧ Q ∈ Pc ∧ z ∈ Z₀)
    (P Q : Eˣ) (z : E) (h : ¬ (P ∈ Pc ∧ Q ∈ Pc ∧ z ∈ Z₀)) :
    gslice (K := K) (L := L) (v := v) σ φ P Q z = 0 := by
  letI := AutomorphicForm.glBorelOf E
  unfold gslice
  refine setIntegral_eq_zero_of_forall_eq_zero fun k hk => ?_
  by_contra hne
  exact h (hsupp P Q z k hk hne)

p2m_export "TwLogExpR2" "gslice_eq_zero_of_not"

theorem continuous_sigmaGL (σ : L ≃ₐ[K] L) [FiniteDimensional K L] : Continuous (AutomorphicForm.sigmaGL K L F σ) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L F
  refine Continuous.units_map _ ?_
  exact continuous_id.matrix_map (IsModuleTopology.continuous_of_linearMap
    (TensorProduct.RightActions.AlgebraMap.baseChange K L L F σ.toAlgHom).toLinearMap)

theorem continuous_unipotentGL2 [FiniteDimensional K L] :
    Continuous (fun z : E => (AutomorphicForm.unipotentGL2 z : G)) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L F
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [AutomorphicForm.unipotentGL2] <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    have h : ∀ z : E, (((AutomorphicForm.unipotentGL2 z : G)⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) = !![1, -z; 0, 1] :=
      fun z => rfl
    simp_rw [h]
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

set_option maxHeartbeats 1600000 in

private theorem _root_.TwLogExpR2.measurable_gslice_comp (σ : L ≃ₐ[K] L) [FiniteDimensional K L] [MeasurableSpace E] [BorelSpace E]
    (φ : G → ℂ) (hφ : AutomorphicForm.IsSemiLocalTestFn K L v φ) (P Q : Eˣ) (a : E) :
    Measurable (fun z : E => gslice (K := K) (L := L) (v := v) σ φ P Q (a * z)) := by
  letI := AutomorphicForm.glBorelOf E
  haveI : BorelSpace G := AutomorphicForm.borelSpace_glBorelOf E
  haveI := AutomorphicForm.isTopologicalRing_tensor K L F
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L F

  have hφc : Continuous φ := hφ.1.continuous
  have hword : Continuous fun w : E × G =>
      w.2⁻¹ * (diagUnits2 P Q * AutomorphicForm.unipotentGL2 (a * w.1)) * AutomorphicForm.sigmaGL K L F σ w.2 := by
    refine ((continuous_snd.inv).mul (continuous_const.mul ?_)).mul ((continuous_sigmaGL σ).comp continuous_snd)
    exact continuous_unipotentGL2.comp (continuous_const.mul continuous_fst)
  haveI := secondCountableTopology_E' (K := K) (L := L) (v := v)
  haveI := secondCountableTopology_GL' (K := K) (L := L) (v := v)
  haveI := AutomorphicForm.locallyCompactSpace_tensorGL K L F
  haveI : (AutomorphicForm.semiLocalHaar K L v).IsHaarMeasure := AutomorphicForm.isHaarMeasure_semiLocalHaar K L v
  have hf : StronglyMeasurable fun w : E × G =>
      φ (w.2⁻¹ * (diagUnits2 P Q * AutomorphicForm.unipotentGL2 (a * w.1)) * AutomorphicForm.sigmaGL K L F σ w.2) :=
    (hφc.comp hword).stronglyMeasurable
  haveI hfin : IsFiniteMeasure ((AutomorphicForm.semiLocalHaar K L v).restrict 𝒦) :=
    ⟨by rw [Measure.restrict_apply_univ, AutomorphicForm.semiLocalHaar_semiLocalIntegralSet]; exact ENNReal.one_lt_top⟩
  have hsig : SigmaFinite ((AutomorphicForm.semiLocalHaar K L v).restrict 𝒦) :=
    @IsFiniteMeasure.toSigmaFinite G (AutomorphicForm.glBorelOf E) _ hfin
  have hsf : SFinite ((AutomorphicForm.semiLocalHaar K L v).restrict 𝒦) :=
    @instSFiniteOfSigmaFinite G (AutomorphicForm.glBorelOf E) _ hsig
  have h : StronglyMeasurable fun z : E => ∫ k : G, (fun w : E × G =>
        φ (w.2⁻¹ * (diagUnits2 P Q * AutomorphicForm.unipotentGL2 (a * w.1)) * AutomorphicForm.sigmaGL K L F σ w.2)) (z, k)
        ∂((AutomorphicForm.semiLocalHaar K L v).restrict 𝒦) :=
    @StronglyMeasurable.integral_prod_right' E G ℂ _ (AutomorphicForm.glBorelOf E)
      ((AutomorphicForm.semiLocalHaar K L v).restrict 𝒦) _ _ hsf _ hf
  have heq : (fun z : E => gslice (K := K) (L := L) (v := v) σ φ P Q (a * z)) =
      fun z : E => ∫ k : G, (fun w : E × G =>
        φ (w.2⁻¹ * (diagUnits2 P Q * AutomorphicForm.unipotentGL2 (a * w.1)) * AutomorphicForm.sigmaGL K L F σ w.2)) (z, k)
        ∂((AutomorphicForm.semiLocalHaar K L v).restrict 𝒦) := by
    funext z
    unfold gslice
    rfl
  rw [heq]
  exact h.measurable

p2m_export "TwLogExpR2" "measurable_gslice_comp"
end TwLogExpR2

end R2G

section R2Dom
open scoped TensorProduct TensorProduct.RightActions Classical

namespace TwLogExpR2

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {v : HeightOneSpectrum (𝓞 K)}

local notation "F" => v.adicCompletion K
local notation "E" => L ⊗[K] v.adicCompletion K

attribute [local instance 9999] Algebra.toModule

theorem continuous_algebraNorm' : Continuous (Algebra.norm F : E → F) := by
  classical
  let b := Module.finBasis F E
  have h1 : Continuous fun x : E => Algebra.leftMulMatrix b x :=
    IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix b).toLinearMap
  have h2 : (Algebra.norm F : E → F) = fun x => (Algebra.leftMulMatrix b x).det := by
    funext x; exact Algebra.norm_eq_matrix_det b x
  rw [h2]
  exact h1.matrix_det

noncomputable def dom (D : Set (Eˣ × Eˣ)) (βs : E × E → ℝ) (p : E × E) : ℝ :=
  if h : IsUnit p.1 ∧ IsUnit p.2 then
    (if (h.1.unit, h.2.unit) ∈ D then ‖Algebra.norm F (p.1 * p.2)‖⁻¹ * βs p else 0)
  else 0

theorem dom_eq_indicator (D : Set (Eˣ × Eˣ)) (βs : E × E → ℝ) :
    dom (K := K) (L := L) (v := v) D βs =
      ((fun q : Eˣ × Eˣ => (((q.1 : Eˣ) : E), ((q.2 : Eˣ) : E))) '' D).indicator
        (fun p => ‖Algebra.norm F (p.1 * p.2)‖⁻¹ * βs p) := by
  funext p
  unfold dom
  by_cases h : IsUnit p.1 ∧ IsUnit p.2
  · rw [dif_pos h]
    by_cases hD : (h.1.unit, h.2.unit) ∈ D
    · rw [if_pos hD, Set.indicator_of_mem]
      exact ⟨(h.1.unit, h.2.unit), hD, by simp⟩
    · rw [if_neg hD, Set.indicator_of_notMem]
      rintro ⟨q, hq, hqp⟩
      apply hD
      have h1 : h.1.unit = q.1 := Units.ext (by rw [IsUnit.unit_spec]; exact (congrArg Prod.fst hqp).symm)
      have h2 : h.2.unit = q.2 := Units.ext (by rw [IsUnit.unit_spec]; exact (congrArg Prod.snd hqp).symm)
      rw [h1, h2]; exact hq
  · rw [dif_neg h, Set.indicator_of_notMem]
    rintro ⟨q, -, hqp⟩
    apply h
    rw [← hqp]
    exact ⟨q.1.isUnit, q.2.isUnit⟩

set_option maxHeartbeats 3200000 in

theorem exists_V_integrable_dom_and_integral_le [FiniteDimensional K L]
    [MeasurableSpace E] [BorelSpace E] (ν : Measure E) [ν.IsAddHaarMeasure]
    (D : Set (Eˣ × Eˣ)) (hDc : IsCompact D)
    (βs : E × E → ℝ) (hβm : Measurable βs) (hβ01 : ∀ p, 0 ≤ βs p ∧ βs p ≤ 1) :
    ∃ V : ℝ, 0 ≤ V ∧ Integrable (dom (K := K) (L := L) (v := v) D βs) (ν.prod ν) ∧
      ∫ p, dom (K := K) (L := L) (v := v) D βs p ∂(ν.prod ν) ≤ V := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L F
  haveI := AutomorphicForm.t2Space_tensor K L F
  haveI := AutomorphicForm.locallyCompactSpace_tensor K L F
  haveI : SecondCountableTopology E := by
    let e : E ≃ₗ[F] (Fin (Module.finrank F E) → F) := (Module.finBasis F E).equivFun
    let e' : E ≃L[F] (Fin (Module.finrank F E) → F) :=
      { e with
        continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
        continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }
    exact e'.toHomeomorph.secondCountableTopology
  set vv : Eˣ × Eˣ → E × E := fun q => (((q.1 : Eˣ) : E), ((q.2 : Eˣ) : E)) with hvv
  have hvvc : Continuous vv := (Units.continuous_val.comp continuous_fst).prodMk (Units.continuous_val.comp continuous_snd)
  set S : Set (E × E) := vv '' D with hS
  have hSc : IsCompact S := hDc.image hvvc
  have hSm : MeasurableSet S := hSc.isClosed.measurableSet
  have hSfin : (ν.prod ν) S < ⊤ := hSc.measure_lt_top

  have hNc : Continuous fun q : Eˣ × Eˣ => ‖Algebra.norm F ((((q.1 : Eˣ) : E)) * ((q.2 : Eˣ) : E))‖⁻¹ := by
    refine ((continuous_norm.comp (continuous_algebraNorm'.comp ?_)).inv₀ fun q => ?_)
    · exact (Units.continuous_val.comp continuous_fst).mul (Units.continuous_val.comp continuous_snd)
    · show ‖Algebra.norm F ((((q.1 : Eˣ) : E)) * ((q.2 : Eˣ) : E))‖ ≠ 0
      rw [← Units.val_mul]
      exact norm_ne_zero_iff.2 (((q.1 * q.2).isUnit.map (Algebra.norm F)).ne_zero)
  obtain ⟨B, hB⟩ := hDc.exists_bound_of_continuousOn hNc.continuousOn
  set Dmax : ℝ := max B 0 with hDmax
  have hDmax0 : 0 ≤ Dmax := le_max_right _ _
  set f : E × E → ℝ := fun p => ‖Algebra.norm F (p.1 * p.2)‖⁻¹ * βs p with hf
  have hfm : Measurable f := by
    refine Measurable.mul ?_ hβm
    exact ((continuous_norm.comp (continuous_algebraNorm'.comp (continuous_fst.mul continuous_snd))).measurable).inv
  have hfb : ∀ p ∈ S, ‖f p‖ ≤ Dmax := by
    rintro p ⟨q, hq, rfl⟩
    simp only [hf, hvv]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (inv_nonneg.2 (norm_nonneg _)), abs_of_nonneg (hβ01 _).1]
    have h1 := hB q hq
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (norm_nonneg _))] at h1
    calc _ ≤ Dmax * 1 := mul_le_mul (h1.trans (le_max_left _ _)) (hβ01 _).2 (hβ01 _).1 hDmax0
      _ = Dmax := mul_one _
  have hfS : IntegrableOn f S (ν.prod ν) :=
    IntegrableOn.of_bound hSfin hfm.aestronglyMeasurable Dmax
      ((ae_restrict_iff' hSm).2 (Filter.Eventually.of_forall hfb))
  refine ⟨Dmax * ((ν.prod ν) S).toReal, by positivity, ?_, ?_⟩
  · rw [dom_eq_indicator, integrable_indicator_iff hSm]
    exact hfS
  · rw [dom_eq_indicator, integral_indicator hSm]
    calc ∫ p in S, f p ∂(ν.prod ν) ≤ ∫ p in S, Dmax ∂(ν.prod ν) := by
          refine setIntegral_mono_on hfS (integrableOn_const (hs := hSfin.ne)) hSm fun p hp => ?_
          exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hfb p hp))
      _ = Dmax * ((ν.prod ν) S).toReal := by
          rw [setIntegral_const, smul_eq_mul, mul_comm]; rfl

end TwLogExpR2

end R2Dom

section TwCEsec
open scoped TensorProduct TensorProduct.RightActions

namespace TwCE

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (σ : L ≃ₐ[K] L)

section HNorm

variable (A : Type) [CommRing A] [Algebra K A]

theorem norm_algEquiv {S T : Type} [Ring S] [Ring T] [Algebra A S] [Algebra A T] (e : S ≃ₐ[A] T) (x : S) :
    Algebra.norm A (e x) = Algebra.norm A x := by
  rw [Algebra.norm_apply, Algebra.norm_apply]
  have h : (Algebra.lmul A T (e x) : T →ₗ[A] T) =
      (e.toLinearEquiv : S →ₗ[A] T) ∘ₗ (Algebra.lmul A S x : S →ₗ[A] S) ∘ₗ (e.toLinearEquiv.symm : T →ₗ[A] S) := by
    ext y
    simp [Algebra.coe_lmul_eq_mul]
  rw [h, LinearMap.det_conj]

theorem rcomm_tmul (a : A) (l : L) :
    TensorProduct.RightActions.Algebra.TensorProduct.comm K A L (a ⊗ₜ[K] l) = l ⊗ₜ[K] a := by
  rfl

theorem rcomm_map (g : L ≃ₐ[K] L) (z : A ⊗[K] L) :
    TensorProduct.RightActions.Algebra.TensorProduct.comm K A L (Algebra.TensorProduct.map (AlgHom.id K A) (g : L →ₐ[K] L) z) =
      AutomorphicForm.sigmaTensor K L A g (TensorProduct.RightActions.Algebra.TensorProduct.comm K A L z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a l =>
    rw [Algebra.TensorProduct.map_tmul, rcomm_tmul, rcomm_tmul]
    show (g : L →ₐ[K] L) l ⊗ₜ[K] (AlgHom.id K A) a = (Algebra.TensorProduct.map (g : L →ₐ[K] L) (AlgHom.id K A)) (l ⊗ₜ[K] a)
    rw [Algebra.TensorProduct.map_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem algebraMap_norm_eq_prod_sigmaTensor (x : L ⊗[K] A) :
    algebraMap A (L ⊗[K] A) (Algebra.norm A x) = ∏ g : L ≃ₐ[K] L, AutomorphicForm.sigmaTensor K L A g x := by
  classical
  set c := TensorProduct.RightActions.Algebra.TensorProduct.comm K A L with hc
  obtain ⟨z, rfl⟩ : ∃ z, x = c z := ⟨c.symm x, (c.apply_symm_apply x).symm⟩
  rw [norm_algEquiv, ← c.commutes, Algebra.TensorProduct.algebraMap_norm_eq_prod_map_algEquiv K L A z, map_prod]
  refine Finset.prod_congr rfl fun g _ => ?_
  rw [hc, rcomm_map]

theorem sigmaTensor_iterate (i : ℕ) (x : L ⊗[K] A) :
    (AutomorphicForm.sigmaTensor K L A σ)^[i] x = AutomorphicForm.sigmaTensor K L A (σ ^ i) x := by
  induction i generalizing x with
  | zero =>
    simp only [Function.iterate_zero, id_eq, pow_zero]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul l a =>
      show l ⊗ₜ[K] a = (Algebra.TensorProduct.map ((1 : L ≃ₐ[K] L) : L →ₐ[K] L) (AlgHom.id K A)) (l ⊗ₜ[K] a)
      rw [Algebra.TensorProduct.map_tmul]; rfl
    | add x y hx hy => rw [map_add, ← hx, ← hy]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ']
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul l a =>
      show (Algebra.TensorProduct.map (σ : L →ₐ[K] L) (AlgHom.id K A))
          ((Algebra.TensorProduct.map ((σ ^ n : L ≃ₐ[K] L) : L →ₐ[K] L) (AlgHom.id K A)) (l ⊗ₜ[K] a)) =
        (Algebra.TensorProduct.map ((σ * σ ^ n : L ≃ₐ[K] L) : L →ₐ[K] L) (AlgHom.id K A)) (l ⊗ₜ[K] a)
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]; rfl
    | add x y hx hy =>
      rw [map_add, map_add, hx, hy, map_add]

theorem list_prod_range_eq {M : Type} [CommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).prod = ∏ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.prod_range_succ, Finset.prod_range_succ, ih]

theorem orderOf_eq_finrank' (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    orderOf σ = Module.finrank K L := by
  rw [← IsGalois.card_aut_eq_finrank, orderOf_eq_card_of_forall_mem_zpowers hgen, Nat.card_eq_fintype_card]

theorem algebraMap_norm_eq_prod_range (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (x : L ⊗[K] A) :
    algebraMap A (L ⊗[K] A) (Algebra.norm A x) =
      ((List.range (Module.finrank K L)).map fun i => (AutomorphicForm.sigmaTensor K L A σ)^[i] x).prod := by
  classical
  rw [algebraMap_norm_eq_prod_sigmaTensor, list_prod_range_eq]
  have hn : orderOf σ = Module.finrank K L := orderOf_eq_finrank' K L σ hgen
  have hinj : Set.InjOn (fun i : ℕ => σ ^ i) (Finset.range (Module.finrank K L) : Set ℕ) := by
    intro i hi j hj hij
    rw [Finset.coe_range, Set.mem_Iio, ← hn] at hi hj
    exact pow_injOn_Iio_orderOf hi hj hij
  have himg : (Finset.range (Module.finrank K L)).image (fun i : ℕ => σ ^ i) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn hinj, Finset.card_range, ← Nat.card_eq_fintype_card,
      IsGalois.card_aut_eq_finrank]
  rw [← himg, Finset.prod_image hinj]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [sigmaTensor_iterate]

end HNorm

section HNorm2

variable (A : Type) [CommRing A] [Algebra K A]

theorem sigmaGL_diagUnits2 (x y : (L ⊗[K] A)ˣ) :
    AutomorphicForm.sigmaGL K L A σ (diagUnits2 x y) =
      diagUnits2 (Units.map (AutomorphicForm.sigmaTensor K L A σ : L ⊗[K] A →* L ⊗[K] A) x)
        (Units.map (AutomorphicForm.sigmaTensor K L A σ : L ⊗[K] A →* L ⊗[K] A) y) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AutomorphicForm.sigmaGL, Matrix.GeneralLinearGroup.map, LanglandsTunnell.CubicInduction.coe_diagUnits2]

omit σ in
theorem diagUnits2_mul (x y x' y' : (L ⊗[K] A)ˣ) :
    diagUnits2 x y * diagUnits2 x' y' = diagUnits2 (x * x') (y * y') := by
  apply Units.ext
  rw [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2, LanglandsTunnell.CubicInduction.coe_diagUnits2,
    LanglandsTunnell.CubicInduction.coe_diagUnits2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem sigmaGL_iterate_diagUnits2 (i : ℕ) (x y : (L ⊗[K] A)ˣ) :
    (AutomorphicForm.sigmaGL K L A σ)^[i] (diagUnits2 x y) =
      diagUnits2 ((Units.map (AutomorphicForm.sigmaTensor K L A σ : L ⊗[K] A →* L ⊗[K] A))^[i] x)
        ((Units.map (AutomorphicForm.sigmaTensor K L A σ : L ⊗[K] A →* L ⊗[K] A))^[i] y) := by
  induction i with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, sigmaGL_diagUnits2, Function.iterate_succ_apply',
      Function.iterate_succ_apply']

theorem normString_diagUnits2 (x y : (L ⊗[K] A)ˣ) :
    AutomorphicForm.normString K L A σ (diagUnits2 x y) =
      diagUnits2 (((List.range (Module.finrank K L)).map fun i =>
          (Units.map (AutomorphicForm.sigmaTensor K L A σ : L ⊗[K] A →* L ⊗[K] A))^[i] x).prod)
        (((List.range (Module.finrank K L)).map fun i =>
          (Units.map (AutomorphicForm.sigmaTensor K L A σ : L ⊗[K] A →* L ⊗[K] A))^[i] y).prod) := by
  unfold AutomorphicForm.normString
  induction Module.finrank K L with
  | zero =>
    simp only [List.range_zero, List.map_nil, List.prod_nil]
    apply Units.ext
    rw [LanglandsTunnell.CubicInduction.coe_diagUnits2]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  | succ n ih => rw [List.prod_range_succ, List.prod_range_succ, List.prod_range_succ, ih, sigmaGL_iterate_diagUnits2,
      diagUnits2_mul]

omit σ in
theorem toTensorGL_diagUnits2 (a b : Aˣ) :
    AutomorphicForm.toTensorGL K L A (diagUnits2 a b) =
      diagUnits2 (Units.map (algebraMap A (L ⊗[K] A) : A →* L ⊗[K] A) a)
        (Units.map (algebraMap A (L ⊗[K] A) : A →* L ⊗[K] A) b) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AutomorphicForm.toTensorGL, Matrix.GeneralLinearGroup.map, LanglandsTunnell.CubicInduction.coe_diagUnits2,
      TensorProduct.RightActions.algebraMap_eval, Algebra.TensorProduct.includeRight_apply]

omit σ in
theorem val_list_prod_iterate_map (f : L ⊗[K] A →* L ⊗[K] A) (x : (L ⊗[K] A)ˣ) (m : ℕ) :
    ((((List.range m).map fun i => (Units.map f)^[i] x).prod : (L ⊗[K] A)ˣ) : L ⊗[K] A) =
      ((List.range m).map fun i => (⇑f)^[i] (x : L ⊗[K] A)).prod := by
  have hit : ∀ i, (((Units.map f)^[i] x : (L ⊗[K] A)ˣ) : L ⊗[K] A) = (⇑f)^[i] (x : L ⊗[K] A) := by
    intro i
    induction i with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Units.coe_map, ih]
  induction m with
  | zero => simp
  | succ n ih => rw [List.prod_range_succ, List.prod_range_succ, Units.val_mul, ih, hit]

omit σ in
theorem algebraMap_tensor_injective : Function.Injective (algebraMap A (L ⊗[K] A)) := by
  have h : (algebraMap A (L ⊗[K] A) : A → L ⊗[K] A) =
      (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) := by
    funext a
    rw [TensorProduct.RightActions.algebraMap_eval, Algebra.TensorProduct.includeRight_apply]
  rw [h]
  exact Algebra.TensorProduct.includeRight_injective (algebraMap K L).injective

private theorem _root_.TwCE.norm_eq_of_normString_diagUnits2 (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (a b : Aˣ) (α β : (L ⊗[K] A)ˣ)
    (h : AutomorphicForm.normString K L A σ (diagUnits2 α β) = AutomorphicForm.toTensorGL K L A (diagUnits2 a b)) :
    Algebra.norm A (α : L ⊗[K] A) = a ∧ Algebra.norm A (β : L ⊗[K] A) = b := by
  rw [normString_diagUnits2, toTensorGL_diagUnits2] at h
  have hv := congrArg (fun g : GL (Fin 2) (L ⊗[K] A) => (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))) h
  simp only [LanglandsTunnell.CubicInduction.coe_diagUnits2] at hv
  have h00 := congrFun (congrFun hv 0) 0
  have h11 := congrFun (congrFun hv 1) 1
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const] at h00 h11
  rw [val_list_prod_iterate_map, Units.coe_map] at h00 h11
  have h00' : ((List.range (Module.finrank K L)).map fun i =>
      (⇑(AutomorphicForm.sigmaTensor K L A σ))^[i] (α : L ⊗[K] A)).prod = algebraMap A (L ⊗[K] A) a := h00
  have h11' : ((List.range (Module.finrank K L)).map fun i =>
      (⇑(AutomorphicForm.sigmaTensor K L A σ))^[i] (β : L ⊗[K] A)).prod = algebraMap A (L ⊗[K] A) b := h11
  rw [← algebraMap_norm_eq_prod_range K L σ A hgen] at h00' h11'
  exact ⟨algebraMap_tensor_injective K L A h00', algebraMap_tensor_injective K L A h11'⟩

p2m_export "TwCE" "norm_eq_of_normString_diagUnits2"
end HNorm2

end TwCE

end TwCEsec

namespace TwLogExp

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {v : HeightOneSpectrum (𝓞 K)}

open scoped TensorProduct TensorProduct.RightActions

attribute [local instance 9999] Algebra.toModule

local notation "F" => v.adicCompletion K
local notation "E" => L ⊗[K] v.adicCompletion K
local notation "G" => GL (Fin 2) (L ⊗[K] v.adicCompletion K)
local notation "𝒦" => AutomorphicForm.semiLocalIntegralSet K L v

theorem norm_eq_of_norm_sub_lt'' {A : Type*} [NormedField A] [IsUltrametricDist A] {a a' : A}
    (h : ‖a' - a‖ < ‖a‖) : ‖a'‖ = ‖a‖ := by
  apply le_antisymm
  · have h1 : ‖a'‖ = ‖(a' - a) + a‖ := by rw [sub_add_cancel]
    rw [h1]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h.le le_rfl)
  · by_contra hlt
    push_neg at hlt
    have h2 : ‖a‖ = ‖(a - a') + a'‖ := by rw [sub_add_cancel]
    have h3 : ‖a - a'‖ < ‖a‖ := by rwa [norm_sub_rev]
    have := (IsUltrametricDist.norm_add_le_max (a - a') a')
    rw [← h2] at this
    exact absurd (this.trans_lt (max_lt h3 hlt)) (lt_irrefl _)

theorem rs_eq (a t : Fˣ) (ht : ‖(1 : F) - (t : F)‖ < 1) :
    ((AutomorphicForm.LocalWeightedOrbital.ratio (fun x : F => ‖x‖) a (a * t) *
        AutomorphicForm.LocalWeightedOrbital.sqrtRatio (fun x : F => ‖x‖) a (a * t) : ℝ) : ℂ) =
      ((‖(1 : F) - (t : F)‖ : ℝ) : ℂ) := by
  have ht1 : ‖(t : F)‖ = 1 := by
    have h : ‖(t : F) - 1‖ < ‖(1 : F)‖ := by rw [norm_sub_rev, norm_one]; exact ht
    have := norm_eq_of_norm_sub_lt'' h
    rwa [norm_one] at this
  have hprod : ((a * t : Fˣ) : F) * (((a)⁻¹ : Fˣ) : F) = ((t : Fˣ) : F) := by
    rw [← Units.val_mul, mul_comm a t, mul_assoc, mul_inv_cancel, mul_one]
  congr 1
  simp only [AutomorphicForm.LocalWeightedOrbital.ratio, AutomorphicForm.LocalWeightedOrbital.sqrtRatio]
  rw [hprod, Units.val_mul, norm_mul, ht1, mul_one, div_self (norm_pos_iff.2 (Units.ne_zero a)).ne', Real.sqrt_one,
    mul_one]

set_option maxHeartbeats 4000000 in

theorem exists_compact_support (σ : L ≃ₐ[K] L) [FiniteDimensional K L]
    (φ : G → ℂ) (hφ : AutomorphicForm.IsSemiLocalTestFn K L v φ) :
    ∃ Pc : Set Eˣ, IsCompact Pc ∧ ∃ Z₀ : Set E, IsCompact Z₀ ∧
      ∀ (P Q : Eˣ) (z : E) (k : G), k ∈ 𝒦 →
        φ (k⁻¹ * (diagUnits2 P Q * AutomorphicForm.unipotentGL2 z) * AutomorphicForm.sigmaGL K L F σ k) ≠ 0 →
        P ∈ Pc ∧ Q ∈ Pc ∧ z ∈ Z₀ := by
  classical
  haveI := AutomorphicForm.isTopologicalRing_tensor K L F
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L F
  haveI := AutomorphicForm.t2Space_tensor K L F
  obtain ⟨hlc, hcs⟩ := hφ
  have hσG : Continuous (AutomorphicForm.sigmaGL K L F σ) := by
    refine Continuous.units_map _ ?_
    exact continuous_id.matrix_map (IsModuleTopology.continuous_of_linearMap
      (TensorProduct.RightActions.AlgebraMap.baseChange K L L F σ.toAlgHom).toLinearMap)
  set Ω' : Set G := (fun p : G × G => p.1 * p.2 * (AutomorphicForm.sigmaGL K L F σ p.1)⁻¹) ''
    ((𝒦 : Set G) ×ˢ tsupport φ) with hΩ'
  have hΩ'c : IsCompact Ω' := by
    rw [hΩ']
    refine ((AutomorphicForm.isCompact_semiLocalIntegralSet K L v).prod hcs).image ?_
    exact (continuous_fst.mul continuous_snd).mul (hσG.comp continuous_fst).inv
  have hmem : ∀ k ∈ (𝒦 : Set G), ∀ B : G,
      φ (k⁻¹ * B * AutomorphicForm.sigmaGL K L F σ k) ≠ 0 → B ∈ Ω' := by
    intro k hk B hB
    refine ⟨(k, k⁻¹ * B * AutomorphicForm.sigmaGL K L F σ k), Set.mk_mem_prod hk (subset_tsupport _ hB), ?_⟩
    show k * (k⁻¹ * B * AutomorphicForm.sigmaGL K L F σ k) * (AutomorphicForm.sigmaGL K L F σ k)⁻¹ = B
    group

  have hval : Continuous fun B : G => ((B : G) : Matrix (Fin 2) (Fin 2) E) := Units.continuous_val
  have hinv : Continuous fun B : G => (((B⁻¹ : G)) : Matrix (Fin 2) (Fin 2) E) := Units.continuous_coe_inv
  have hent : ∀ i j : Fin 2, Continuous fun B : G => ((B : G) : Matrix (Fin 2) (Fin 2) E) i j := fun i j =>
    (continuous_apply j).comp ((continuous_apply i).comp hval)
  have hent' : ∀ i j : Fin 2, Continuous fun B : G => (((B⁻¹ : G)) : Matrix (Fin 2) (Fin 2) E) i j := fun i j =>
    (continuous_apply j).comp ((continuous_apply i).comp hinv)
  let e : Fin 2 → G → E × MulOpposite E := fun i B =>
    (((B : G) : Matrix (Fin 2) (Fin 2) E) i i, MulOpposite.op ((((B⁻¹ : G)) : Matrix (Fin 2) (Fin 2) E) i i))
  have he : ∀ i, Continuous (e i) := fun i => (hent i i).prodMk (MulOpposite.continuous_op.comp (hent' i i))
  let ez : G → E := fun B => -((((B⁻¹ : G)) : Matrix (Fin 2) (Fin 2) E) 0 1) * ((B : G) : Matrix (Fin 2) (Fin 2) E) 1 1
  have hez : Continuous ez := ((hent' 0 1).neg).mul (hent 1 1)
  set Pc : Set Eˣ := (Units.embedProduct E) ⁻¹' (e 0 '' Ω' ∪ e 1 '' Ω') with hPc
  refine ⟨Pc, ?_, ez '' Ω', hΩ'c.image hez, ?_⟩
  · rw [hPc]
    exact Units.isClosedEmbedding_embedProduct.isCompact_preimage ((hΩ'c.image (he 0)).union (hΩ'c.image (he 1)))
  intro P Q z k hk hne
  have hB := hmem k hk _ hne

  have hBv : ((diagUnits2 P Q * AutomorphicForm.unipotentGL2 z : G) : Matrix (Fin 2) (Fin 2) E) =
      !![(P : E), (P : E) * z; 0, (Q : E)] := by
    rw [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [AutomorphicForm.unipotentGL2, Matrix.mul_apply, Fin.sum_univ_two]
  have hBi : (((diagUnits2 P Q * AutomorphicForm.unipotentGL2 z)⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) =
      !![((P⁻¹ : Eˣ) : E), -z * ((Q⁻¹ : Eˣ) : E); 0, ((Q⁻¹ : Eˣ) : E)] := by
    rw [Matrix.coe_units_inv, hBv]
    apply Matrix.inv_eq_left_inv
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Units.inv_mul, Units.mul_inv, mul_assoc, ← mul_assoc]
  have h00 : ((diagUnits2 P Q * AutomorphicForm.unipotentGL2 z : G) : Matrix (Fin 2) (Fin 2) E) 0 0 = (P : E) := by
    rw [hBv]; simp
  have h11 : ((diagUnits2 P Q * AutomorphicForm.unipotentGL2 z : G) : Matrix (Fin 2) (Fin 2) E) 1 1 = (Q : E) := by
    rw [hBv]; simp
  have hi00 : (((diagUnits2 P Q * AutomorphicForm.unipotentGL2 z)⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) 0 0 =
      ((P⁻¹ : Eˣ) : E) := by rw [hBi]; simp
  have hi11 : (((diagUnits2 P Q * AutomorphicForm.unipotentGL2 z)⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) 1 1 =
      ((Q⁻¹ : Eˣ) : E) := by rw [hBi]; simp
  have hi01 : (((diagUnits2 P Q * AutomorphicForm.unipotentGL2 z)⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) 0 1 =
      -z * ((Q⁻¹ : Eˣ) : E) := by rw [hBi]; simp
  refine ⟨?_, ?_, ?_⟩
  · show Units.embedProduct E P ∈ e 0 '' Ω' ∪ e 1 '' Ω'
    refine Or.inl ⟨_, hB, ?_⟩
    show ((((diagUnits2 P Q * AutomorphicForm.unipotentGL2 z : G) : Matrix (Fin 2) (Fin 2) E) 0 0),
      MulOpposite.op ((((diagUnits2 P Q * AutomorphicForm.unipotentGL2 z)⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) 0 0))
      = Units.embedProduct E P
    rw [h00, hi00]; rfl
  · show Units.embedProduct E Q ∈ e 0 '' Ω' ∪ e 1 '' Ω'
    refine Or.inr ⟨_, hB, ?_⟩
    show ((((diagUnits2 P Q * AutomorphicForm.unipotentGL2 z : G) : Matrix (Fin 2) (Fin 2) E) 1 1),
      MulOpposite.op ((((diagUnits2 P Q * AutomorphicForm.unipotentGL2 z)⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) 1 1))
      = Units.embedProduct E Q
    rw [h11, hi11]; rfl
  · refine ⟨_, hB, ?_⟩
    show -((((diagUnits2 P Q * AutomorphicForm.unipotentGL2 z)⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) 0 1) *
      ((diagUnits2 P Q * AutomorphicForm.unipotentGL2 z : G) : Matrix (Fin 2) (Fin 2) E) 1 1 = z
    rw [hi01, h11]
    calc -(-z * ((Q⁻¹ : Eˣ) : E)) * ((Q : Eˣ) : E) = z * (((Q⁻¹ : Eˣ) : E) * ((Q : Eˣ) : E)) := by ring
      _ = z := by rw [Units.inv_mul, mul_one]

section SliceShift28

theorem ss28_continuous_sigmaTensor (σ : L ≃ₐ[K] L) :
    Continuous (AutomorphicForm.sigmaTensor K L F σ) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L F
  exact IsModuleTopology.continuous_of_linearMap
    (TensorProduct.RightActions.AlgebraMap.baseChange K L L F σ.toAlgHom).toLinearMap

theorem ss28_continuous_sigmaGL (σ : L ≃ₐ[K] L) : Continuous (AutomorphicForm.sigmaGL K L F σ) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L F
  refine Continuous.units_map _ ?_
  exact continuous_id.matrix_map (ss28_continuous_sigmaTensor (K := K) (L := L) (v := v) σ)

theorem ss28_includeRight_eq_smul_one (r : F) :
    (Algebra.TensorProduct.includeRight (R := K) (A := L) r : E) = r • (1 : E) := by
  show (algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K)) r = r • (1 : E)
  exact Algebra.algebraMap_eq_smul_one r

theorem ss28_continuous_iotaE :
    Continuous fun r : F => (Algebra.TensorProduct.includeRight (R := K) (A := L) r : E) := by
  haveI : ContinuousSMul F E := IsModuleTopology.toContinuousSMul (R := F) (A := E)
  have : (fun r : F => (Algebra.TensorProduct.includeRight (R := K) (A := L) r : E)) = fun r : F => r • (1 : E) :=
    funext (ss28_includeRight_eq_smul_one (K := K) (L := L) (v := v))
  rw [this]
  exact continuous_id.fun_smul continuous_const

theorem ss28_toTensorGL_diagUnits2_apply (a b : Fˣ) (i j : Fin 2) :
    ((AutomorphicForm.toTensorGL K L F (diagUnits2 a b) : G) : Matrix (Fin 2) (Fin 2) E) i j =
      Algebra.TensorProduct.includeRight (R := K) (A := L) ((diagUnits2 a b : GL (Fin 2) F) i j) := rfl

theorem ss28_coe_toTensorGL_diagUnits2_one (u : Fˣ) :
    ((AutomorphicForm.toTensorGL K L F (diagUnits2 1 u) : G) : Matrix (Fin 2) (Fin 2) E) =
      !![1, 0; 0, Algebra.TensorProduct.includeRight (R := K) (A := L) ((u : Fˣ) : F)] := by
  ext i j
  rw [ss28_toTensorGL_diagUnits2_apply, LanglandsTunnell.CubicInduction.coe_diagUnits2]
  fin_cases i <;> fin_cases j <;> simp [Algebra.TensorProduct.one_def]

theorem ss28_diagUnits2_one_inv (u : Fˣ) : (diagUnits2 (1 : Fˣ) u)⁻¹ = diagUnits2 1 u⁻¹ := by
  refine inv_eq_of_mul_eq_one_right ?_
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2, LanglandsTunnell.CubicInduction.coe_diagUnits2]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem ss28_continuous_iotaDiag :
    Continuous fun u : Fˣ => AutomorphicForm.toTensorGL K L F (diagUnits2 1 u) := by
  have hι := ss28_continuous_iotaE (K := K) (L := L) (v := v)
  rw [Units.continuous_iff]
  have hinv : ∀ u : Fˣ, ((AutomorphicForm.toTensorGL K L F (diagUnits2 1 u))⁻¹ : G) =
      AutomorphicForm.toTensorGL K L F (diagUnits2 1 u⁻¹) := by
    intro u; rw [← map_inv, ss28_diagUnits2_one_inv]
  constructor
  · show Continuous fun u : Fˣ => ((AutomorphicForm.toTensorGL K L F (diagUnits2 1 u) : G) : Matrix (Fin 2) (Fin 2) E)
    simp_rw [ss28_coe_toTensorGL_diagUnits2_one]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j
    · exact continuous_const
    · exact continuous_const
    · exact continuous_const
    · exact hι.comp Units.continuous_val
  · show Continuous fun u : Fˣ => (((AutomorphicForm.toTensorGL K L F (diagUnits2 1 u))⁻¹ : G) : Matrix (Fin 2) (Fin 2) E)
    simp_rw [hinv, ss28_coe_toTensorGL_diagUnits2_one]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j
    · exact continuous_const
    · exact continuous_const
    · exact continuous_const
    · exact hι.comp Units.continuous_coe_inv

noncomputable def theta (σ : L ≃ₐ[K] L) (z : Fˣ × G) : G :=
  (AutomorphicForm.sigmaGL K L F σ z.2)⁻¹ * AutomorphicForm.toTensorGL K L F (diagUnits2 1 z.1) *
    AutomorphicForm.sigmaGL K L F σ z.2

theorem ss28_continuous_theta (σ : L ≃ₐ[K] L) :
    Continuous (theta (K := K) (L := L) (v := v) σ) := by
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L F
  have hσ := ss28_continuous_sigmaGL (K := K) (L := L) (v := v) σ
  unfold theta
  exact (((hσ.comp continuous_snd).inv).mul
    ((ss28_continuous_iotaDiag (K := K) (L := L) (v := v)).comp continuous_fst)).mul (hσ.comp continuous_snd)

theorem theta_one (σ : L ≃ₐ[K] L) (k : G) : theta (K := K) (L := L) (v := v) σ (1, k) = 1 := by
  unfold theta
  have : diagUnits2 (1 : Fˣ) (1 : Fˣ) = 1 := by
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [LanglandsTunnell.CubicInduction.coe_diagUnits2]
    fin_cases i <;> fin_cases j <;> simp
  simp only [this, map_one, mul_one, inv_mul_cancel]

theorem exists_nhds_forall_theta_mem (σ : L ≃ₐ[K] L) {W : Set G} (hWo : IsOpen W) (h1W : (1 : G) ∈ W) :
    ∃ U₁ ∈ nhds (1 : Fˣ), ∀ u ∈ U₁, ∀ k ∈ 𝒦, theta (K := K) (L := L) (v := v) σ (u, k) ∈ W := by
  have hcont := ss28_continuous_theta (K := K) (L := L) (v := v) σ
  have hopen : IsOpen ((theta (K := K) (L := L) (v := v) σ) ⁻¹' W) := hWo.preimage hcont
  have hsub : ({(1 : Fˣ)} : Set Fˣ) ×ˢ 𝒦 ⊆ (theta (K := K) (L := L) (v := v) σ) ⁻¹' W := by
    rintro ⟨u, k⟩ ⟨hu, -⟩
    have hu' : u = 1 := hu
    subst hu'
    show theta (K := K) (L := L) (v := v) σ (1, k) ∈ W
    rw [theta_one]; exact h1W
  obtain ⟨U₁, V, hU₁, -, h1U, hKV, hUV⟩ :=
    generalized_tube_lemma isCompact_singleton (AutomorphicForm.isCompact_semiLocalIntegralSet K L v) hopen hsub
  refine ⟨U₁, hU₁.mem_nhds (h1U (Set.mem_singleton _)), fun u hu k hk => ?_⟩
  exact hUV (Set.mk_mem_prod hu (hKV hk))

theorem slice_identity (P Q : Eˣ) (z : E) (u : Fˣ) :
    diagUnits2 P (Q * Units.map ((Algebra.TensorProduct.includeRight :
            (v.adicCompletion K) →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom) u) * AutomorphicForm.unipotentGL2 z =
      diagUnits2 P Q * AutomorphicForm.unipotentGL2
          (z * (Algebra.TensorProduct.includeRight (R := K) (A := L) ((u⁻¹ : Fˣ) : F) : E)) *
        AutomorphicForm.toTensorGL K L F (diagUnits2 1 u) := by
  have hu : (Algebra.TensorProduct.includeRight (R := K) (A := L) ((u⁻¹ : Fˣ) : F) : E) *
      Algebra.TensorProduct.includeRight (R := K) (A := L) ((u : Fˣ) : F) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have hz : z * (Algebra.TensorProduct.includeRight (R := K) (A := L) ((u⁻¹ : Fˣ) : F) : E) *
      Algebra.TensorProduct.includeRight (R := K) (A := L) ((u : Fˣ) : F) = z := by
    rw [mul_assoc, hu, mul_one]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2,
    LanglandsTunnell.CubicInduction.coe_diagUnits2, AutomorphicForm.unipotentGL2_coe, AutomorphicForm.unipotentGL2_coe,
    ss28_coe_toTensorGL_diagUnits2_one, Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.mul_fin_two, Units.val_mul,
    Units.coe_map]
  simp only [mul_one, mul_zero, zero_mul, add_zero, zero_add]
  rw [show (P : E) * (z * (Algebra.TensorProduct.includeRight (R := K) (A := L) ((u⁻¹ : Fˣ) : F) : E)) *
      Algebra.TensorProduct.includeRight (R := K) (A := L) ((u : Fˣ) : F) = (P : E) * z by
    rw [mul_assoc (P : E), hz]]
  rfl

end SliceShift28

theorem exists_nhds_forall_slice_shift (σ : L ≃ₐ[K] L) [FiniteDimensional K L]
    (φ : G → ℂ) (hφ : AutomorphicForm.IsSemiLocalTestFn K L v φ) :
    ∃ U₁ ∈ nhds (1 : Fˣ), ∀ u : Fˣ, u ∈ U₁ → ∀ (P Q : Eˣ) (z : E) (k : G), k ∈ 𝒦 →
      φ (k⁻¹ * (diagUnits2 P (Q * Units.map ((Algebra.TensorProduct.includeRight :
            F →ₐ[K] E).toRingHom.toMonoidHom) u) * AutomorphicForm.unipotentGL2 z) *
          AutomorphicForm.sigmaGL K L F σ k) =
      φ (k⁻¹ * (diagUnits2 P Q * AutomorphicForm.unipotentGL2
            (z * (Algebra.TensorProduct.includeRight (R := K) (A := L) ((u⁻¹ : Fˣ) : F) : E))) *
          AutomorphicForm.sigmaGL K L F σ k) := by
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L F
  obtain ⟨W, hWo, h1W, hW⟩ :=
    IsLocallyConstant.exists_isOpen_one_mem_forall_mul_eq_of_hasCompactSupport φ hφ.1 hφ.2
  obtain ⟨U₁, hU₁, hθ⟩ := exists_nhds_forall_theta_mem (K := K) (L := L) (v := v) σ hWo h1W
  refine ⟨U₁, hU₁, fun u hu P Q z k hk => ?_⟩
  have key : k⁻¹ * (diagUnits2 P (Q * Units.map ((Algebra.TensorProduct.includeRight :
            (v.adicCompletion K) →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom) u) * AutomorphicForm.unipotentGL2 z) * AutomorphicForm.sigmaGL K L F σ k =
      (k⁻¹ * (diagUnits2 P Q * AutomorphicForm.unipotentGL2
          (z * (Algebra.TensorProduct.includeRight (R := K) (A := L) ((u⁻¹ : Fˣ) : F) : E))) *
        AutomorphicForm.sigmaGL K L F σ k) * theta (K := K) (L := L) (v := v) σ (u, k) := by
    rw [slice_identity]
    unfold theta
    simp only [mul_assoc, mul_inv_cancel_left]
  rw [key]
  exact (hW _ _ (hθ u hu k hk)).1

noncomputable def kern [FiniteDimensional K L] (q : Eˣ) (z : E) : ℝ :=
  2 * Real.log ‖Algebra.norm F ((q : Eˣ) : E)‖ +
    2 * (Module.finrank K L : ℝ) * Real.log ‖Algebra.trace F E z‖

noncomputable def gslice (σ : L ≃ₐ[K] L) (φ : G → ℂ) (P Q : Eˣ) (z : E) : ℂ :=
  letI := AutomorphicForm.glBorelOf E
  ∫ k in 𝒦, φ (k⁻¹ * (diagUnits2 P Q * AutomorphicForm.unipotentGL2 z) *
    AutomorphicForm.sigmaGL K L F σ k) ∂(AutomorphicForm.semiLocalHaar K L v)

noncomputable def sU (σ : L ≃ₐ[K] L) : Eˣ →* Eˣ := Units.map (AutomorphicForm.sigmaTensor K L F σ : E →* E)

noncomputable def iU : Fˣ →* Eˣ :=
  Units.map ((Algebra.TensorProduct.includeRight : F →ₐ[K] E).toRingHom.toMonoidHom)

open scoped Classical in

noncomputable def Fc (σ : L ≃ₐ[K] L) [MeasurableSpace E] (ν : Measure E) (φ : G → ℂ) (α β : Eˣ)
    (βs : E × E → ℝ) (c : ℝ) (p : E × E) : ℂ :=
  if h : IsUnit p.1 ∧ IsUnit p.2 then
    ((‖Algebra.norm F (p.1 * p.2)‖⁻¹ : ℝ) : ℂ) * (βs p : ℂ) *
      ∫ ξ : E,
        gslice (K := K) (L := L) (v := v) σ φ (α * sU (K := K) (L := L) (v := v) σ h.1.unit * h.1.unit⁻¹)
            (β * sU (K := K) (L := L) (v := v) σ h.2.unit * h.2.unit⁻¹)
            (AutomorphicForm.sigmaTensor K L F σ ξ -
              (((β * sU (K := K) (L := L) (v := v) σ h.2.unit * h.2.unit⁻¹) *
                  (α * sU (K := K) (L := L) (v := v) σ h.1.unit * h.1.unit⁻¹)⁻¹ : Eˣ) : E) * ξ) *
          ((AutomorphicForm.semiLocalWeight K L v (AutomorphicForm.unipotentGL2 ξ) + c : ℝ) : ℂ) ∂ν
  else 0

theorem integral_comp_unit_mul [FiniteDimensional K L] [MeasurableSpace E] [BorelSpace E]
    (ν : Measure E) [ν.IsAddHaarMeasure] (q : Eˣ) (f : E → ℂ) :
    ∫ ξ, f ξ ∂ν = ((‖Algebra.norm F ((q : Eˣ) : E)‖ : ℝ) : ℂ) * ∫ η, f (((q : Eˣ) : E) * η) ∂ν := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L F

  have hc : Continuous fun η : E => ((q : Eˣ) : E) * η := continuous_const.mul continuous_id
  have hc' : Continuous fun η : E => ((q⁻¹ : Eˣ) : E) * η := continuous_const.mul continuous_id
  let e : E ≃ᵐ E :=
    { toFun := fun η => ((q : Eˣ) : E) * η
      invFun := fun η => ((q⁻¹ : Eˣ) : E) * η
      left_inv := fun η => by simp [← mul_assoc]
      right_inv := fun η => by simp [← mul_assoc]
      measurable_toFun := hc.measurable
      measurable_invFun := hc'.measurable }

  have hdet : LinearMap.det ((Algebra.lmul F E ((q : Eˣ) : E)) : E →ₗ[F] E) = Algebra.norm F ((q : Eˣ) : E) := by
    rw [Algebra.norm_apply]
  have hN0 : Algebra.norm F ((q : Eˣ) : E) ≠ 0 := by
    intro h0
    have h1 : Algebra.norm F ((q : Eˣ) : E) * Algebra.norm F ((q⁻¹ : Eˣ) : E) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  have hmap : Measure.map e ν = ENNReal.ofReal ‖Algebra.norm F ((q : Eˣ) : E)‖⁻¹ • ν := by
    have h := NumberField.AdicCompletion.map_linearMap_eq_norm_det_inv_smul_of_isAddHaarMeasure K v E ν
      ((Algebra.lmul F E ((q : Eˣ) : E)) : E →ₗ[F] E) (by rw [hdet]; exact hN0)
    rw [hdet] at h
    exact h
  have h1 : ∫ η, f (((q : Eˣ) : E) * η) ∂ν = ∫ ξ, f ξ ∂(Measure.map e ν) := (MeasureTheory.integral_map_equiv e f).symm
  rw [h1, hmap, integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.2 (norm_nonneg _))]
  have hn0 : (‖Algebra.norm F ((q : Eˣ) : E)‖ : ℝ) ≠ 0 := norm_ne_zero_iff.2 hN0
  rw [Complex.real_smul]
  push_cast
  rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hn0 : ((‖Algebra.norm F ((q : Eˣ) : E)‖ : ℝ) : ℂ) ≠ 0), one_mul]

theorem exists_bound_of_isSemiLocalTestFn (φ : G → ℂ) (hφ : AutomorphicForm.IsSemiLocalTestFn K L v φ) :
    ∃ M : ℝ, 0 < M ∧ ∀ g, ‖φ g‖ ≤ M := by
  obtain ⟨hlc, hcs⟩ := hφ
  obtain ⟨C, hC⟩ := (hlc.continuous.norm).bounded_above_of_compact_support hcs.norm
  refine ⟨max C 1, by positivity, fun g => ?_⟩
  have h := hC g
  rw [norm_norm] at h
  exact h.trans (le_max_left _ _)

namespace L4Kit

theorem sigmaTensor_sigmaTensor (σ τ : L ≃ₐ[K] L) (x : E) :
    AutomorphicForm.sigmaTensor K L F σ (AutomorphicForm.sigmaTensor K L F τ x) =
      AutomorphicForm.sigmaTensor K L F (σ * τ) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul l f =>
    show Algebra.TensorProduct.map _ _ (Algebra.TensorProduct.map _ _ (l ⊗ₜ[K] f)) =
      Algebra.TensorProduct.map _ _ (l ⊗ₜ[K] f)
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem norm_sigmaTensor [FiniteDimensional K L] [IsGalois K L] (τ₀ : L ≃ₐ[K] L) (x : E) :
    Algebra.norm F (AutomorphicForm.sigmaTensor K L F τ₀ x) = Algebra.norm F x := by
  apply (algebraMap F E).injective
  rw [TwCE.algebraMap_norm_eq_prod_sigmaTensor K L F, TwCE.algebraMap_norm_eq_prod_sigmaTensor K L F x]
  simp_rw [sigmaTensor_sigmaTensor]
  exact Fintype.prod_equiv (Equiv.mulRight τ₀) _ _ (fun τ => rfl)

theorem norm_sU_mul_inv [FiniteDimensional K L] [IsGalois K L] (σ : L ≃ₐ[K] L) (u : Eˣ) :
    Algebra.norm F (((sU (K := K) (L := L) (v := v) σ u * u⁻¹ : Eˣ) : E)) = 1 := by
  rw [Units.val_mul, map_mul]
  have h1 : ((sU (K := K) (L := L) (v := v) σ u : Eˣ) : E) = AutomorphicForm.sigmaTensor K L F σ (u : E) := rfl
  rw [h1, norm_sigmaTensor, ← map_mul, Units.mul_inv, map_one]

end L4Kit

theorem Fc_eq_zero_of_not_exists (σ : L ≃ₐ[K] L) [FiniteDimensional K L] [IsGalois K L]
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    [MeasurableSpace E] (ν : Measure E) (φ : G → ℂ)
    (Pc : Set Eˣ) (Z₀ : Set E)
    (hsupp : ∀ (P Q : Eˣ) (z : E) (k : G), k ∈ 𝒦 →
        φ (k⁻¹ * (diagUnits2 P Q * AutomorphicForm.unipotentGL2 z) * AutomorphicForm.sigmaGL K L F σ k) ≠ 0 →
        P ∈ Pc ∧ Q ∈ Pc ∧ z ∈ Z₀)
    (α β : Eˣ) (a b : Fˣ)
    (hN : AutomorphicForm.normString K L F σ (diagUnits2 α β) = AutomorphicForm.toTensorGL K L F (diagUnits2 a b))
    (hex : ¬ ∃ P ∈ Pc, Algebra.norm F ((P : Eˣ) : E) = (a : F))
    (βs : E × E → ℝ) (c : ℝ) (p : E × E) :
    Fc (K := K) (L := L) (v := v) σ ν φ α β βs c p = 0 := by
  classical
  unfold Fc
  split_ifs with h
  · set P : Eˣ := α * sU (K := K) (L := L) (v := v) σ h.1.unit * h.1.unit⁻¹ with hP
    set Q' : Eˣ := β * sU (K := K) (L := L) (v := v) σ h.2.unit * h.2.unit⁻¹ with hQ
    have hNα : Algebra.norm F ((α : Eˣ) : E) = (a : F) :=
      (TwCE.norm_eq_of_normString_diagUnits2 K L σ F hgen a b α β hN).1
    have hNP : Algebra.norm F ((P : Eˣ) : E) = (a : F) := by
      rw [hP, mul_assoc, Units.val_mul, map_mul, hNα, L4Kit.norm_sU_mul_inv, mul_one]
    have hPc : P ∉ Pc := fun hmem => hex ⟨P, hmem, hNP⟩
    have hg : ∀ z : E, gslice (K := K) (L := L) (v := v) σ φ P Q' z = 0 := by
      intro z
      unfold gslice
      refine setIntegral_eq_zero_of_forall_eq_zero fun k hk => ?_
      by_contra hne
      exact hPc (hsupp P Q' z k hk hne).1
    simp only [hg, zero_mul, integral_zero, mul_zero]
  · rfl

theorem L5_lift_move (σ : L ≃ₐ[K] L) (γ γ' cc u : Eˣ)
    (hγ : γ = γ' * (cc * (sU (K := K) (L := L) (v := v) σ cc)⁻¹)) :
    γ * sU (K := K) (L := L) (v := v) σ (cc * u) * (cc * u)⁻¹ = γ' * sU (K := K) (L := L) (v := v) σ u * u⁻¹ := by
  rw [hγ, map_mul]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem L5_norm_unit_ne_zero (q : Eˣ) : Algebra.norm F ((q : Eˣ) : E) ≠ 0 := by
  intro h0
  have h1 : Algebra.norm F ((q : Eˣ) : E) * Algebra.norm F ((q⁻¹ : Eˣ) : E) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  rw [h0, zero_mul] at h1
  exact zero_ne_one h1

theorem L5_Fc_dilate (σ : L ≃ₐ[K] L) [MeasurableSpace E] (ν : Measure E) (φ : G → ℂ)
    (α β α' β' c₁ c₂ : Eˣ)
    (h₁ : α = α' * (c₁ * (sU (K := K) (L := L) (v := v) σ c₁)⁻¹))
    (h₂ : β = β' * (c₂ * (sU (K := K) (L := L) (v := v) σ c₂)⁻¹))
    (βs : E × E → ℝ) (c : ℝ) (p : E × E) :
    Fc (K := K) (L := L) (v := v) σ ν φ α' β' (fun p => βs (((c₁ : Eˣ) : E) * p.1, ((c₂ : Eˣ) : E) * p.2)) c p =
      ((‖Algebra.norm F ((c₁ : Eˣ) : E)‖ * ‖Algebra.norm F ((c₂ : Eˣ) : E)‖ : ℝ) : ℂ) *
        Fc (K := K) (L := L) (v := v) σ ν φ α β βs c (((c₁ : Eˣ) : E) * p.1, ((c₂ : Eˣ) : E) * p.2) := by
  classical
  set N₁ : ℝ := ‖Algebra.norm F ((c₁ : Eˣ) : E)‖ with hN₁
  set N₂ : ℝ := ‖Algebra.norm F ((c₂ : Eˣ) : E)‖ with hN₂
  have hN₁0 : N₁ ≠ 0 := norm_ne_zero_iff.2 (L5_norm_unit_ne_zero (K := K) (L := L) (v := v) c₁)
  have hN₂0 : N₂ ≠ 0 := norm_ne_zero_iff.2 (L5_norm_unit_ne_zero (K := K) (L := L) (v := v) c₂)
  by_cases hp : IsUnit p.1 ∧ IsUnit p.2
  · have hp' : IsUnit (((c₁ : Eˣ) : E) * p.1) ∧ IsUnit (((c₂ : Eˣ) : E) * p.2) :=
      ⟨(Units.isUnit c₁).mul hp.1, (Units.isUnit c₂).mul hp.2⟩
    have hu₁ : hp'.1.unit = c₁ * hp.1.unit := Units.ext (by rw [IsUnit.unit_spec, Units.val_mul, IsUnit.unit_spec])
    have hu₂ : hp'.2.unit = c₂ * hp.2.unit := Units.ext (by rw [IsUnit.unit_spec, Units.val_mul, IsUnit.unit_spec])
    have hA : α * sU (K := K) (L := L) (v := v) σ hp'.1.unit * hp'.1.unit⁻¹ =
        α' * sU (K := K) (L := L) (v := v) σ hp.1.unit * hp.1.unit⁻¹ := by
      rw [hu₁]; exact L5_lift_move (K := K) (L := L) (v := v) σ α α' c₁ hp.1.unit h₁
    have hB : β * sU (K := K) (L := L) (v := v) σ hp'.2.unit * hp'.2.unit⁻¹ =
        β' * sU (K := K) (L := L) (v := v) σ hp.2.unit * hp.2.unit⁻¹ := by
      rw [hu₂]; exact L5_lift_move (K := K) (L := L) (v := v) σ β β' c₂ hp.2.unit h₂
    have hdens : ((‖Algebra.norm F ((((c₁ : Eˣ) : E) * p.1) * (((c₂ : Eˣ) : E) * p.2))‖⁻¹ : ℝ) : ℂ) =
        (((N₁ * N₂)⁻¹ : ℝ) : ℂ) * ((‖Algebra.norm F (p.1 * p.2)‖⁻¹ : ℝ) : ℂ) := by
      have : (((c₁ : Eˣ) : E) * p.1) * (((c₂ : Eˣ) : E) * p.2) = (((c₁ : Eˣ) : E) * ((c₂ : Eˣ) : E)) * (p.1 * p.2) := by ring
      rw [this, map_mul, map_mul, norm_mul, norm_mul, ← hN₁, ← hN₂, ← Complex.ofReal_mul, mul_inv, mul_inv]
    have hNN : ∀ x y z : ℂ, ((N₁ * N₂ : ℝ) : ℂ) * ((((N₁ * N₂)⁻¹ : ℝ) : ℂ) * x * y * z) = x * y * z := by
      intro x y z
      rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (mul_ne_zero hN₁0 hN₂0),
        Complex.ofReal_one, one_mul]
    unfold Fc
    rw [dif_pos hp, dif_pos hp', hA, hB, hdens, hNN]
  · have hp' : ¬ (IsUnit (((c₁ : Eˣ) : E) * p.1) ∧ IsUnit (((c₂ : Eˣ) : E) * p.2)) := by
      rintro ⟨h1, h2⟩
      exact hp ⟨(Units.isUnit_units_mul c₁ p.1).1 h1, (Units.isUnit_units_mul c₂ p.2).1 h2⟩
    unfold Fc
    rw [dif_neg hp, dif_neg hp', mul_zero]

theorem L5_map_mul_unit [FiniteDimensional K L] [MeasurableSpace E] [BorelSpace E]
    (ν : Measure E) [ν.IsAddHaarMeasure] (q : Eˣ) :
    Measure.map (fun η : E => ((q : Eˣ) : E) * η) ν = ENNReal.ofReal ‖Algebra.norm F ((q : Eˣ) : E)‖⁻¹ • ν := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L F
  have hdet : LinearMap.det ((Algebra.lmul F E ((q : Eˣ) : E)) : E →ₗ[F] E) = Algebra.norm F ((q : Eˣ) : E) := by
    rw [Algebra.norm_apply]
  have h := NumberField.AdicCompletion.map_linearMap_eq_norm_det_inv_smul_of_isAddHaarMeasure K v E ν
    ((Algebra.lmul F E ((q : Eˣ) : E)) : E →ₗ[F] E) (by rw [hdet]; exact L5_norm_unit_ne_zero (K := K) (L := L) (v := v) q)
  rw [hdet] at h
  exact h

noncomputable def L5_mulEquiv [MeasurableSpace E] [BorelSpace E] (q : Eˣ) : E ≃ᵐ E :=
  haveI := AutomorphicForm.isTopologicalRing_tensor K L F
  { toFun := fun η => ((q : Eˣ) : E) * η
    invFun := fun η => ((q⁻¹ : Eˣ) : E) * η
    left_inv := fun η => by simp [← mul_assoc]
    right_inv := fun η => by simp [← mul_assoc]
    measurable_toFun := (continuous_const.mul continuous_id).measurable
    measurable_invFun := (continuous_const.mul continuous_id).measurable }

theorem L5_mulEquiv_apply [MeasurableSpace E] [BorelSpace E] (q : Eˣ) (η : E) :
    L5_mulEquiv (K := K) (L := L) (v := v) q η = ((q : Eˣ) : E) * η := rfl

theorem integral_Fc_eq_of_eq_mul (σ : L ≃ₐ[K] L) [FiniteDimensional K L]
    [MeasurableSpace E] [BorelSpace E] (ν : Measure E) [ν.IsAddHaarMeasure] (φ : G → ℂ)
    (α β α' β' c₁ c₂ : Eˣ)
    (h₁ : α = α' * (c₁ * (sU (K := K) (L := L) (v := v) σ c₁)⁻¹))
    (h₂ : β = β' * (c₂ * (sU (K := K) (L := L) (v := v) σ c₂)⁻¹))
    (βs : E × E → ℝ) (c : ℝ) :
    (∫ p, Fc (K := K) (L := L) (v := v) σ ν φ α β βs c p ∂(ν.prod ν) =
      ∫ p, Fc (K := K) (L := L) (v := v) σ ν φ α' β'
        (fun p => βs (((c₁ : Eˣ) : E) * p.1, ((c₂ : Eˣ) : E) * p.2)) c p ∂(ν.prod ν)) ∧
    (Integrable (Fc (K := K) (L := L) (v := v) σ ν φ α β βs c) (ν.prod ν) →
      Integrable (Fc (K := K) (L := L) (v := v) σ ν φ α' β'
        (fun p => βs (((c₁ : Eˣ) : E) * p.1, ((c₂ : Eˣ) : E) * p.2)) c) (ν.prod ν)) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L F
  haveI : T2Space E := AutomorphicForm.t2Space_tensor K L F
  haveI : LocallyCompactSpace E := AutomorphicForm.locallyCompactSpace_tensor K L F
  haveI : SecondCountableTopology E := KcSemiLocalIwasawaHaar.secondCountableTopology_E
  haveI : SigmaCompactSpace E := sigmaCompactSpace_of_locallyCompact_secondCountable
  set N₁ : ℝ := ‖Algebra.norm F ((c₁ : Eˣ) : E)‖ with hN₁
  set N₂ : ℝ := ‖Algebra.norm F ((c₂ : Eˣ) : E)‖ with hN₂
  have hN₁0 : N₁ ≠ 0 := norm_ne_zero_iff.2 (L5_norm_unit_ne_zero (K := K) (L := L) (v := v) c₁)
  have hN₂0 : N₂ ≠ 0 := norm_ne_zero_iff.2 (L5_norm_unit_ne_zero (K := K) (L := L) (v := v) c₂)

  set e : E × E ≃ᵐ E × E :=
    MeasurableEquiv.prodCongr (L5_mulEquiv (K := K) (L := L) (v := v) c₁) (L5_mulEquiv (K := K) (L := L) (v := v) c₂) with he
  have he' : (e : E × E → E × E) = Prod.map (fun η : E => ((c₁ : Eˣ) : E) * η) (fun η : E => ((c₂ : Eˣ) : E) * η) := by
    funext p
    show (L5_mulEquiv (K := K) (L := L) (v := v) c₁ p.1, L5_mulEquiv (K := K) (L := L) (v := v) c₂ p.2) = _
    rfl
  have hmap : Measure.map e (ν.prod ν) = (ENNReal.ofReal N₁⁻¹ * ENNReal.ofReal N₂⁻¹) • (ν.prod ν) := by
    rw [he', ← Measure.map_prod_map ν ν (f := fun η : E => ((c₁ : Eˣ) : E) * η) (g := fun η : E => ((c₂ : Eˣ) : E) * η)
        (continuous_const.mul continuous_id).measurable (continuous_const.mul continuous_id).measurable,
      L5_map_mul_unit (K := K) (L := L) (v := v) ν c₁, L5_map_mul_unit (K := K) (L := L) (v := v) ν c₂,
      Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  have htoReal : (ENNReal.ofReal N₁⁻¹ * ENNReal.ofReal N₂⁻¹).toReal = (N₁ * N₂)⁻¹ := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.2 (norm_nonneg _)),
      ENNReal.toReal_ofReal (inv_nonneg.2 (norm_nonneg _)), mul_inv]
  have hfin : (ENNReal.ofReal N₁⁻¹ * ENNReal.ofReal N₂⁻¹) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hfun : (Fc (K := K) (L := L) (v := v) σ ν φ α' β' (fun p => βs (((c₁ : Eˣ) : E) * p.1, ((c₂ : Eˣ) : E) * p.2)) c) =
      fun p => ((N₁ * N₂ : ℝ) : ℂ) * Fc (K := K) (L := L) (v := v) σ ν φ α β βs c (e p) := by
    funext p
    rw [L5_Fc_dilate (K := K) (L := L) (v := v) σ ν φ α β α' β' c₁ c₂ h₁ h₂ βs c p]
    rfl
  refine ⟨?_, ?_⟩
  · rw [hfun, integral_const_mul, ← MeasureTheory.integral_map_equiv e, hmap, integral_smul_measure, htoReal,
      Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (mul_ne_zero hN₁0 hN₂0),
      Complex.ofReal_one, one_mul]
  · intro hI
    rw [hfun]
    refine Integrable.const_mul ?_ _
    have h2 : Integrable (Fc (K := K) (L := L) (v := v) σ ν φ α β βs c) (Measure.map e (ν.prod ν)) := by
      rw [hmap]; exact hI.smul_measure hfin
    exact (integrable_map_equiv e _).1 h2

theorem inner_eq_norm_mul_integral (σ : L ≃ₐ[K] L) [FiniteDimensional K L]
    [MeasurableSpace E] [BorelSpace E] (ν : Measure E) [ν.IsAddHaarMeasure] (φ : G → ℂ)
    (P Q q : Eˣ) (u : Fˣ)
    (hQP : Q * P⁻¹ = iU (K := K) (L := L) (v := v) u * (sU (K := K) (L := L) (v := v) σ q * q⁻¹)) (c : ℝ) :
    ∫ ξ : E, gslice (K := K) (L := L) (v := v) σ φ P Q
        (AutomorphicForm.sigmaTensor K L F σ ξ - ((Q * P⁻¹ : Eˣ) : E) * ξ) *
        ((AutomorphicForm.semiLocalWeight K L v (AutomorphicForm.unipotentGL2 ξ) + c : ℝ) : ℂ) ∂ν =
      ((‖Algebra.norm F ((q : Eˣ) : E)‖ : ℝ) : ℂ) *
        ∫ η : E, gslice (K := K) (L := L) (v := v) σ φ P Q
          (((sU (K := K) (L := L) (v := v) σ q : Eˣ) : E) *
            (AutomorphicForm.sigmaTensor K L F σ η -
              (Algebra.TensorProduct.includeRight (R := K) (A := L) (u : F) : E) * η)) *
          ((AutomorphicForm.semiLocalWeight K L v (AutomorphicForm.unipotentGL2 (((q : Eˣ) : E) * η)) + c : ℝ) : ℂ) ∂ν := by
  have h := integral_comp_unit_mul (K := K) (L := L) (v := v) ν q
    (fun ξ : E => gslice (K := K) (L := L) (v := v) σ φ P Q
        (AutomorphicForm.sigmaTensor K L F σ ξ - ((Q * P⁻¹ : Eˣ) : E) * ξ) *
        ((AutomorphicForm.semiLocalWeight K L v (AutomorphicForm.unipotentGL2 ξ) + c : ℝ) : ℂ))
  refine h.trans (congrArg (fun I : ℂ => ((‖Algebra.norm F ((q : Eˣ) : E)‖ : ℝ) : ℂ) * I) ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
  have hσq : ((sU (K := K) (L := L) (v := v) σ q : Eˣ) : E) = AutomorphicForm.sigmaTensor K L F σ ((q : Eˣ) : E) := rfl
  have hQP' : ((Q * P⁻¹ : Eˣ) : E) * ((q : Eˣ) : E) =
      (Algebra.TensorProduct.includeRight (R := K) (A := L) (u : F) : E) * AutomorphicForm.sigmaTensor K L F σ ((q : Eˣ) : E) := by
    rw [hQP, Units.val_mul, Units.val_mul, ← hσq, mul_assoc, mul_assoc, ← Units.val_mul q⁻¹ q, inv_mul_cancel,
      Units.val_one, mul_one]
    rfl
  have harg : AutomorphicForm.sigmaTensor K L F σ (((q : Eˣ) : E) * η) - ((Q * P⁻¹ : Eˣ) : E) * (((q : Eˣ) : E) * η) =
      ((sU (K := K) (L := L) (v := v) σ q : Eˣ) : E) *
        (AutomorphicForm.sigmaTensor K L F σ η - (Algebra.TensorProduct.includeRight (R := K) (A := L) (u : F) : E) * η) := by
    rw [map_mul, ← mul_assoc, hQP', hσq]
    ring
  dsimp only
  rw [harg]

private theorem _root_.TwLogExp.norm_eq_of_normString_diagUnits2 (σ : L ≃ₐ[K] L) [FiniteDimensional K L] [IsGalois K L]
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (α β : Eˣ) (a b : Fˣ)
    (hN : AutomorphicForm.normString K L F σ (diagUnits2 α β) = AutomorphicForm.toTensorGL K L F (diagUnits2 a b)) :
    Algebra.norm F ((α : Eˣ) : E) = (a : F) ∧ Algebra.norm F ((β : Eˣ) : E) = (b : F) :=
  TwCE.norm_eq_of_normString_diagUnits2 K L σ F hgen a b α β hN

p2m_export "TwLogExp" "norm_eq_of_normString_diagUnits2"

theorem norm_iU [FiniteDimensional K L] (u : Fˣ) :
    Algebra.norm F ((iU (K := K) (L := L) (v := v) u : Eˣ) : E) = (u : F) ^ Module.finrank K L := by
  have h : ((iU (K := K) (L := L) (v := v) u : Eˣ) : E) = algebraMap F E (u : F) := rfl
  rw [h, Algebra.norm_algebraMap, TensorProduct.finrank_rightAlgebra]

theorem exists_eq_mul_mul_sU_inv (σ : L ≃ₐ[K] L) [FiniteDimensional K L] [IsGalois K L]
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (α α' : Eˣ)
    (h : Algebra.norm F ((α : Eˣ) : E) = Algebra.norm F ((α' : Eˣ) : E)) :
    ∃ c : Eˣ, α = α' * (c * (sU (K := K) (L := L) (v := v) σ c)⁻¹) := by
  have hN' : Algebra.norm F ((α' : Eˣ) : E) ≠ 0 := ((α'.isUnit).map (Algebra.norm F)).ne_zero
  have hx : Algebra.norm F (((α * α'⁻¹ : Eˣ)) : E) = 1 := by
    have hmul : Algebra.norm F (((α * α'⁻¹ : Eˣ)) : E) * Algebra.norm F ((α' : Eˣ) : E) =
        Algebra.norm F ((α : Eˣ) : E) := by
      rw [← map_mul, ← Units.val_mul, inv_mul_cancel_right]
    rw [h] at hmul
    exact (mul_eq_right₀ hN').1 hmul
  obtain ⟨y, hy⟩ := AutomorphicForm.exists_units_mul_sigmaTensor_eq_of_norm_eq_one K L σ hgen v _ hx
  refine ⟨y, ?_⟩
  have hyu : (α * α'⁻¹) * sU (K := K) (L := L) (v := v) σ y = y := by
    apply Units.ext
    rw [Units.val_mul]
    exact hy
  have hq : α * α'⁻¹ = y * (sU (K := K) (L := L) (v := v) σ y)⁻¹ := eq_mul_inv_of_mul_eq hyu
  calc α = (α * α'⁻¹) * α' := by rw [inv_mul_cancel_right]
    _ = α' * (α * α'⁻¹) := mul_comm (α * α'⁻¹) α'
    _ = α' * (y * (sU (K := K) (L := L) (v := v) σ y)⁻¹) := by rw [hq]

theorem gslice_eq_zero_of_not (σ : L ≃ₐ[K] L) [FiniteDimensional K L] (φ : G → ℂ)
    (Pc : Set Eˣ) (Z₀ : Set E)
    (hsupp : ∀ (P Q : Eˣ) (z : E) (k : G), k ∈ 𝒦 →
        φ (k⁻¹ * (diagUnits2 P Q * AutomorphicForm.unipotentGL2 z) * AutomorphicForm.sigmaGL K L F σ k) ≠ 0 →
        P ∈ Pc ∧ Q ∈ Pc ∧ z ∈ Z₀)
    (P Q : Eˣ) (z : E) (h : ¬ (P ∈ Pc ∧ Q ∈ Pc ∧ z ∈ Z₀)) :
    gslice (K := K) (L := L) (v := v) σ φ P Q z = 0 := by
  unfold gslice
  refine setIntegral_eq_zero_of_forall_eq_zero fun k hk => ?_
  by_contra hne
  exact h (hsupp P Q z k hk hne)

theorem norm_gslice_le (σ : L ≃ₐ[K] L) [FiniteDimensional K L] (φ : G → ℂ) (M : ℝ)
    (hφM : ∀ g, ‖φ g‖ ≤ M) (P Q : Eˣ) (z : E) :
    ‖gslice (K := K) (L := L) (v := v) σ φ P Q z‖ ≤ M := by
  letI := AutomorphicForm.glBorelOf E
  unfold gslice
  have h := norm_setIntegral_le_of_norm_le_const (μ := AutomorphicForm.semiLocalHaar K L v)
    (s := AutomorphicForm.semiLocalIntegralSet K L v)
    (f := fun k : G => φ (k⁻¹ * (diagUnits2 P Q * AutomorphicForm.unipotentGL2 z) * AutomorphicForm.sigmaGL K L F σ k))
    (by rw [AutomorphicForm.semiLocalHaar_semiLocalIntegralSet]; exact ENNReal.one_lt_top) (fun k _ => hφM _)
  simp only [measureReal_def, AutomorphicForm.semiLocalHaar_semiLocalIntegralSet, ENNReal.toReal_one, mul_one] at h
  exact h

private theorem _root_.TwLogExp.measurable_gslice_comp (σ : L ≃ₐ[K] L) [FiniteDimensional K L] [MeasurableSpace E] [BorelSpace E]
    (φ : G → ℂ) (hφ : AutomorphicForm.IsSemiLocalTestFn K L v φ) (P Q : Eˣ) (a : E) :
    Measurable (fun z : E => gslice (K := K) (L := L) (v := v) σ φ P Q (a * z)) :=
  TwLogExpR2.measurable_gslice_comp (K := K) (L := L) (v := v) σ φ hφ P Q a

p2m_export "TwLogExp" "measurable_gslice_comp"

theorem kern_iU_mul [FiniteDimensional K L] (q : Eˣ) (u : Fˣ) (hu : ‖(u : F)‖ = 1) (z : E) :
    kern (K := K) (L := L) (v := v) q (((iU (K := K) (L := L) (v := v) u : Eˣ) : E) * z) =
      kern (K := K) (L := L) (v := v) q z := by
  unfold kern
  have h1 : ((iU (K := K) (L := L) (v := v) u : Eˣ) : E) * z = (u : F) • z := by
    show (algebraMap F E (u : F)) * z = (u : F) • z
    exact (Algebra.smul_def (u : F) z).symm
  rw [h1, LinearMap.map_smul, smul_eq_mul, norm_mul, hu, one_mul]

theorem quot_eq (σ : L ≃ₐ[K] L) (α₀ p₁ p₂ : Eˣ) (u : Fˣ) :
    (α₀ * iU (K := K) (L := L) (v := v) u * sU (K := K) (L := L) (v := v) σ p₂ * p₂⁻¹) *
        (α₀ * sU (K := K) (L := L) (v := v) σ p₁ * p₁⁻¹)⁻¹ =
      iU (K := K) (L := L) (v := v) u *
        (sU (K := K) (L := L) (v := v) σ (p₂ * p₁⁻¹) * (p₂ * p₁⁻¹)⁻¹) := by
  simp only [map_mul, map_inv, mul_inv_rev, inv_inv]
  apply Units.ext
  simp only [Units.val_mul]
  have hA : ((α₀ : Eˣ) : E) * (((α₀⁻¹ : Eˣ)) : E) = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  linear_combination ((((iU (K := K) (L := L) (v := v) u : Eˣ)) : E) * ((sU (K := K) (L := L) (v := v) σ p₂ : Eˣ) : E) *
    (((p₂⁻¹ : Eˣ)) : E) * ((p₁ : Eˣ) : E) * ((((sU (K := K) (L := L) (v := v) σ p₁)⁻¹ : Eˣ)) : E)) * hA

theorem inner_eq_norm_mul_M_mul (σ : L ≃ₐ[K] L) [FiniteDimensional K L]
    [MeasurableSpace E] [BorelSpace E] (ν : Measure E) [ν.IsAddHaarMeasure] (φ : G → ℂ)
    (P Q q : Eˣ) (u : Fˣ)
    (hQP : Q * P⁻¹ = iU (K := K) (L := L) (v := v) u * (sU (K := K) (L := L) (v := v) σ q * q⁻¹))
    (c M : ℝ) (hM : 0 < M) :
    ∫ ξ : E, gslice (K := K) (L := L) (v := v) σ φ P Q
        (AutomorphicForm.sigmaTensor K L F σ ξ - ((Q * P⁻¹ : Eˣ) : E) * ξ) *
        ((AutomorphicForm.semiLocalWeight K L v (AutomorphicForm.unipotentGL2 ξ) + c : ℝ) : ℂ) ∂ν =
      ((‖Algebra.norm F ((q : Eˣ) : E)‖ : ℝ) : ℂ) * (((M : ℝ) : ℂ) *
        ∫ η : E, (((M⁻¹ : ℝ) : ℂ) * gslice (K := K) (L := L) (v := v) σ φ P Q
            (((sU (K := K) (L := L) (v := v) σ q : Eˣ) : E) *
              (AutomorphicForm.sigmaTensor K L F σ η -
                (Algebra.TensorProduct.includeRight (R := K) (A := L) (u : F) : E) * η))) *
          ((AutomorphicForm.semiLocalWeight K L v (AutomorphicForm.unipotentGL2 (((q : Eˣ) : E) * η)) + c : ℝ) : ℂ) ∂ν) := by
  rw [inner_eq_norm_mul_integral (K := K) (L := L) (v := v) σ ν φ P Q q u hQP c]
  congr 1
  rw [← integral_const_mul]
  congr 1
  funext η
  have hM0 : ((M : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  rw [← mul_assoc, ← mul_assoc, show ((M : ℝ) : ℂ) * ((M⁻¹ : ℝ) : ℂ) = 1 by push_cast; exact mul_inv_cancel₀ hM0, one_mul]

set_option maxHeartbeats 4000000 in

theorem refIntegral_eq_M_mul (σ : L ≃ₐ[K] L) [FiniteDimensional K L]
    [MeasurableSpace E] [BorelSpace E] (ν : Measure E) [ν.IsAddHaarMeasure] (φ : G → ℂ)
    (P Qr q : Eˣ) (u : Fˣ) (hu : ‖(u : F)‖ = 1)
    (hswapu : ∀ (P' Q' : Eˣ) (z : E) (k : G), k ∈ 𝒦 →
      φ (k⁻¹ * (diagUnits2 P' (Q' * iU (K := K) (L := L) (v := v) u) * AutomorphicForm.unipotentGL2 z) *
          AutomorphicForm.sigmaGL K L F σ k) =
      φ (k⁻¹ * (diagUnits2 P' Q' * AutomorphicForm.unipotentGL2
          (z * (Algebra.TensorProduct.includeRight (R := K) (A := L) ((u⁻¹ : Fˣ) : F) : E))) *
          AutomorphicForm.sigmaGL K L F σ k))
    (M : ℝ) (hM : 0 < M) :
    ∫ z : E, gslice (K := K) (L := L) (v := v) σ φ P Qr (((sU (K := K) (L := L) (v := v) σ q : Eˣ) : E) * z) *
        (kern (K := K) (L := L) (v := v) q z : ℂ) ∂ν =
      ((M : ℝ) : ℂ) * ∫ z : E, (((M⁻¹ : ℝ) : ℂ) *
          gslice (K := K) (L := L) (v := v) σ φ P (Qr * iU (K := K) (L := L) (v := v) u)
            (((sU (K := K) (L := L) (v := v) σ q : Eˣ) : E) * z)) *
        ((2 * Real.log ‖Algebra.norm F ((q : Eˣ) : E)‖ +
            2 * (Module.finrank K L : ℝ) * Real.log ‖Algebra.trace F E z‖ : ℝ) : ℂ) ∂ν := by
  classical
  letI : MeasurableSpace G := AutomorphicForm.glBorelOf E
  haveI : BorelSpace G := AutomorphicForm.borelSpace_glBorelOf E
  haveI := AutomorphicForm.isTopologicalRing_tensor K L F
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L F
  have hMc : ((M : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hM.ne'

  have hkern : ∀ z : E, ((2 * Real.log ‖Algebra.norm F ((q : Eˣ) : E)‖ +
      2 * (Module.finrank K L : ℝ) * Real.log ‖Algebra.trace F E z‖ : ℝ) : ℂ) =
      (kern (K := K) (L := L) (v := v) q z : ℂ) := fun z => rfl
  simp_rw [hkern]

  have hpull : (fun z : E => ((M⁻¹ : ℝ) : ℂ) *
      gslice (K := K) (L := L) (v := v) σ φ P (Qr * iU (K := K) (L := L) (v := v) u)
        (((sU (K := K) (L := L) (v := v) σ q : Eˣ) : E) * z) * (kern (K := K) (L := L) (v := v) q z : ℂ)) =
      fun z : E => ((M⁻¹ : ℝ) : ℂ) *
        (gslice (K := K) (L := L) (v := v) σ φ P (Qr * iU (K := K) (L := L) (v := v) u)
          (((sU (K := K) (L := L) (v := v) σ q : Eˣ) : E) * z) * (kern (K := K) (L := L) (v := v) q z : ℂ)) := by
    funext z; ring
  rw [hpull, integral_const_mul, ← mul_assoc, show ((M : ℝ) : ℂ) * ((M⁻¹ : ℝ) : ℂ) = 1 by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ hM.ne', Complex.ofReal_one], one_mul]

  have hK : MeasurableSet (𝒦 : Set G) := (AutomorphicForm.isOpen_semiLocalIntegralSet K L v).measurableSet
  have hsw : ∀ w : E, gslice (K := K) (L := L) (v := v) σ φ P (Qr * iU (K := K) (L := L) (v := v) u) w =
      gslice (K := K) (L := L) (v := v) σ φ P Qr
        (w * (Algebra.TensorProduct.includeRight (R := K) (A := L) ((u⁻¹ : Fˣ) : F) : E)) := by
    intro w
    unfold gslice
    exact setIntegral_congr_fun hK fun k hk => hswapu P Qr w k hk
  simp_rw [hsw]

  rw [integral_comp_unit_mul (K := K) (L := L) (v := v) ν (iU (K := K) (L := L) (v := v) u)
    (fun z : E => gslice (K := K) (L := L) (v := v) σ φ P Qr
      ((((sU (K := K) (L := L) (v := v) σ q : Eˣ) : E) * z) *
        (Algebra.TensorProduct.includeRight (R := K) (A := L) ((u⁻¹ : Fˣ) : F) : E)) *
      (kern (K := K) (L := L) (v := v) q z : ℂ))]
  have hN1 : ‖Algebra.norm F (((iU (K := K) (L := L) (v := v) u : Eˣ)) : E)‖ = 1 := by
    rw [norm_iU, norm_pow, hu, one_pow]
  rw [hN1, Complex.ofReal_one, one_mul]
  have hι : (((iU (K := K) (L := L) (v := v) u : Eˣ)) : E) *
      (Algebra.TensorProduct.includeRight (R := K) (A := L) ((u⁻¹ : Fˣ) : F) : E) = 1 := by
    show (Algebra.TensorProduct.includeRight (R := K) (A := L) ((u : Fˣ) : F) : E) *
      (Algebra.TensorProduct.includeRight (R := K) (A := L) ((u⁻¹ : Fˣ) : F) : E) = 1
    rw [← map_mul, Units.mul_inv, map_one]
  have hfin : ∀ z : E,
      (((sU (K := K) (L := L) (v := v) σ q : Eˣ) : E) * ((((iU (K := K) (L := L) (v := v) u : Eˣ)) : E) * z)) *
        (Algebra.TensorProduct.includeRight (R := K) (A := L) ((u⁻¹ : Fˣ) : F) : E) =
      ((sU (K := K) (L := L) (v := v) σ q : Eˣ) : E) * z := by
    intro z
    have h1 : (((sU (K := K) (L := L) (v := v) σ q : Eˣ) : E) * ((((iU (K := K) (L := L) (v := v) u : Eˣ)) : E) * z)) *
        (Algebra.TensorProduct.includeRight (R := K) (A := L) ((u⁻¹ : Fˣ) : F) : E) =
      ((sU (K := K) (L := L) (v := v) σ q : Eˣ) : E) * z *
        ((((iU (K := K) (L := L) (v := v) u : Eˣ)) : E) *
          (Algebra.TensorProduct.includeRight (R := K) (A := L) ((u⁻¹ : Fˣ) : F) : E)) := by ring
    rw [h1, hι, mul_one]
  congr 1
  funext z
  rw [kern_iU_mul (K := K) (L := L) (v := v) q u hu z, hfin z]

theorem perp_numeric (dens βsp Nq NQ M C_B ρL : ℝ) (ρ X Y : ℂ)
    (hd : 0 ≤ dens) (hβ : 0 ≤ βsp) (hNq : 0 ≤ Nq) (hNqle : Nq ≤ NQ) (hM : 0 < M) (hρL : 0 ≤ ρL)
    (hB : ‖ρ * X - Y‖ ≤ C_B * ρL) :
    ‖ρ * ((dens : ℂ) * (βsp : ℂ) * ((Nq : ℂ) * ((M : ℂ) * X))) - (dens : ℂ) * (βsp : ℂ) * (Nq : ℂ) * ((M : ℂ) * Y)‖ ≤
      NQ * M * (max C_B 0) * ρL * (dens * βsp) := by
  have e : ρ * ((dens : ℂ) * (βsp : ℂ) * ((Nq : ℂ) * ((M : ℂ) * X))) - (dens : ℂ) * (βsp : ℂ) * (Nq : ℂ) * ((M : ℂ) * Y) =
      ((dens * βsp * Nq * M : ℝ) : ℂ) * (ρ * X - Y) := by push_cast; ring
  have h4 : 0 ≤ dens * βsp * Nq * M := mul_nonneg (mul_nonneg (mul_nonneg hd hβ) hNq) hM.le
  rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h4]
  have hB' : ‖ρ * X - Y‖ ≤ max C_B 0 * ρL := hB.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hρL)
  calc dens * βsp * Nq * M * ‖ρ * X - Y‖ ≤ dens * βsp * NQ * M * (max C_B 0 * ρL) := by
        apply mul_le_mul _ hB' (norm_nonneg _) (mul_nonneg (mul_nonneg (mul_nonneg hd hβ) (hNq.trans hNqle)) hM.le)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNqle (mul_nonneg hd hβ)) hM.le
    _ = NQ * M * (max C_B 0) * ρL * (dens * βsp) := by ring

theorem continuous_diagUnits2_prod [FiniteDimensional K L] :
    Continuous fun q : Eˣ × Eˣ => (diagUnits2 q.1 q.2 : G) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L F
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [LanglandsTunnell.CubicInduction.coe_diagUnits2] <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    have h : ∀ q : Eˣ × Eˣ, (((diagUnits2 q.1 q.2 : G)⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) =
        !![((q.1⁻¹ : Eˣ) : E), 0; 0, ((q.2⁻¹ : Eˣ) : E)] := fun q => rfl
    simp_rw [h]
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem continuous_sigmaGL_r2 (σ : L ≃ₐ[K] L) [FiniteDimensional K L] : Continuous (AutomorphicForm.sigmaGL K L F σ) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L F
  refine Continuous.units_map _ ?_
  exact continuous_id.matrix_map (IsModuleTopology.continuous_of_linearMap
    (TensorProduct.RightActions.AlgebraMap.baseChange K L L F σ.toAlgHom).toLinearMap)

theorem continuous_unipotentGL2_r2 [FiniteDimensional K L] :
    Continuous (fun z : E => (AutomorphicForm.unipotentGL2 z : G)) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L F
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [AutomorphicForm.unipotentGL2] <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    have h : ∀ z : E, (((AutomorphicForm.unipotentGL2 z : G)⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) = !![1, -z; 0, 1] :=
      fun z => rfl
    simp_rw [h]
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem continuous_sU (σ : L ≃ₐ[K] L) [FiniteDimensional K L] :
    Continuous (sU (K := K) (L := L) (v := v) σ) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L F
  refine Continuous.units_map _ ?_
  exact IsModuleTopology.continuous_of_linearMap
    (TensorProduct.RightActions.AlgebraMap.baseChange K L L F σ.toAlgHom).toLinearMap

set_option maxHeartbeats 6400000 in
open scoped Classical in

theorem measurable_Gref (σ : L ≃ₐ[K] L) [FiniteDimensional K L]
    [MeasurableSpace E] [BorelSpace E] (ν : Measure E) [ν.IsAddHaarMeasure]
    (φ : G → ℂ) (hφ : AutomorphicForm.IsSemiLocalTestFn K L v φ) (α₀ : Eˣ)
    (βs : E × E → ℝ) (hβm : Measurable βs)
    (qf : E × E → Eˣ) (hqf : ∀ (p : E × E) (h : IsUnit p.1 ∧ IsUnit p.2), qf p = h.2.unit * h.1.unit⁻¹) :
    Measurable (fun p : E × E =>
      (if h : IsUnit p.1 ∧ IsUnit p.2 then
          ((‖Algebra.norm F (p.1 * p.2)‖⁻¹ : ℝ) : ℂ) * (βs p : ℂ) *
            ((‖Algebra.norm F (((qf p : Eˣ)) : E)‖ : ℝ) : ℂ) *
            ∫ z : E, gslice (K := K) (L := L) (v := v) σ φ
                (α₀ * sU (K := K) (L := L) (v := v) σ h.1.unit * h.1.unit⁻¹)
                (α₀ * sU (K := K) (L := L) (v := v) σ h.2.unit * h.2.unit⁻¹)
                (((sU (K := K) (L := L) (v := v) σ (qf p) : Eˣ) : E) * z) *
              (kern (K := K) (L := L) (v := v) (qf p) z : ℂ) ∂ν
       else 0)) := by
  classical
  letI : MeasurableSpace G := AutomorphicForm.glBorelOf E
  haveI : BorelSpace G := AutomorphicForm.borelSpace_glBorelOf E
  haveI := AutomorphicForm.isTopologicalRing_tensor K L F
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L F
  haveI := AutomorphicForm.locallyCompactSpace_tensor K L F
  haveI := AutomorphicForm.t2Space_tensor K L F
  haveI : SecondCountableTopology E := KcSemiLocalIwasawaHaar.secondCountableTopology_E (K := K) (L := L) (v := v)
  haveI : SecondCountableTopology G := KcSemiLocalIwasawaHaar.secondCountableTopology_GL (K := K) (L := L) (v := v)

  set U : Set (E × E) := {p | IsUnit p.1 ∧ IsUnit p.2} with hU
  have hUo : IsOpen U := by
    have h1 : IsOpen {x : E | IsUnit x} := KcSemiLocalIwasawaHaar.isOpen_units (K := K) (L := L) (v := v)
    exact (h1.preimage continuous_fst).inter (h1.preimage continuous_snd)
  have hUm : MeasurableSet U := hUo.measurableSet
  refine measurable_of_restrict_of_restrict_compl hUm ?_ ?_
  swap
  ·
    have : (Uᶜ.domRestrict fun p : E × E =>
      (if h : IsUnit p.1 ∧ IsUnit p.2 then
          ((‖Algebra.norm F (p.1 * p.2)‖⁻¹ : ℝ) : ℂ) * (βs p : ℂ) *
            ((‖Algebra.norm F (((qf p : Eˣ)) : E)‖ : ℝ) : ℂ) *
            ∫ z : E, gslice (K := K) (L := L) (v := v) σ φ
                (α₀ * sU (K := K) (L := L) (v := v) σ h.1.unit * h.1.unit⁻¹)
                (α₀ * sU (K := K) (L := L) (v := v) σ h.2.unit * h.2.unit⁻¹)
                (((sU (K := K) (L := L) (v := v) σ (qf p) : Eˣ) : E) * z) *
              (kern (K := K) (L := L) (v := v) (qf p) z : ℂ) ∂ν
       else 0)) = fun _ => 0 := by
      funext p
      simp only [Set.domRestrict_apply]
      rw [dif_neg (show ¬ (IsUnit (p : E × E).1 ∧ IsUnit (p : E × E).2) from p.2)]
    rw [this]
    exact measurable_const

  set u₁ : U → Eˣ := fun p => (p.2).1.unit with hu₁
  set u₂ : U → Eˣ := fun p => (p.2).2.unit with hu₂
  have hu₁c : Continuous u₁ := by
    rw [Units.continuous_iff]
    refine ⟨continuous_fst.comp continuous_subtype_val, ?_⟩
    have : (fun p : U => (((u₁ p)⁻¹ : Eˣ) : E)) = fun p : U => Ring.inverse ((p : E × E).1) := by
      funext p; rw [show ((p : E × E).1) = ((u₁ p : Eˣ) : E) from rfl, Ring.inverse_unit]
    rw [this]
    exact KcSemiLocalIwasawaHaar.continuous_ringInverse_comp (K := K) (L := L) (v := v)
      (continuous_fst.comp continuous_subtype_val) fun p => p.2.1
  have hu₂c : Continuous u₂ := by
    rw [Units.continuous_iff]
    refine ⟨continuous_snd.comp continuous_subtype_val, ?_⟩
    have : (fun p : U => (((u₂ p)⁻¹ : Eˣ) : E)) = fun p : U => Ring.inverse ((p : E × E).2) := by
      funext p; rw [show ((p : E × E).2) = ((u₂ p : Eˣ) : E) from rfl, Ring.inverse_unit]
    rw [this]
    exact KcSemiLocalIwasawaHaar.continuous_ringInverse_comp (K := K) (L := L) (v := v)
      (continuous_snd.comp continuous_subtype_val) fun p => p.2.2
  set qq : U → Eˣ := fun p => u₂ p * (u₁ p)⁻¹ with hqq
  have hqqc : Continuous qq := hu₂c.mul hu₁c.inv
  have hqf' : ∀ p : U, qf (p : E × E) = qq p := fun p => hqf p p.2
  set A : U → Eˣ := fun p => α₀ * sU (K := K) (L := L) (v := v) σ (u₁ p) * (u₁ p)⁻¹ with hA
  set B : U → Eˣ := fun p => α₀ * sU (K := K) (L := L) (v := v) σ (u₂ p) * (u₂ p)⁻¹ with hB
  have hσc := continuous_sU (K := K) (L := L) (v := v) σ
  have hAc : Continuous A := (continuous_const.mul (hσc.comp hu₁c)).mul hu₁c.inv
  have hBc : Continuous B := (continuous_const.mul (hσc.comp hu₂c)).mul hu₂c.inv

  have hre : (U.domRestrict fun p : E × E =>
      (if h : IsUnit p.1 ∧ IsUnit p.2 then
          ((‖Algebra.norm F (p.1 * p.2)‖⁻¹ : ℝ) : ℂ) * (βs p : ℂ) *
            ((‖Algebra.norm F (((qf p : Eˣ)) : E)‖ : ℝ) : ℂ) *
            ∫ z : E, gslice (K := K) (L := L) (v := v) σ φ
                (α₀ * sU (K := K) (L := L) (v := v) σ h.1.unit * h.1.unit⁻¹)
                (α₀ * sU (K := K) (L := L) (v := v) σ h.2.unit * h.2.unit⁻¹)
                (((sU (K := K) (L := L) (v := v) σ (qf p) : Eˣ) : E) * z) *
              (kern (K := K) (L := L) (v := v) (qf p) z : ℂ) ∂ν
       else 0)) =
      fun p : U => ((‖Algebra.norm F ((p : E × E).1 * (p : E × E).2)‖⁻¹ : ℝ) : ℂ) * (βs p : ℂ) *
            ((‖Algebra.norm F (((qq p : Eˣ)) : E)‖ : ℝ) : ℂ) *
            ∫ z : E, gslice (K := K) (L := L) (v := v) σ φ (A p) (B p)
                (((sU (K := K) (L := L) (v := v) σ (qq p) : Eˣ) : E) * z) *
              (kern (K := K) (L := L) (v := v) (qq p) z : ℂ) ∂ν := by
    funext p
    simp only [Set.domRestrict_apply]
    rw [dif_pos (show IsUnit (p : E × E).1 ∧ IsUnit (p : E × E).2 from p.2), hqf' p]
  rw [hre]

  have hNc : Continuous (Algebra.norm F : E → F) := KcSemiLocalIwasawaHaar.continuous_algebraNorm (K := K) (L := L) (v := v)
  have m1 : Measurable fun p : U => ((‖Algebra.norm F ((p : E × E).1 * (p : E × E).2)‖⁻¹ : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp ((continuous_norm.comp (hNc.comp
      ((continuous_fst.comp continuous_subtype_val).mul (continuous_snd.comp continuous_subtype_val)))).measurable.inv)
  have m2 : Measurable fun p : U => (βs p : ℂ) :=
    Complex.measurable_ofReal.comp (hβm.comp measurable_subtype_coe)
  have m3 : Measurable fun p : U => ((‖Algebra.norm F (((qq p : Eˣ)) : E)‖ : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (continuous_norm.comp (hNc.comp (Units.continuous_val.comp hqqc))).measurable

  have hφc : Continuous φ := hφ.1.continuous
  have hword : Continuous fun w : (U × E) × G =>
      w.2⁻¹ * (diagUnits2 (A w.1.1) (B w.1.1) * AutomorphicForm.unipotentGL2
        ((((sU (K := K) (L := L) (v := v) σ (qq w.1.1) : Eˣ) : E)) * w.1.2)) *
        AutomorphicForm.sigmaGL K L F σ w.2 := by
    refine ((continuous_snd.inv).mul ((continuous_diagUnits2_prod.comp
      ((hAc.comp (continuous_fst.comp continuous_fst)).prodMk (hBc.comp (continuous_fst.comp continuous_fst)))).mul
      ?_)).mul ((continuous_sigmaGL_r2 (K := K) (L := L) (v := v) σ).comp continuous_snd)
    refine (continuous_unipotentGL2_r2 (K := K) (L := L) (v := v)).comp ?_
    exact (Units.continuous_val.comp (hσc.comp (hqqc.comp (continuous_fst.comp continuous_fst)))).mul
      (continuous_snd.comp continuous_fst)
  haveI hfin : IsFiniteMeasure ((AutomorphicForm.semiLocalHaar K L v).restrict 𝒦) :=
    ⟨by rw [Measure.restrict_apply_univ, AutomorphicForm.semiLocalHaar_semiLocalIntegralSet]; exact ENNReal.one_lt_top⟩
  have hsig : SigmaFinite ((AutomorphicForm.semiLocalHaar K L v).restrict 𝒦) :=
    @IsFiniteMeasure.toSigmaFinite G (AutomorphicForm.glBorelOf E) _ hfin
  have hsf : SFinite ((AutomorphicForm.semiLocalHaar K L v).restrict 𝒦) :=
    @instSFiniteOfSigmaFinite G (AutomorphicForm.glBorelOf E) _ hsig
  have hΦ : StronglyMeasurable fun w : (U × E) × G =>
      φ (w.2⁻¹ * (diagUnits2 (A w.1.1) (B w.1.1) * AutomorphicForm.unipotentGL2
        ((((sU (K := K) (L := L) (v := v) σ (qq w.1.1) : Eˣ) : E)) * w.1.2)) *
        AutomorphicForm.sigmaGL K L F σ w.2) := (hφc.comp hword).stronglyMeasurable
  have hgs : StronglyMeasurable fun y : U × E => ∫ k : G, (fun w : (U × E) × G =>
      φ (w.2⁻¹ * (diagUnits2 (A w.1.1) (B w.1.1) * AutomorphicForm.unipotentGL2
        ((((sU (K := K) (L := L) (v := v) σ (qq w.1.1) : Eˣ) : E)) * w.1.2)) *
        AutomorphicForm.sigmaGL K L F σ w.2)) (y, k) ∂((AutomorphicForm.semiLocalHaar K L v).restrict 𝒦) :=
    @StronglyMeasurable.integral_prod_right' (U × E) G ℂ _ (AutomorphicForm.glBorelOf E)
      ((AutomorphicForm.semiLocalHaar K L v).restrict 𝒦) _ _ hsf _ hΦ
  have hgs' : StronglyMeasurable fun y : U × E => gslice (K := K) (L := L) (v := v) σ φ (A y.1) (B y.1)
      ((((sU (K := K) (L := L) (v := v) σ (qq y.1) : Eˣ) : E)) * y.2) := by
    have heq : (fun y : U × E => gslice (K := K) (L := L) (v := v) σ φ (A y.1) (B y.1)
        ((((sU (K := K) (L := L) (v := v) σ (qq y.1) : Eˣ) : E)) * y.2)) =
      fun y : U × E => ∫ k : G, (fun w : (U × E) × G =>
        φ (w.2⁻¹ * (diagUnits2 (A w.1.1) (B w.1.1) * AutomorphicForm.unipotentGL2
          ((((sU (K := K) (L := L) (v := v) σ (qq w.1.1) : Eˣ) : E)) * w.1.2)) *
          AutomorphicForm.sigmaGL K L F σ w.2)) (y, k) ∂((AutomorphicForm.semiLocalHaar K L v).restrict 𝒦) := by
      funext y; unfold gslice; rfl
    rw [heq]; exact hgs
  have hkern : Measurable fun y : U × E => (kern (K := K) (L := L) (v := v) (qq y.1) y.2 : ℂ) := by
    unfold kern
    refine Complex.measurable_ofReal.comp ?_
    refine Measurable.add ?_ ?_
    · exact (measurable_const.mul (Real.measurable_log.comp
        (continuous_norm.comp (hNc.comp (Units.continuous_val.comp (hqqc.comp continuous_fst)))).measurable))
    · have hTr : Continuous (Algebra.trace F E) := IsModuleTopology.continuous_of_linearMap _
      exact measurable_const.mul (Real.measurable_log.comp ((continuous_norm.comp (hTr.comp continuous_snd)).measurable))
  have hH : StronglyMeasurable fun y : U × E => gslice (K := K) (L := L) (v := v) σ φ (A y.1) (B y.1)
      ((((sU (K := K) (L := L) (v := v) σ (qq y.1) : Eˣ) : E)) * y.2) *
      (kern (K := K) (L := L) (v := v) (qq y.1) y.2 : ℂ) :=
    hgs'.mul hkern.stronglyMeasurable
  have m4 : Measurable fun p : U => ∫ z : E, gslice (K := K) (L := L) (v := v) σ φ (A p) (B p)
      (((sU (K := K) (L := L) (v := v) σ (qq p) : Eˣ) : E) * z) *
      (kern (K := K) (L := L) (v := v) (qq p) z : ℂ) ∂ν :=
    (StronglyMeasurable.integral_prod_right' (ν := ν) hH).measurable
  exact ((m1.mul m2).mul m3).mul m4

end TwLogExp

open scoped TensorProduct TensorProduct.RightActions in
open scoped Classical in
open scoped Pointwise in
set_option maxHeartbeats 16000000 in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hdeg : (Module.finrank K L).Prime)
    (v : HeightOneSpectrum (𝓞 K))
    (φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hφ : AutomorphicForm.IsSemiLocalTestFn K L v φ) :
    ∃ (Λ : (v.adicCompletion K)ˣ → ℂ) (C : ℝ), ∃ U ∈ nhds (1 : (v.adicCompletion K)ˣ),
      ∀ a t : (v.adicCompletion K)ˣ, t ≠ 1 → t ∈ U →
        ∀ α β : (L ⊗[K] (v.adicCompletion K))ˣ,
              AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
                AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a (a * t)) →
            ∀ (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β))
                (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β))),
              @Measure.IsHaarMeasure _ _ _
                (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)) τ' →
              τ' {x | (x : GL (Fin 2) (L ⊗[K] (v.adicCompletion K))) ∈ AutomorphicForm.semiLocalIntegralSet K L v} = 1 →
            ∀ J' : ℂ, AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ (diagUnits2 α β) τ' φ J' →
            ∀ I' : ℂ, AutomorphicForm.IsTwistedOrbitalIntegral K L v σ (diagUnits2 α β) τ' φ I' →
              ‖((AutomorphicForm.LocalWeightedOrbital.ratio (fun x : (v.adicCompletion K) => ‖x‖) a (a * t) *
                  AutomorphicForm.LocalWeightedOrbital.sqrtRatio (fun x : (v.adicCompletion K) => ‖x‖) a (a * t) : ℝ) : ℂ) * J' +
                2 * (Module.finrank K L : ℂ) *
                  ((Real.log ‖(1 : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖ : ℝ) : ℂ) *
                  (((AutomorphicForm.LocalWeightedOrbital.ratio (fun x : (v.adicCompletion K) => ‖x‖) a (a * t) *
                      AutomorphicForm.LocalWeightedOrbital.sqrtRatio (fun x : (v.adicCompletion K) => ‖x‖) a (a * t) : ℝ) : ℂ) * I') -
                Λ a‖ ≤
                C * ‖(1 : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖ * (1 + |Real.log ‖(1 : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖|) := by
  classical
  letI mE : MeasurableSpace (L ⊗[K] v.adicCompletion K) := borel _
  haveI hBE : BorelSpace (L ⊗[K] v.adicCompletion K) := ⟨rfl⟩
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := AutomorphicForm.t2Space_tensor K L (v.adicCompletion K)
  haveI := AutomorphicForm.locallyCompactSpace_tensor K L (v.adicCompletion K)
  obtain ⟨βs, hβm, hβ01, hβprop, hβsec⟩ :=
    AutomorphicForm.exists_torusSection_forall_normString_diagUnits2_eq K L σ hgen v
  obtain ⟨κ, hκ, hA⟩ :=
    AutomorphicForm.exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq
      K L σ hgen v (Measure.addHaar : Measure (L ⊗[K] v.adicCompletion K)) φ hφ
  obtain ⟨Pc, hPc, Z₀, hZ₀, hsupp⟩ := TwLogExp.exists_compact_support (K := K) (L := L) (v := v) σ φ hφ
  obtain ⟨U₁, hU₁, hswap⟩ := TwLogExp.exists_nhds_forall_slice_shift (K := K) (L := L) (v := v) σ φ hφ

  have hAF : ∀ (α β : (L ⊗[K] v.adicCompletion K)ˣ) (a t : (v.adicCompletion K)ˣ) (hat : a ≠ a * t)
      (hN : AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
        AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a (a * t)))
      (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β))
        (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)))
      (hτ' : @Measure.IsHaarMeasure _ _ _
        (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)) τ')
      (h1 : τ' {x | (x : GL (Fin 2) (L ⊗[K] (v.adicCompletion K))) ∈ AutomorphicForm.semiLocalIntegralSet K L v} = 1)
      (c : ℝ) (J' I' : ℂ)
      (hJ' : AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ (diagUnits2 α β) τ' φ J')
      (hI' : AutomorphicForm.IsTwistedOrbitalIntegral K L v σ (diagUnits2 α β) τ' φ I'),
      Integrable (TwLogExp.Fc (K := K) (L := L) (v := v) σ (Measure.addHaar) φ α β βs c)
          ((Measure.addHaar : Measure (L ⊗[K] v.adicCompletion K)).prod Measure.addHaar) ∧
        J' + (c : ℂ) * I' = (κ : ℂ) * ∫ p, TwLogExp.Fc (K := K) (L := L) (v := v) σ (Measure.addHaar) φ α β βs c p
          ∂((Measure.addHaar : Measure (L ⊗[K] v.adicCompletion K)).prod Measure.addHaar) := by
    intro α β a t hat hN τ' hτ' h1 c J' I' hJ' hI'
    exact hA α β a (a * t) hat hN τ' hτ' h1 βs hβm (fun p => (hβ01 p).1) (hβsec α β a (a * t) hat hN τ' hτ' h1)
      c J' I' hJ' hI'

  obtain ⟨M, hM, hφM⟩ := TwLogExp.exists_bound_of_isSemiLocalTestFn (K := K) (L := L) (v := v) φ hφ

  let NE : (L ⊗[K] v.adicCompletion K)ˣ → v.adicCompletion K := fun P => Algebra.norm (v.adicCompletion K) ((P : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K)

  have href : ∀ a : (v.adicCompletion K)ˣ, ∃ P : (L ⊗[K] v.adicCompletion K)ˣ,
      ((∃ P' ∈ Pc, NE P' = (a : v.adicCompletion K)) → P ∈ Pc ∧ NE P = (a : v.adicCompletion K)) := by
    intro a
    by_cases h : ∃ P' ∈ Pc, NE P' = (a : v.adicCompletion K)
    · obtain ⟨P', hP', hN'⟩ := h; exact ⟨P', fun _ => ⟨hP', hN'⟩⟩
    · exact ⟨1, fun h' => absurd h' h⟩
  choose αref hαref using href

  set C₁ : Set (L ⊗[K] v.adicCompletion K)ˣ := Pc⁻¹ * Pc with hC₁
  have hC₁c : IsCompact C₁ := by rw [hC₁]; exact hPc.inv.mul hPc

  obtain ⟨U₂, hU₂c, hU₂n, hU₂sub⟩ : ∃ U₂ : Set (v.adicCompletion K)ˣ, IsCompact U₂ ∧ U₂ ∈ nhds 1 ∧ U₂ ⊆ U₁ := by

    have hA := hU₁
    rw [Units.isEmbedding_val₀.nhds_eq_comap, Filter.mem_comap] at hA
    obtain ⟨Vs, hVs, hsub⟩ := hA
    obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.1 (by simpa using hVs)
    refine ⟨(Units.val : (v.adicCompletion K)ˣ → v.adicCompletion K) ⁻¹' Metric.closedBall (1 : v.adicCompletion K) (min (ε / 2) (1 / 2)),
      ?_, ?_, fun d hd => hsub (hεV ?_)⟩
    · rw [Units.isEmbedding_val₀.isCompact_iff, Set.image_preimage_eq_inter_range]
      have hsub' : Metric.closedBall (1 : v.adicCompletion K) (min (ε / 2) (1 / 2)) ⊆
          Set.range (Units.val : (v.adicCompletion K)ˣ → v.adicCompletion K) := by
        intro x hx
        rw [Metric.mem_closedBall, dist_eq_norm] at hx
        have hx0 : x ≠ 0 := by
          intro h0; rw [h0, zero_sub, norm_neg, norm_one] at hx
          linarith [min_le_right (ε / 2) (1 / 2 : ℝ)]
        exact ⟨Units.mk0 x hx0, rfl⟩
      rw [Set.inter_eq_left.2 hsub']
      exact isCompact_closedBall _ _
    · first
        | simpa using Units.continuous_val.continuousAt.preimage_mem_nhds (Metric.closedBall_mem_nhds _ (by positivity))
        | exact Units.continuous_val.continuousAt.preimage_mem_nhds (Metric.closedBall_mem_nhds _ (by positivity))
        | (have h := Units.continuous_val.continuousAt.preimage_mem_nhds (Metric.closedBall_mem_nhds _ (by positivity))
           simp at h; exact h)
    · have hd' : ‖(d : v.adicCompletion K) - 1‖ ≤ min (ε / 2) (1 / 2) := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hd
      rw [Metric.mem_ball, dist_eq_norm]
      linarith [min_le_left (ε / 2) (1 / 2 : ℝ)]
  set C₂ : Set (L ⊗[K] v.adicCompletion K)ˣ := (TwLogExp.iU (K := K) (L := L) (v := v) '' U₂)⁻¹ * (Pc⁻¹ * Pc) with hC₂
  have hιc : Continuous (TwLogExp.iU (K := K) (L := L) (v := v)) := by
    refine Continuous.units_map _ ?_
    show Continuous fun r : v.adicCompletion K => (Algebra.TensorProduct.includeRight (R := K) (A := L) r : L ⊗[K] v.adicCompletion K)
    have : (fun r : v.adicCompletion K => (Algebra.TensorProduct.includeRight (R := K) (A := L) r : L ⊗[K] v.adicCompletion K)) =
        fun r : v.adicCompletion K => r • (1 : L ⊗[K] v.adicCompletion K) := by
      funext r
      show (algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K)) r = r • (1 : L ⊗[K] v.adicCompletion K)
      exact Algebra.algebraMap_eq_smul_one r
    rw [this]
    haveI : ContinuousSMul (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) := IsModuleTopology.toContinuousSMul _ _
    exact continuous_id.fun_smul continuous_const
  have hC₂c : IsCompact C₂ := by
    rw [hC₂]; exact (hU₂c.image hιc).inv.mul hC₁c
  obtain ⟨D, hDc, hD⟩ := hβprop (C₁ ×ˢ C₂) (hC₁c.prod hC₂c)
  set Qc : Set (L ⊗[K] v.adicCompletion K)ˣ := (fun q : (L ⊗[K] v.adicCompletion K)ˣ × (L ⊗[K] v.adicCompletion K)ˣ => q.2 * q.1⁻¹) '' D with hQc
  have hQcc : IsCompact Qc := by
    rw [hQc]; exact hDc.image (continuous_snd.mul continuous_fst.inv)

  set Z : Set (L ⊗[K] v.adicCompletion K) :=
    (fun w : ((L ⊗[K] v.adicCompletion K)ˣ × (L ⊗[K] v.adicCompletion K)) × (v.adicCompletion K)ˣ =>
      (((TwLogExp.sU (K := K) (L := L) (v := v) σ w.1.1)⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) *
        w.1.2 * (Algebra.TensorProduct.includeRight (R := K) (A := L) ((w.2 : (v.adicCompletion K)ˣ) : v.adicCompletion K) : L ⊗[K] v.adicCompletion K))
      '' ((Qc ×ˢ Z₀) ×ˢ U₂) with hZ
  have hσu : Continuous (TwLogExp.sU (K := K) (L := L) (v := v) σ) := by
    refine Continuous.units_map _ ?_
    exact IsModuleTopology.continuous_of_linearMap
      (TensorProduct.RightActions.AlgebraMap.baseChange K L L (v.adicCompletion K) σ.toAlgHom).toLinearMap
  have hZc : IsCompact Z := by
    rw [hZ]
    refine ((hQcc.prod hZ₀).prod hU₂c).image ?_
    refine ((Units.continuous_val.comp ((hσu.comp (continuous_fst.comp continuous_fst)).inv)).mul
      (continuous_snd.comp continuous_fst)).mul ?_
    exact (Units.continuous_val.comp (hιc.comp continuous_snd))
  obtain ⟨hlogint, C_B, U_B, hU_B, hB⟩ :=
    AutomorphicForm.exists_forall_norm_mul_integral_comp_sigmaTensor_sub_smul_mul_semiLocalWeight_add_sub_integral_mul_log_norm_trace_le
      K L σ hgen v (Measure.addHaar : Measure (L ⊗[K] v.adicCompletion K)) Z hZc Qc hQcc

  have hℓ : 0 < Module.finrank K L := Module.finrank_pos
  set Uu : Set (v.adicCompletion K)ˣ := U₂ ∩ U_B with hUu
  have hUun : Uu ∈ nhds (1 : (v.adicCompletion K)ˣ) := Filter.inter_mem hU₂n hU_B
  obtain hpow := IsDedekindDomain.HeightOneSpectrum.image_pow_mem_nhds_one_units_adicCompletion K v
    (Module.finrank K L) hℓ Uu hUun
  set Uball : Set (v.adicCompletion K)ˣ := {t | ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖ < 1} with hUball
  have hUballn : Uball ∈ nhds (1 : (v.adicCompletion K)ˣ) := by
    have hc : Continuous fun t : (v.adicCompletion K)ˣ => ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖ :=
      continuous_norm.comp (continuous_const.sub Units.continuous_val)
    exact (isOpen_lt hc continuous_const).mem_nhds (by simp)
  set U : Set (v.adicCompletion K)ˣ := Uball ∩ (fun s : (v.adicCompletion K)ˣ => s ^ Module.finrank K L) '' Uu with hU
  have hUn : U ∈ nhds (1 : (v.adicCompletion K)ˣ) := Filter.inter_mem hUballn hpow

  set q_of : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K) → (L ⊗[K] v.adicCompletion K)ˣ :=
    fun p => if h : IsUnit p.1 ∧ IsUnit p.2 then h.2.unit * h.1.unit⁻¹ else 1 with hq_of
  set Λ : (v.adicCompletion K)ˣ → ℂ := fun a =>
    if (∃ P' ∈ Pc, NE P' = (a : v.adicCompletion K)) then
      (κ : ℂ) * ∫ p : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K),
        (if h : IsUnit p.1 ∧ IsUnit p.2 then
          ((‖Algebra.norm (v.adicCompletion K) (p.1 * p.2)‖⁻¹ : ℝ) : ℂ) * (βs p : ℂ) *
            ((‖Algebra.norm (v.adicCompletion K) (((q_of p : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K))‖ : ℝ) : ℂ) *
            ∫ z : L ⊗[K] v.adicCompletion K,
              TwLogExp.gslice (K := K) (L := L) (v := v) σ φ
                  (αref a * TwLogExp.sU (K := K) (L := L) (v := v) σ h.1.unit * h.1.unit⁻¹)
                  (αref a * TwLogExp.sU (K := K) (L := L) (v := v) σ h.2.unit * h.2.unit⁻¹)
                  (((TwLogExp.sU (K := K) (L := L) (v := v) σ (q_of p) : (L ⊗[K] v.adicCompletion K)ˣ) :
                      L ⊗[K] v.adicCompletion K) * z) *
                (TwLogExp.kern (K := K) (L := L) (v := v) (q_of p) z : ℂ) ∂Measure.addHaar
         else 0) ∂((Measure.addHaar : Measure (L ⊗[K] v.adicCompletion K)).prod Measure.addHaar)
    else 0 with hΛ

  obtain ⟨V, hV0, hdomI, hdomV⟩ := TwLogExpR2.exists_V_integrable_dom_and_integral_le (K := K) (L := L) (v := v)
    (Measure.addHaar : Measure (L ⊗[K] v.adicCompletion K)) D hDc βs hβm hβ01
  obtain ⟨NQ, hNQ0, hNQ⟩ : ∃ NQ : ℝ, 0 ≤ NQ ∧ ∀ q ∈ Qc,
      ‖Algebra.norm (v.adicCompletion K) (((q : (L ⊗[K] v.adicCompletion K)ˣ)) : L ⊗[K] v.adicCompletion K)‖ ≤ NQ := by
    have hcont : Continuous fun q : (L ⊗[K] v.adicCompletion K)ˣ =>
        ‖Algebra.norm (v.adicCompletion K) (((q : (L ⊗[K] v.adicCompletion K)ˣ)) : L ⊗[K] v.adicCompletion K)‖ := by
      refine continuous_norm.comp ?_
      have hN : Continuous (Algebra.norm (v.adicCompletion K) : L ⊗[K] v.adicCompletion K → v.adicCompletion K) := by
        let b := Module.finBasis (v.adicCompletion K) (L ⊗[K] v.adicCompletion K)
        have h1 : Continuous fun x : L ⊗[K] v.adicCompletion K => Algebra.leftMulMatrix b x :=
          IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix b).toLinearMap
        have h2 : (Algebra.norm (v.adicCompletion K) : L ⊗[K] v.adicCompletion K → v.adicCompletion K) =
            fun x => (Algebra.leftMulMatrix b x).det := by
          funext x; exact Algebra.norm_eq_matrix_det b x
        rw [h2]; exact h1.matrix_det
      exact hN.comp Units.continuous_val
    obtain ⟨NQ, hNQ⟩ := hQcc.exists_bound_of_continuousOn hcont.continuousOn
    exact ⟨max NQ 0, le_max_right _ _, fun q hq => (by have := hNQ q hq; rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at this; exact this.trans (le_max_left _ _))⟩
  refine ⟨Λ, (κ : ℝ) * V * NQ * M * (max C_B 0) + 0, U, hUn, ?_⟩
  intro a t ht1 htU α β hN τ' hτ' h1 J' hJ' I' hI'
  obtain ⟨htball, u, huU, hut⟩ := htU
  have ht' : ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖ < 1 := htball
  have hat : a ≠ a * t := by
    intro h; exact ht1 (mul_eq_left.1 h.symm)
  set c₀ : ℝ := 2 * (Module.finrank K L : ℝ) * Real.log ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖ with hc₀
  obtain ⟨hintF, hJI⟩ := hAF α β a t hat hN τ' hτ' h1 c₀ J' I' hJ' hI'
  rw [TwLogExp.rs_eq (K := K) (v := v) a t ht']
  have hcomb : ((‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖ : ℝ) : ℂ) * J' +
      2 * (Module.finrank K L : ℂ) *
        ((Real.log ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖ : ℝ) : ℂ) *
        (((‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖ : ℝ) : ℂ) * I') =
      ((‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖ : ℝ) : ℂ) * (J' + (c₀ : ℂ) * I') := by
    rw [hc₀]; push_cast; ring
  rw [hcomb, hJI]
  by_cases hex : ∃ P' ∈ Pc, NE P' = (a : v.adicCompletion K)
  ·
    obtain ⟨hα₀P, hα₀N⟩ := hαref a hex
    set α₀ : (L ⊗[K] v.adicCompletion K)ˣ := αref a with hα₀

    obtain ⟨hNα, hNβ⟩ := TwLogExp.norm_eq_of_normString_diagUnits2 (K := K) (L := L) (v := v) σ hgen α β a (a * t) hN
    have hNιu : Algebra.norm (v.adicCompletion K)
        ((TwLogExp.iU (K := K) (L := L) (v := v) u : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) =
        (t : v.adicCompletion K) := by
      have hut' : u ^ Module.finrank K L = t := hut
      rw [TwLogExp.norm_iU (K := K) (L := L) (v := v) u, ← Units.val_pow_eq_pow_val, hut']
    set β₀ : (L ⊗[K] v.adicCompletion K)ˣ := α₀ * TwLogExp.iU (K := K) (L := L) (v := v) u with hβ₀

    have hα₀N' : Algebra.norm (v.adicCompletion K) ((α₀ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) =
        (a : v.adicCompletion K) := hα₀N
    obtain ⟨c₁, hc₁⟩ := TwLogExp.exists_eq_mul_mul_sU_inv (K := K) (L := L) (v := v) σ hgen α α₀
      (by rw [hNα, hα₀N'])
    have hβ₀N : Algebra.norm (v.adicCompletion K) ((β₀ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) =
        ((a * t : (v.adicCompletion K)ˣ) : v.adicCompletion K) := by
      rw [hβ₀, Units.val_mul, map_mul, hα₀N', hNιu, Units.val_mul]
    obtain ⟨c₂, hc₂⟩ := TwLogExp.exists_eq_mul_mul_sU_inv (K := K) (L := L) (v := v) σ hgen β β₀
      (by rw [hNβ, hβ₀N])

    set S : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K) → ℝ := fun p =>
      βs ((((c₁⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ)) : L ⊗[K] v.adicCompletion K) * p.1,
        (((c₂⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ)) : L ⊗[K] v.adicCompletion K) * p.2) with hS
    have hSm : Measurable S := by
      rw [hS]
      have hm₁ : Measurable fun x : L ⊗[K] v.adicCompletion K =>
          (((c₁⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ)) : L ⊗[K] v.adicCompletion K) * x := (continuous_const.mul continuous_id).measurable
      have hm₂ : Measurable fun x : L ⊗[K] v.adicCompletion K =>
          (((c₂⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ)) : L ⊗[K] v.adicCompletion K) * x := (continuous_const.mul continuous_id).measurable
      exact hβm.comp ((hm₁.comp measurable_fst).prodMk (hm₂.comp measurable_snd))
    have hS0 : ∀ p, 0 ≤ S p := fun p => (hβ01 _).1
    have hSsec : ∀ p : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K), IsUnit p.1 → IsUnit p.2 →
        @integral _ ℝ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)) τ'
          (fun t' => S ((((t' : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0) * p.1,
            (((t' : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1) * p.2)) = 1 := by
      intro p hp1 hp2
      have h := hβsec α β a (a * t) hat hN τ' hτ' h1
        ((((c₁⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ)) : L ⊗[K] v.adicCompletion K) * p.1,
          (((c₂⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ)) : L ⊗[K] v.adicCompletion K) * p.2)
        ((c₁⁻¹).isUnit.mul hp1) ((c₂⁻¹).isUnit.mul hp2)
      rw [hS]
      simp only [mul_left_comm _ (((c₁⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ)) : L ⊗[K] v.adicCompletion K),
        mul_left_comm _ (((c₂⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ)) : L ⊗[K] v.adicCompletion K)] at h ⊢
      exact h
    have hAS : Integrable (TwLogExp.Fc (K := K) (L := L) (v := v) σ Measure.addHaar φ α β S c₀)
          ((Measure.addHaar : Measure (L ⊗[K] v.adicCompletion K)).prod Measure.addHaar) ∧
        J' + (c₀ : ℂ) * I' = (κ : ℂ) * ∫ p, TwLogExp.Fc (K := K) (L := L) (v := v) σ Measure.addHaar φ α β S c₀ p
          ∂((Measure.addHaar : Measure (L ⊗[K] v.adicCompletion K)).prod Measure.addHaar) :=
      hA α β a (a * t) hat hN τ' hτ' h1 S hSm hS0 hSsec c₀ J' I' hJ' hI'
    obtain ⟨hintS, hJIS⟩ := hAS
    obtain ⟨hLC, hLCint⟩ := TwLogExp.integral_Fc_eq_of_eq_mul (K := K) (L := L) (v := v) σ Measure.addHaar φ
      α β α₀ β₀ c₁ c₂ hc₁ hc₂ S c₀
    have hSback : (fun p : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K) =>
        S (((c₁ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) * p.1,
          ((c₂ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) * p.2)) = βs := by
      funext p; rw [hS]; simp [← mul_assoc]
    rw [hSback] at hLC hLCint

    rw [← hJI, hJIS, hLC]

    set β₀ : (L ⊗[K] v.adicCompletion K)ˣ := α₀ * TwLogExp.iU (K := K) (L := L) (v := v) u with hβ₀
    set Fw : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K) → ℂ :=
      TwLogExp.Fc (K := K) (L := L) (v := v) σ Measure.addHaar φ α₀ β₀ βs c₀ with hFw
    set Gref : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K) → ℂ := fun p =>
      (if h : IsUnit p.1 ∧ IsUnit p.2 then
          ((‖Algebra.norm (v.adicCompletion K) (p.1 * p.2)‖⁻¹ : ℝ) : ℂ) * (βs p : ℂ) *
            ((‖Algebra.norm (v.adicCompletion K) (((q_of p : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K))‖ : ℝ) : ℂ) *
            ∫ z : L ⊗[K] v.adicCompletion K,
              TwLogExp.gslice (K := K) (L := L) (v := v) σ φ
                  (αref a * TwLogExp.sU (K := K) (L := L) (v := v) σ h.1.unit * h.1.unit⁻¹)
                  (αref a * TwLogExp.sU (K := K) (L := L) (v := v) σ h.2.unit * h.2.unit⁻¹)
                  (((TwLogExp.sU (K := K) (L := L) (v := v) σ (q_of p) : (L ⊗[K] v.adicCompletion K)ˣ) :
                      L ⊗[K] v.adicCompletion K) * z) *
                (TwLogExp.kern (K := K) (L := L) (v := v) (q_of p) z : ℂ) ∂Measure.addHaar
         else 0) with hGref
    have hΛa : Λ a = (κ : ℂ) * ∫ p, Gref p ∂((Measure.addHaar : Measure (L ⊗[K] v.adicCompletion K)).prod Measure.addHaar) := by
      rw [hΛ]; simp only [hex, if_true, hGref]
    rw [hΛa]
    set ρL : ℝ := ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖ *
      (1 + |Real.log ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖|) with hρL
    have hρL0 : 0 ≤ ρL := by rw [hρL]; positivity
    have hFw_int : Integrable Fw ((Measure.addHaar : Measure (L ⊗[K] v.adicCompletion K)).prod Measure.addHaar) :=
      hLCint hintS
    set dom : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K) → ℝ :=
      TwLogExpR2.dom (K := K) (L := L) (v := v) D βs with hdom
    have hdom_int : Integrable dom ((Measure.addHaar : Measure (L ⊗[K] v.adicCompletion K)).prod Measure.addHaar) := hdomI
    have hdom_V : ∫ p, dom p ∂((Measure.addHaar : Measure (L ⊗[K] v.adicCompletion K)).prod Measure.addHaar) ≤ V := hdomV
    have hpt : ∀ p : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K),
        ‖((‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖ : ℝ) : ℂ) * Fw p - Gref p‖ ≤
          NQ * M * (max C_B 0) * ρL * dom p := by
      intro p
      have hC0 : 0 ≤ NQ * M * (max C_B 0) * ρL := by
        have : 0 ≤ max C_B 0 := le_max_right _ _
        positivity
      by_cases h : IsUnit p.1 ∧ IsUnit p.2
      swap
      · have hF : Fw p = 0 := by rw [hFw]; unfold TwLogExp.Fc; rw [dif_neg h]
        have hG : Gref p = 0 := by rw [hGref]; simp only [dif_neg h]
        have hd : dom p = 0 := by rw [hdom]; unfold TwLogExpR2.dom; rw [dif_neg h]
        rw [hF, hG, hd, mul_zero, sub_zero, norm_zero, mul_zero]

      set p₁ : (L ⊗[K] v.adicCompletion K)ˣ := h.1.unit with hp₁
      set p₂ : (L ⊗[K] v.adicCompletion K)ˣ := h.2.unit with hp₂
      have hdomp : dom p = if (p₁, p₂) ∈ D then ‖Algebra.norm (v.adicCompletion K) (p.1 * p.2)‖⁻¹ * βs p else 0 := by
        rw [hdom]; unfold TwLogExpR2.dom; rw [dif_pos h]
      have hpval : (((p₁ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K),
          ((p₂ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K)) = p :=
        Prod.ext h.1.unit_spec h.2.unit_spec

      set P : (L ⊗[K] v.adicCompletion K)ˣ := α₀ * TwLogExp.sU (K := K) (L := L) (v := v) σ p₁ * p₁⁻¹ with hP
      set Q₀ : (L ⊗[K] v.adicCompletion K)ˣ := β₀ * TwLogExp.sU (K := K) (L := L) (v := v) σ p₂ * p₂⁻¹ with hQ₀
      set Qr : (L ⊗[K] v.adicCompletion K)ˣ := α₀ * TwLogExp.sU (K := K) (L := L) (v := v) σ p₂ * p₂⁻¹ with hQr
      have hFwp : Fw p = ((‖Algebra.norm (v.adicCompletion K) (p.1 * p.2)‖⁻¹ : ℝ) : ℂ) * (βs p : ℂ) *
          ∫ ξ : L ⊗[K] v.adicCompletion K,
            TwLogExp.gslice (K := K) (L := L) (v := v) σ φ P Q₀
              (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ ξ -
                (((Q₀ * P⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ)) : L ⊗[K] v.adicCompletion K) * ξ) *
            ((AutomorphicForm.semiLocalWeight K L v (AutomorphicForm.unipotentGL2 ξ) + c₀ : ℝ) : ℂ) ∂Measure.addHaar := by
        rw [hFw]; unfold TwLogExp.Fc; rw [dif_pos h]
      have hGp : Gref p = ((‖Algebra.norm (v.adicCompletion K) (p.1 * p.2)‖⁻¹ : ℝ) : ℂ) * (βs p : ℂ) *
          ((‖Algebra.norm (v.adicCompletion K) (((q_of p : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K))‖ : ℝ) : ℂ) *
          ∫ z : L ⊗[K] v.adicCompletion K,
            TwLogExp.gslice (K := K) (L := L) (v := v) σ φ P Qr
              (((TwLogExp.sU (K := K) (L := L) (v := v) σ (q_of p) : (L ⊗[K] v.adicCompletion K)ˣ) :
                  L ⊗[K] v.adicCompletion K) * z) *
            (TwLogExp.kern (K := K) (L := L) (v := v) (q_of p) z : ℂ) ∂Measure.addHaar := by
        rw [hGref]; simp only [dif_pos h]; rfl
      by_cases hpD : (p₁, p₂) ∈ D
      ·
        set q : (L ⊗[K] v.adicCompletion K)ˣ := p₂ * p₁⁻¹ with hq
        have hq_ofp : q_of p = q := by rw [hq_of]; simp only [dif_pos h]; rfl
        have hqQc : q ∈ Qc := by rw [hQc]; exact ⟨(p₁, p₂), hpD, rfl⟩
        have hNq : ‖Algebra.norm (v.adicCompletion K) ((q : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K)‖ ≤ NQ :=
          hNQ q hqQc
        have hdp : dom p = ‖Algebra.norm (v.adicCompletion K) (p.1 * p.2)‖⁻¹ * βs p := by rw [hdomp, if_pos hpD]
        have hQP : Q₀ * P⁻¹ = TwLogExp.iU (K := K) (L := L) (v := v) u *
            (TwLogExp.sU (K := K) (L := L) (v := v) σ q * q⁻¹) := by
          rw [hQ₀, hP, hβ₀, hq]; exact TwLogExp.quot_eq (K := K) (L := L) (v := v) σ α₀ p₁ p₂ u
        have hul : u ^ Module.finrank K L ≠ 1 := fun h1' => ht1 (by have hut' : u ^ Module.finrank K L = t := hut; rw [← hut', h1'])
        have hut2 : (((u ^ Module.finrank K L : (v.adicCompletion K)ˣ)) : v.adicCompletion K) = (t : v.adicCompletion K) := by
          have hut' : u ^ Module.finrank K L = t := hut
          rw [hut']
        have hu1 : ‖(u : v.adicCompletion K)‖ = 1 := by
          have htn : ‖(t : v.adicCompletion K)‖ = 1 := by
            have hh : ‖(t : v.adicCompletion K) - 1‖ < ‖(1 : v.adicCompletion K)‖ := by rw [norm_sub_rev, norm_one]; exact ht'
            have := TwLogExp.norm_eq_of_norm_sub_lt'' hh
            rwa [norm_one] at this
          rw [← hut2, Units.val_pow_eq_pow_val, norm_pow] at htn
          exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (Module.finrank_pos).ne').1 htn

        set g : L ⊗[K] v.adicCompletion K → ℂ := fun z => ((M⁻¹ : ℝ) : ℂ) *
          TwLogExp.gslice (K := K) (L := L) (v := v) σ φ P Q₀
            (((TwLogExp.sU (K := K) (L := L) (v := v) σ q : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) * z) with hg
        have hgm : Measurable g := by
          rw [hg]
          exact (TwLogExp.measurable_gslice_comp (K := K) (L := L) (v := v) σ φ hφ P Q₀ _).const_mul _
        have hg1 : ∀ z, ‖g z‖ ≤ 1 := by
          intro z
          rw [hg]; beta_reduce
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hM)]
          calc M⁻¹ * ‖TwLogExp.gslice (K := K) (L := L) (v := v) σ φ P Q₀ _‖ ≤ M⁻¹ * M :=
                mul_le_mul_of_nonneg_left (TwLogExp.norm_gslice_le (K := K) (L := L) (v := v) σ φ M hφM P Q₀ _)
                  (inv_pos.2 hM).le
            _ = 1 := inv_mul_cancel₀ hM.ne'
        have hgZ : ∀ z, z ∉ Z → g z = 0 := by
          intro z hz
          rw [hg]
          by_cases hgs : TwLogExp.gslice (K := K) (L := L) (v := v) σ φ P Q₀
              (((TwLogExp.sU (K := K) (L := L) (v := v) σ q : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) * z) = 0
          · beta_reduce; rw [hgs, mul_zero]
          · exfalso
            apply hz
            have hz₀ : (((TwLogExp.sU (K := K) (L := L) (v := v) σ q : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) * z) ∈ Z₀ := by
              by_contra hnz
              exact hgs (TwLogExp.gslice_eq_zero_of_not (K := K) (L := L) (v := v) σ φ Pc Z₀ hsupp P Q₀ _ (fun hh => hnz hh.2.2))
            rw [hZ]
            refine ⟨((q, ((TwLogExp.sU (K := K) (L := L) (v := v) σ q : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) * z), 1),
              Set.mk_mem_prod (Set.mk_mem_prod hqQc hz₀) (mem_of_mem_nhds hU₂n), ?_⟩
            simp only [map_one, Units.val_one, mul_one]
            rw [← mul_assoc, Units.inv_mul, one_mul]
        obtain ⟨hB1, -⟩ := hB u huU.2 hul q hqQc g hgm hg1 hgZ
        rw [hut2] at hB1
        have hinner := TwLogExp.inner_eq_norm_mul_M_mul (K := K) (L := L) (v := v) σ Measure.addHaar φ P Q₀ q u hQP c₀ M hM
        have hQ₀r : Q₀ = Qr * TwLogExp.iU (K := K) (L := L) (v := v) u := by
          rw [hQ₀, hQr, hβ₀, mul_right_comm α₀ (TwLogExp.iU (K := K) (L := L) (v := v) u), mul_right_comm (α₀ * TwLogExp.sU (K := K) (L := L) (v := v) σ p₂) (TwLogExp.iU (K := K) (L := L) (v := v) u) p₂⁻¹]
        have hY := TwLogExp.refIntegral_eq_M_mul (K := K) (L := L) (v := v) σ Measure.addHaar φ P Qr q u hu1
          (fun P' Q' z k hk => hswap u (hU₂sub huU.1) P' Q' z k hk) M hM
        rw [← hQ₀r] at hY

        rw [hFwp, hGp, hq_ofp, hinner, hY, hdp, hc₀]
        refine TwLogExp.perp_numeric _ _ _ NQ M C_B ρL _ _ _ (inv_nonneg.2 (norm_nonneg _)) (hβ01 p).1
          (norm_nonneg _) hNq hM hρL0 ?_
        rw [hρL, ← mul_assoc]
        exact hB1
      ·
        have hd0 : dom p = 0 := by rw [hdomp, if_neg hpD]
        rw [hd0, mul_zero]
        by_cases hβ0 : βs p = 0
        · rw [hFwp, hGp, hβ0]; simp
        · have hnotC : ¬ ((TwLogExp.sU (K := K) (L := L) (v := v) σ p₁ * p₁⁻¹,
              TwLogExp.sU (K := K) (L := L) (v := v) σ p₂ * p₂⁻¹) ∈ C₁ ×ˢ C₂) := by
            intro hC
            exact hpD (hD (p₁, p₂) (by rw [hpval]; exact hβ0) hC)
          rw [Set.mem_prod, not_and_or] at hnotC
          have h1U₂ : (1 : (v.adicCompletion K)ˣ) ∈ U₂ := mem_of_mem_nhds hU₂n

          have hvan : (∀ z, TwLogExp.gslice (K := K) (L := L) (v := v) σ φ P Q₀ z = 0) ∧
              (∀ z, TwLogExp.gslice (K := K) (L := L) (v := v) σ φ P Qr z = 0) := by
            rcases hnotC with h₁ | h₂
            · have hPn : P ∉ Pc := by
                intro hPm
                apply h₁
                rw [hC₁]
                refine ⟨α₀⁻¹, Set.inv_mem_inv.2 hα₀P, P, hPm, ?_⟩
                rw [hP]; group
              exact ⟨fun z => TwLogExp.gslice_eq_zero_of_not (K := K) (L := L) (v := v) σ φ Pc Z₀ hsupp P Q₀ z
                  (fun hh => hPn hh.1),
                fun z => TwLogExp.gslice_eq_zero_of_not (K := K) (L := L) (v := v) σ φ Pc Z₀ hsupp P Qr z
                  (fun hh => hPn hh.1)⟩
            · have hQ₀n : Q₀ ∉ Pc := by
                intro hQm
                apply h₂
                rw [hC₂]
                refine ⟨(TwLogExp.iU (K := K) (L := L) (v := v) u)⁻¹, Set.inv_mem_inv.2 ⟨u, huU.1, rfl⟩,
                  α₀⁻¹ * Q₀, ⟨α₀⁻¹, Set.inv_mem_inv.2 hα₀P, Q₀, hQm, rfl⟩, ?_⟩
                rw [hQ₀, hβ₀]; group
              have hQrn : Qr ∉ Pc := by
                intro hQm
                apply h₂
                rw [hC₂]
                refine ⟨(TwLogExp.iU (K := K) (L := L) (v := v) 1)⁻¹, Set.inv_mem_inv.2 ⟨1, h1U₂, rfl⟩,
                  α₀⁻¹ * Qr, ⟨α₀⁻¹, Set.inv_mem_inv.2 hα₀P, Qr, hQm, rfl⟩, ?_⟩
                rw [hQr, map_one]; group
              exact ⟨fun z => TwLogExp.gslice_eq_zero_of_not (K := K) (L := L) (v := v) σ φ Pc Z₀ hsupp P Q₀ z
                  (fun hh => hQ₀n hh.2.1),
                fun z => TwLogExp.gslice_eq_zero_of_not (K := K) (L := L) (v := v) σ φ Pc Z₀ hsupp P Qr z
                  (fun hh => hQrn hh.2.1)⟩
          rw [hFwp, hGp]
          simp only [hvan.1, hvan.2, zero_mul, integral_zero, mul_zero, sub_zero, norm_zero, le_refl]
    have hGref_meas : AEStronglyMeasurable Gref ((Measure.addHaar : Measure (L ⊗[K] v.adicCompletion K)).prod Measure.addHaar) := by
      rw [hGref]
      exact (TwLogExp.measurable_Gref (K := K) (L := L) (v := v) σ Measure.addHaar φ hφ (αref a) βs hβm q_of
        (fun p h => by rw [hq_of]; exact dif_pos h)).aestronglyMeasurable
    have hGref_int : Integrable Gref ((Measure.addHaar : Measure (L ⊗[K] v.adicCompletion K)).prod Measure.addHaar) := by
      have hΔ : Integrable (fun p => ((‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖ : ℝ) : ℂ) * Fw p - Gref p)
          ((Measure.addHaar : Measure (L ⊗[K] v.adicCompletion K)).prod Measure.addHaar) :=
        Integrable.mono' (hdom_int.const_mul (NQ * M * (max C_B 0) * ρL))
          ((hFw_int.const_mul _).aestronglyMeasurable.sub hGref_meas) (Filter.Eventually.of_forall hpt)
      have := (hFw_int.const_mul (((‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖ : ℝ) : ℂ))).sub hΔ
      refine this.congr (Filter.Eventually.of_forall fun p => ?_)
      simp only [Pi.sub_apply, sub_sub_cancel]
    have hdiff : ((‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖ : ℝ) : ℂ) *
          ((κ : ℂ) * ∫ p, Fw p ∂((Measure.addHaar : Measure (L ⊗[K] v.adicCompletion K)).prod Measure.addHaar)) -
          (κ : ℂ) * ∫ p, Gref p ∂((Measure.addHaar : Measure (L ⊗[K] v.adicCompletion K)).prod Measure.addHaar) =
        (κ : ℂ) * ∫ p, (((‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖ : ℝ) : ℂ) * Fw p - Gref p)
          ∂((Measure.addHaar : Measure (L ⊗[K] v.adicCompletion K)).prod Measure.addHaar) := by
      rw [integral_sub (hFw_int.const_mul _) hGref_int, integral_const_mul]
      ring
    rw [hdiff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ]
    calc κ * ‖∫ p, (((‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖ : ℝ) : ℂ) * Fw p - Gref p)
            ∂((Measure.addHaar : Measure (L ⊗[K] v.adicCompletion K)).prod Measure.addHaar)‖
        ≤ κ * ∫ p, NQ * M * (max C_B 0) * ρL * dom p
            ∂((Measure.addHaar : Measure (L ⊗[K] v.adicCompletion K)).prod Measure.addHaar) := by
          refine mul_le_mul_of_nonneg_left ?_ hκ.le
          exact norm_integral_le_of_norm_le (hdom_int.const_mul _) (Filter.Eventually.of_forall hpt)
      _ = κ * (NQ * M * (max C_B 0) * ρL) * ∫ p, dom p
            ∂((Measure.addHaar : Measure (L ⊗[K] v.adicCompletion K)).prod Measure.addHaar) := by
          rw [integral_const_mul]; ring
      _ ≤ κ * (NQ * M * (max C_B 0) * ρL) * V := by
          refine mul_le_mul_of_nonneg_left hdom_V ?_
          have : 0 ≤ max C_B 0 := le_max_right _ _
          positivity
      _ = (κ * V * NQ * M * (max C_B 0) + 0) * ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖ *
            (1 + |Real.log ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖|) := by
          rw [hρL]; ring
  ·
    have hF0 : (fun p => TwLogExp.Fc (K := K) (L := L) (v := v) σ Measure.addHaar φ α β βs c₀ p) = fun _ => 0 := by
      funext p
      exact TwLogExp.Fc_eq_zero_of_not_exists (K := K) (L := L) (v := v) σ hgen Measure.addHaar φ Pc Z₀ hsupp α β a (a * t) hN hex βs c₀ p
    have hΛ0 : Λ a = 0 := by rw [hΛ]; simp only [hex, if_false]
    rw [hF0, integral_zero, mul_zero, mul_zero, hΛ0, sub_zero, norm_zero]
    positivity

end S_AutomorphicForm_exists_forall_norm_ratio_mul_sqrtRatio_mul_twistedWeighted_add_mul_log_mul_twistedOrbital_sub_le_of_normString_diagUnits2_eq
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_norm_ratio_mul_sqrtRatio_mul_twistedWeighted_add_mul_log_mul_twistedOrbital_sub_le_of_normString_diagUnits2_eq (solution)
