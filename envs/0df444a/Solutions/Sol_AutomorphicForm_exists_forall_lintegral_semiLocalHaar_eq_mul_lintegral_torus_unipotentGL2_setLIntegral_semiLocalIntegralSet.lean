-- Prove2me | solution 1 for AutomorphicForm.exists_forall_lintegral_semiLocalHaar_eq_mul_lintegral_torus_unipotentGL2_setLIntegral_semiLocalIntegralSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/18b8bd99-a164-5720-81a3-508ee1f2cc87

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_ConstantTerm
import Theorems.Thm_NumberField_AdicCompletion_map_linearMap_eq_norm_det_inv_smul_of_isAddHaarMeasure
import Theorems.Thm_AutomorphicForm_mem_semiLocalIntegralSet_iff_and_semiLocalHaar_doubleCoset_localEmbed_eq_localHaar_and_map_baseChangeAlgEquiv_eq_smul_pi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_AutomorphicForm_exists_forall_lintegral_semiLocalHaar_eq_mul_lintegral_torus_unipotentGL2_setLIntegral_semiLocalIntegralSet
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

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

section Module

variable [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
variable (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure]

def wt (e : E) : ℝ≥0∞ := ENNReal.ofReal ‖Algebra.norm F e‖

theorem wt_mul (a b : E) : wt (K := K) (L := L) (v := v) (a * b) = wt a * wt b := by
  simp only [wt, map_mul, norm_mul]
  exact ENNReal.ofReal_mul (norm_nonneg _)

theorem wt_ne_zero {a : E} (ha : IsUnit a) : wt (K := K) (L := L) (v := v) a ≠ 0 := by
  simp only [wt, ne_eq, ENNReal.ofReal_eq_zero, not_le, norm_pos_iff]
  exact (isUnit_iff_norm_ne_zero a).1 ha

theorem wt_ne_top (a : E) : wt (K := K) (L := L) (v := v) a ≠ ⊤ := ENNReal.ofReal_ne_top

theorem map_mul_left {a : E} (ha : IsUnit a) :
    Measure.map (fun x : E => a * x) ν = (wt a)⁻¹ • ν := by
  have hdet : LinearMap.det (Algebra.lmul F E a) = Algebra.norm F a := (Algebra.norm_apply F a).symm
  have hne : LinearMap.det (Algebra.lmul F E a) ≠ 0 := by
    rw [hdet]; exact (isUnit_iff_norm_ne_zero a).1 ha
  have h := NumberField.AdicCompletion.map_linearMap_eq_norm_det_inv_smul_of_isAddHaarMeasure K v E ν
    (Algebra.lmul F E a) hne
  rw [hdet] at h
  have hfun : ((Algebra.lmul F E a : E →ₗ[F] E) : E → E) = fun x => a * x := by
    funext x; rw [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']
  rw [hfun] at h
  rw [h, wt, ENNReal.ofReal_inv_of_pos (norm_pos_iff.2 ((isUnit_iff_norm_ne_zero a).1 ha))]

theorem lintegral_comp_mul_left (H : E → ℝ≥0∞) (hH : Measurable H) {a : E} (ha : IsUnit a) :
    ∫⁻ y, H (a * y) ∂ν = (wt a)⁻¹ * ∫⁻ y, H y ∂ν := by
  rw [← lintegral_map hH (measurable_const_mul a), map_mul_left ν ha, lintegral_smul_measure, smul_eq_mul]

end Module

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

section Meas

variable [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]

theorem borelSpace_Q : BorelSpace Q := inferInstance

theorem measurableSet_goodT : MeasurableSet (goodT : Set Q) := isOpen_goodT.measurableSet

theorem measurable_uGL : Measurable (uGL : Q → G) := by
  refine measurable_of_restrict_of_restrict_compl measurableSet_goodT ?_ ?_
  · exact continuous_uGL_restrict.measurable
  · have : (goodTᶜ : Set Q).domRestrict (uGL : Q → G) = fun _ => 1 := by
      funext x
      have hx : ¬ IsUnit (tm (x : Q)).det := x.2
      simp [Set.domRestrict_apply, uGL, hx]
    rw [this]; exact measurable_const

theorem measurable_nGL : Measurable (nGL : E → G) := continuous_nGL.measurable

theorem measurable_ι : Measurable (ι : Q × E → G) :=
  (measurable_uGL.comp measurable_fst).mul (measurable_nGL.comp measurable_snd)

end Meas

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

variable [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]

theorem measurableSet_K : MeasurableSet (𝒦 : Set G) := isOpen_K.measurableSet

theorem muK : μG 𝒦 = 1 := AutomorphicForm.semiLocalHaar_semiLocalIntegralSet K L v

theorem isLocallyFiniteMeasure_μ : IsLocallyFiniteMeasure μG := isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
theorem sigmaFinite_μ : SigmaFinite μG := by
  haveI := isLocallyFiniteMeasure_μ (K := K) (L := L) (v := v)
  exact MeasureTheory.sigmaFinite_of_locallyFinite
theorem sFinite_μ : SFinite μG := by haveI := sigmaFinite_μ (K := K) (L := L) (v := v); infer_instance

attribute [local instance] sigmaFinite_μ sFinite_μ

theorem map_mul_right_K {k : G} (hk : k ∈ 𝒦) : Measure.map (fun g : G => g * k) μG = μG := by
  have h := Measure.isMulLeftInvariant_eq_smul (Measure.map (fun g : G => g * k) μG) μG
  set c := Measure.haarScalarFactor (Measure.map (fun g : G => g * k) μG) μG with hc
  have hpre : (fun g : G => g * k) ⁻¹' (𝒦 : Set G) = 𝒦 := by
    ext g; exact K_mul_mem_iff_right hk
  have h1 : (Measure.map (fun g : G => g * k) μG) 𝒦 = (c : ℝ≥0∞) * μG 𝒦 := by
    conv_lhs => rw [h]
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  rw [Measure.map_apply (measurable_mul_const k) measurableSet_K, hpre, muK, mul_one] at h1
  have hc1 : c = 1 := ENNReal.coe_eq_one.1 h1.symm
  rw [h, hc1, one_smul]

theorem lintegral_mul_right_K (f : G → ℝ≥0∞) (hf : Measurable f) {k : G} (hk : k ∈ 𝒦) :
    ∫⁻ g, f (g * k) ∂μG = ∫⁻ g, f g ∂μG := by
  rw [← lintegral_map hf (measurable_mul_const k), map_mul_right_K hk]

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
    ext i j w : 2
    have h := congrArg (fun m : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L) => m i j)
      (show ((kw w : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) _) * (((kw w)⁻¹ : GL (Fin 2) _) : Matrix _ _ _) = 1
        by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
    simp only [Matrix.mul_apply, Fin.sum_univ_two] at h ⊢
    simpa [M, M', Matrix.one_apply, ite_apply, Pi.one_apply, Pi.zero_apply] using h
  have hM'M : M' * M = 1 := by
    ext i j w : 2
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
    ext i j : 1
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

section Main

variable [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
variable (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure]

open scoped Classical

attribute [local instance] borelSpace_Q sigmaFinite_μ sFinite_μ

local notation "ν²" => Measure.prod ν ν
local notation "ζ" => Measure.prod (Measure.prod ν ν) ν

def Dr (p : Q) : ℝ := if p ∈ goodT then ‖Algebra.norm F (p.1 * p.2)‖⁻¹ else 0

def D (p : Q) : ℝ≥0∞ := ENNReal.ofReal (Dr p)

theorem Dr_of_mem {p : Q} (hp : p ∈ goodT) : Dr (K := K) (L := L) (v := v) p = ‖Algebra.norm F (p.1 * p.2)‖⁻¹ := by
  simp [Dr, hp]

theorem Dr_of_not {p : Q} (hp : p ∉ goodT) : Dr (K := K) (L := L) (v := v) p = 0 := by
  simp [Dr, hp]

theorem D_of_mem {p : Q} (hp : p ∈ goodT) : D (K := K) (L := L) (v := v) p = ENNReal.ofReal ‖Algebra.norm F (p.1 * p.2)‖⁻¹ := by
  rw [D, Dr_of_mem hp]

theorem D_of_not {p : Q} (hp : p ∉ goodT) : D (K := K) (L := L) (v := v) p = 0 := by
  rw [D, Dr_of_not hp, ENNReal.ofReal_zero]

theorem D_pos_of_mem {p : Q} (hp : p ∈ goodT) : 0 < D (K := K) (L := L) (v := v) p := by
  rw [D_of_mem hp, ENNReal.ofReal_pos, inv_pos, norm_pos_iff]
  have h := (mem_goodT_iff p).1 hp
  exact (isUnit_iff_norm_ne_zero _).1 (h.1.mul h.2)

theorem measurable_Dr : Measurable (Dr : Q → ℝ) := by
  refine Measurable.ite measurableSet_goodT ?_ measurable_const
  exact ((continuous_algebraNorm.comp (continuous_fst.mul continuous_snd)).norm).measurable.inv

theorem measurable_D : Measurable (D : Q → ℝ≥0∞) := ENNReal.measurable_ofReal.comp measurable_Dr

theorem D_ne_top (p : Q) : D (K := K) (L := L) (v := v) p ≠ ⊤ := ENNReal.ofReal_ne_top

theorem D_smul {a : Q} (ha : a ∈ goodT) (q : Q) :
    D (K := K) (L := L) (v := v) (a.1 * q.1, a.2 * q.2) =
      ENNReal.ofReal ‖Algebra.norm F (a.1 * a.2)‖⁻¹ * D q := by
  by_cases hq : q ∈ goodT
  · have haq : ((a.1 * q.1, a.2 * q.2) : Q) ∈ goodT := by
      rw [mem_goodT_iff] at ha hq ⊢; exact ⟨ha.1.mul hq.1, ha.2.mul hq.2⟩
    rw [D_of_mem haq, D_of_mem hq, ← ENNReal.ofReal_mul (inv_nonneg.2 (norm_nonneg _))]
    congr 1
    have : a.1 * q.1 * (a.2 * q.2) = (a.1 * a.2) * (q.1 * q.2) := by ring
    rw [this, map_mul, norm_mul, mul_inv]
  · have haq : ((a.1 * q.1, a.2 * q.2) : Q) ∉ goodT := by
      intro h; apply hq
      rw [mem_goodT_iff] at ha h ⊢
      exact ⟨(IsUnit.mul_iff.1 h.1).2, (IsUnit.mul_iff.1 h.2).2⟩
    rw [D_of_not haq, D_of_not hq, mul_zero]

theorem wt_mul_wt_mul_ofReal_inv {a : Q} (ha : a ∈ goodT) :
    wt (K := K) (L := L) (v := v) a.1 * wt a.2 * ENNReal.ofReal ‖Algebra.norm F (a.1 * a.2)‖⁻¹ = 1 := by
  have h := (mem_goodT_iff a).1 ha
  have hpos : 0 < ‖Algebra.norm F (a.1 * a.2)‖ :=
    norm_pos_iff.2 ((isUnit_iff_norm_ne_zero _).1 (h.1.mul h.2))
  rw [← wt_mul, wt, ← ENNReal.ofReal_mul (norm_nonneg _), mul_inv_cancel₀ hpos.ne', ENNReal.ofReal_one]

theorem lintegral_comp_smul (H : Q → ℝ≥0∞) (hH : Measurable H) {a : Q} (ha : a ∈ goodT) :
    ∫⁻ p, H (a.1 * p.1, a.2 * p.2) ∂ν² = (wt a.1)⁻¹ * (wt a.2)⁻¹ * ∫⁻ p, H p ∂ν² := by
  have h := (mem_goodT_iff a).1 ha
  have hact : Measurable fun p : Q => ((a.1 * p.1, a.2 * p.2) : Q) :=
    (measurable_fst.const_mul a.1).prodMk (measurable_snd.const_mul a.2)
  have hm : Measurable fun p : Q => H (a.1 * p.1, a.2 * p.2) := hH.comp hact
  have h1 : ∫⁻ p, H (a.1 * p.1, a.2 * p.2) ∂ν² = ∫⁻ x, ∫⁻ y, H (a.1 * x, a.2 * y) ∂ν ∂ν := by
    rw [lintegral_prod _ hm.aemeasurable]
  have h2 : ∀ x : E, ∫⁻ y, H (a.1 * x, a.2 * y) ∂ν = (wt a.2)⁻¹ * ∫⁻ y, H (a.1 * x, y) ∂ν := by
    intro x
    exact lintegral_comp_mul_left ν (fun y => H (a.1 * x, y)) (hH.comp (measurable_const.prodMk measurable_id)) h.2
  have h3 : Measurable fun x : E => ∫⁻ y, H (x, y) ∂ν := hH.lintegral_prod_right'
  have h4 : ∫⁻ x, ∫⁻ y, H (a.1 * x, y) ∂ν ∂ν = (wt a.1)⁻¹ * ∫⁻ x, ∫⁻ y, H (x, y) ∂ν ∂ν :=
    lintegral_comp_mul_left ν (fun x => ∫⁻ y, H (x, y) ∂ν) h3 h.1
  rw [h1]
  simp_rw [h2]
  rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 (wt_ne_zero h.2)), h4,
    lintegral_prod _ hH.aemeasurable, ← mul_assoc, mul_comm ((wt _)⁻¹)]

def indK (g : G) : ℝ≥0∞ := (𝒦 : Set G).indicator (fun _ => (1 : ℝ≥0∞)) g

theorem indK_of_mem {g : G} (hg : g ∈ 𝒦) : indK (K := K) (L := L) (v := v) g = 1 := by
  simp [indK, hg]

theorem indK_of_not {g : G} (hg : g ∉ 𝒦) : indK (K := K) (L := L) (v := v) g = 0 := by
  simp [indK, hg]

theorem measurable_indK : Measurable (indK : G → ℝ≥0∞) := measurable_one.indicator measurableSet_K

theorem lintegral_indK : ∫⁻ g, indK (K := K) (L := L) (v := v) g ∂μG = 1 := by
  show ∫⁻ g, (𝒦 : Set G).indicator (fun _ => (1 : ℝ≥0∞)) g ∂μG = 1
  rw [lintegral_indicator_const measurableSet_K, muK, mul_one]

theorem indK_congr {g h : G} (hgh : g ∈ 𝒦 ↔ h ∈ 𝒦) : indK (K := K) (L := L) (v := v) g = indK h := by
  by_cases hg : g ∈ 𝒦
  · rw [indK_of_mem hg, indK_of_mem (hgh.1 hg)]
  · rw [indK_of_not hg, indK_of_not (fun hh => hg (hgh.2 hh))]

def V (g : G) : ℝ≥0∞ := ∫⁻ z, D z.1 * indK ((ι z)⁻¹ * g) ∂ζ

def Λ : ℝ≥0∞ := ∫⁻ z, D z.1 * indK (ι z) ∂ζ

theorem Λ_eq_lintegral_lintegral :
    Λ ν = ∫⁻ p, D p * ∫⁻ x, indK (K := K) (L := L) (v := v) (ι (p, x)) ∂ν ∂ν² := by
  have hm : Measurable fun z : Q × E => D z.1 * indK (K := K) (L := L) (v := v) (ι z) :=
    (measurable_D.comp measurable_fst).mul (measurable_indK.comp measurable_ι)
  rw [Λ, lintegral_prod _ hm.aemeasurable]
  refine lintegral_congr fun p => ?_
  have hmx : Measurable fun x : E => indK (K := K) (L := L) (v := v) (ι (p, x)) :=
    measurable_indK.comp (measurable_ι.comp (measurable_const.prodMk measurable_id))
  dsimp only
  rw [lintegral_const_mul _ hmx]

theorem V_eq_Λ (g : G) : V ν g = Λ ν := by
  obtain ⟨a, ha, c, k, hk, rfl⟩ := iwasawa g
  have haU := (mem_goodT_iff a).1 ha

  have h0 : ∀ z : Q × E, indK (K := K) (L := L) (v := v) ((ι z)⁻¹ * (uGL a * nGL c * k)) =
      indK ((ι z)⁻¹ * (uGL a * nGL c)) := by
    intro z
    apply indK_congr
    rw [← mul_assoc]
    exact K_mul_mem_iff_right hk
  have hmz : Measurable fun z : Q × E => D z.1 * indK (K := K) (L := L) (v := v) ((ι z)⁻¹ * (uGL a * nGL c)) :=
    (measurable_D.comp measurable_fst).mul (measurable_indK.comp ((measurable_ι.inv).mul_const _))

  set J : Q → ℝ≥0∞ := fun p => ∫⁻ x, indK (K := K) (L := L) (v := v) ((ι (p, x))⁻¹ * (uGL a * nGL c)) ∂ν with hJ
  have hJm : Measurable J := by
    have : Measurable fun z : Q × E => indK (K := K) (L := L) (v := v) ((ι z)⁻¹ * (uGL a * nGL c)) :=
      measurable_indK.comp ((measurable_ι.inv).mul_const _)
    exact this.lintegral_prod_right'
  have h1 : V ν (uGL a * nGL c * k) = ∫⁻ p, D p * J p ∂ν² := by
    rw [V]
    simp_rw [h0]
    rw [lintegral_prod _ hmz.aemeasurable]
    refine lintegral_congr fun p => ?_
    have hmx : Measurable fun x : E => indK (K := K) (L := L) (v := v) ((ι (p, x))⁻¹ * (uGL a * nGL c)) :=
      measurable_indK.comp (((measurable_ι.comp (measurable_const.prodMk measurable_id)).inv).mul_const _)
    dsimp only
    rw [lintegral_const_mul _ hmx]

  have h2 : ∫⁻ p, D p * J p ∂ν² = wt (K := K) (L := L) (v := v) a.1 * wt a.2 *
      ∫⁻ q, D (a.1 * q.1, a.2 * q.2) * J (a.1 * q.1, a.2 * q.2) ∂ν² := by
    rw [lintegral_comp_smul ν (fun p => D p * J p) (measurable_D.mul hJm) ha, ← mul_assoc,
      show wt (K := K) (L := L) (v := v) a.1 * wt a.2 * ((wt a.1)⁻¹ * (wt a.2)⁻¹) = 1 by
        rw [mul_mul_mul_comm, ENNReal.mul_inv_cancel (wt_ne_zero haU.1) (wt_ne_top _),
          ENNReal.mul_inv_cancel (wt_ne_zero haU.2) (wt_ne_top _), one_mul], one_mul]

  have h3 : ∀ q : Q, D (K := K) (L := L) (v := v) (a.1 * q.1, a.2 * q.2) * J (a.1 * q.1, a.2 * q.2) =
      ENNReal.ofReal ‖Algebra.norm F (a.1 * a.2)‖⁻¹ * (D q * ∫⁻ x, indK (K := K) (L := L) (v := v) (ι (q, x)) ∂ν) := by
    intro q
    rw [D_smul ha, mul_assoc]
    by_cases hq : q ∈ goodT
    · congr 2
      have haq : ((a.1 * q.1, a.2 * q.2) : Q) ∈ goodT := by
        rw [mem_goodT_iff] at hq ⊢; exact ⟨haU.1.mul hq.1, haU.2.mul hq.2⟩

      have hpt : ∀ x : E, ((ι ((a.1 * q.1, a.2 * q.2), x))⁻¹ * (uGL a * nGL c) ∈ 𝒦) ↔
          ι (q, Ring.inverse q.1 * (-c) * q.2 + x) ∈ 𝒦 := by
        intro x
        have hgrp : (ι ((a.1 * q.1, a.2 * q.2), x))⁻¹ * (uGL a * nGL c) =
            (ι (q, Ring.inverse q.1 * (-c) * q.2 + x))⁻¹ := by
          rw [ι_apply, ι_apply, ← uGL_mul_uGL ha hq, nGL_add, ← mul_assoc (uGL q), ← nGL_mul_uGL hq, nGL_neg]
          group
        rw [hgrp, K_inv_mem_iff]
      simp_rw [hJ, indK_congr (hpt _)]
      exact lintegral_add_left_eq_self (μ := ν) (fun x => indK (K := K) (L := L) (v := v) (ι (q, x)))
        (Ring.inverse q.1 * (-c) * q.2)
    · rw [D_of_not hq, zero_mul, zero_mul]
  rw [h1, h2]
  simp_rw [h3]
  have hmq : Measurable fun q : Q => D q * ∫⁻ x, indK (K := K) (L := L) (v := v) (ι (q, x)) ∂ν :=
    measurable_D.mul ((measurable_indK.comp measurable_ι).lintegral_prod_right')
  rw [lintegral_const_mul _ hmq, ← mul_assoc, wt_mul_wt_mul_ofReal_inv ha, one_mul, Λ_eq_lintegral_lintegral]

theorem coord_eq_Λ_mul (Φ : G → ℝ≥0∞) (hΦ : Measurable Φ) (hΦK : ∀ g, ∀ k ∈ 𝒦, Φ (g * k) = Φ g) :
    ∫⁻ p, D p * ∫⁻ x, Φ (ι (p, x)) ∂ν ∂ν² = Λ ν * ∫⁻ g, Φ g ∂μG := by

  have step1 : ∀ h : G, Φ h = ∫⁻ g, Φ g * indK (K := K) (L := L) (v := v) (h⁻¹ * g) ∂μG := by
    intro h
    have hm : Measurable fun g : G => indK (K := K) (L := L) (v := v) (h⁻¹ * g) :=
      measurable_indK.comp (measurable_const_mul _)
    calc Φ h = Φ h * ∫⁻ g, indK (K := K) (L := L) (v := v) (h⁻¹ * g) ∂μG := by
            rw [lintegral_mul_left_eq_self (fun g => indK (K := K) (L := L) (v := v) g) h⁻¹, lintegral_indK, mul_one]
      _ = ∫⁻ g, Φ h * indK (K := K) (L := L) (v := v) (h⁻¹ * g) ∂μG := (lintegral_const_mul _ hm).symm
      _ = ∫⁻ g, Φ g * indK (K := K) (L := L) (v := v) (h⁻¹ * g) ∂μG := by
            refine lintegral_congr fun g => ?_
            by_cases hg : h⁻¹ * g ∈ 𝒦
            · rw [indK_of_mem hg]
              have : Φ g = Φ h := by
                have := hΦK h (h⁻¹ * g) hg
                rwa [mul_inv_cancel_left] at this
              rw [this]
            · rw [indK_of_not hg, mul_zero, mul_zero]
  have hmz : Measurable fun z : Q × E => D z.1 * Φ (ι z) :=
    (measurable_D.comp measurable_fst).mul (hΦ.comp measurable_ι)
  have hF : Measurable fun w : (Q × E) × G => D w.1.1 * (Φ w.2 * indK (K := K) (L := L) (v := v) ((ι w.1)⁻¹ * w.2)) :=
    (measurable_D.comp (measurable_fst.comp measurable_fst)).mul
      ((hΦ.comp measurable_snd).mul (measurable_indK.comp
        (((measurable_ι.comp measurable_fst).inv).mul measurable_snd)))
  calc ∫⁻ p, D p * ∫⁻ x, Φ (ι (p, x)) ∂ν ∂ν²
      = ∫⁻ z, D z.1 * Φ (ι z) ∂ζ := by
          rw [lintegral_prod _ hmz.aemeasurable]
          refine lintegral_congr fun p => ?_
          have hmx : Measurable fun x : E => Φ (ι (p, x)) :=
            hΦ.comp (measurable_ι.comp (measurable_const.prodMk measurable_id))
          dsimp only
          rw [lintegral_const_mul _ hmx]
    _ = ∫⁻ z, ∫⁻ g, D z.1 * (Φ g * indK (K := K) (L := L) (v := v) ((ι z)⁻¹ * g)) ∂μG ∂ζ := by
          refine lintegral_congr fun z => ?_
          have hmg : Measurable fun g : G => Φ g * indK (K := K) (L := L) (v := v) ((ι z)⁻¹ * g) :=
            hΦ.mul (measurable_indK.comp (measurable_const_mul _))
          rw [lintegral_const_mul _ hmg, ← step1]
    _ = ∫⁻ g, ∫⁻ z, D z.1 * (Φ g * indK (K := K) (L := L) (v := v) ((ι z)⁻¹ * g)) ∂ζ ∂μG :=
          lintegral_lintegral_swap hF.aemeasurable
    _ = ∫⁻ g, Φ g * V ν g ∂μG := by
          refine lintegral_congr fun g => ?_
          have hmz' : Measurable fun z : Q × E => D z.1 * indK (K := K) (L := L) (v := v) ((ι z)⁻¹ * g) :=
            (measurable_D.comp measurable_fst).mul (measurable_indK.comp ((measurable_ι.inv).mul_const _))
          rw [V, ← lintegral_const_mul _ hmz']
          refine lintegral_congr fun z => ?_
          ring
    _ = ∫⁻ g, Φ g * Λ ν ∂μG := by simp_rw [V_eq_Λ]
    _ = Λ ν * ∫⁻ g, Φ g ∂μG := by rw [lintegral_mul_const _ hΦ, mul_comm]

theorem Λ_ne_top : Λ ν ≠ ⊤ := by

  obtain ⟨C, hC⟩ := (isCompact_intg (K := K) (L := L) (v := v)).exists_bound_of_continuousOn
    (continuous_algebraNorm (K := K) (L := L) (v := v)).continuousOn
  set T : Set (Q × E) := ((𝒪 : Set E) ×ˢ (𝒪 : Set E)) ×ˢ (𝒪 : Set E) with hT
  have hTm : MeasurableSet T :=
    ((isCompact_intg.measurableSet).prod isCompact_intg.measurableSet).prod isCompact_intg.measurableSet
  have hTfin : ζ T < ⊤ := by
    rw [hT, Measure.prod_prod, Measure.prod_prod]
    have h := (isCompact_intg (K := K) (L := L) (v := v)).measure_lt_top (μ := ν)
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top h h) h

  have hpt : ∀ z : Q × E, D z.1 * indK (K := K) (L := L) (v := v) (ι z) ≤
      T.indicator (fun _ => ENNReal.ofReal C) z := by
    rintro ⟨p, x⟩
    by_cases hp : p ∈ goodT
    · by_cases hK : ι (p, x) ∈ 𝒦
      · have hpU := (mem_goodT_iff p).1 hp
        obtain ⟨hval, hinv⟩ := (mem_K_iff _).1 hK
        have e00 := hval 0 0; have e01 := hval 0 1; have e11 := hval 1 1
        have i00 := hinv 0 0; have i11 := hinv 1 1
        rw [coe_ι_of_mem hp] at e00 e01 e11
        rw [coe_ι_inv_of_mem hp] at i00 i11
        simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_fin_one] at e00 e01 e11 i00 i11
        have hx : x ∈ 𝒪 := by
          have : x = Ring.inverse p.1 * (p.1 * x) := by
            rw [← mul_assoc, Ring.inverse_mul_cancel _ hpU.1, one_mul]
          rw [this]; exact intg_mul_mem i00 e01
        have hzT : ((p, x) : Q × E) ∈ T := ⟨⟨e00, e11⟩, hx⟩
        rw [indicator_of_mem hzT, indK_of_mem hK, mul_one, D_of_mem hp]
        apply ENNReal.ofReal_le_ofReal

        have hprod : Algebra.norm F (p.1 * p.2) * Algebra.norm F (Ring.inverse p.1 * Ring.inverse p.2) = 1 := by
          rw [← map_mul, show p.1 * p.2 * (Ring.inverse p.1 * Ring.inverse p.2) =
            (p.1 * Ring.inverse p.1) * (p.2 * Ring.inverse p.2) by ring,
            Ring.mul_inverse_cancel _ hpU.1, Ring.mul_inverse_cancel _ hpU.2, mul_one, map_one]
        have hne : Algebra.norm F (p.1 * p.2) ≠ 0 := (isUnit_iff_norm_ne_zero _).1 (hpU.1.mul hpU.2)
        have hinvN : ‖Algebra.norm F (p.1 * p.2)‖⁻¹ = ‖Algebra.norm F (Ring.inverse p.1 * Ring.inverse p.2)‖ := by
          rw [← norm_inv]; congr 1
          exact (eq_inv_of_mul_eq_one_right hprod).symm ▸ rfl
        rw [hinvN]
        exact hC _ (intg_mul_mem i00 i11)
      · rw [indK_of_not hK, mul_zero]; exact zero_le
    · rw [D_of_not hp, zero_mul]; exact zero_le
  have hle : Λ ν ≤ ∫⁻ z, T.indicator (fun _ => ENNReal.ofReal C) z ∂ζ := lintegral_mono hpt
  rw [lintegral_indicator_const hTm] at hle
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hTfin.ne) hle

theorem Λ_ne_zero : Λ ν ≠ 0 := by
  intro h0

  have h := coord_eq_Λ_mul ν (fun _ => (1 : ℝ≥0∞)) measurable_const (fun _ _ _ => rfl)
  rw [h0, zero_mul] at h
  have h' : (∫⁻ p, D (K := K) (L := L) (v := v) p ∂ν²) * ν Set.univ = 0 := by
    rw [← h, ← lintegral_mul_const _ measurable_D]
    refine lintegral_congr fun p => ?_
    show D p * ν Set.univ = D p * ∫⁻ x, (1 : ℝ≥0∞) ∂ν
    rw [lintegral_const, one_mul]
  rw [mul_eq_zero] at h'
  rcases h' with h | h
  · have hpos : 0 < ∫⁻ p, D (K := K) (L := L) (v := v) p ∂ν² := by
      rw [lintegral_pos_iff_support measurable_D]
      have hsupp : Function.support (D (K := K) (L := L) (v := v)) = goodT := by
        ext p
        rw [Function.mem_support]
        constructor
        · intro hp; by_contra hp'; exact hp (D_of_not hp')
        · intro hp; exact (D_pos_of_mem hp).ne'
      rw [hsupp]
      exact isOpen_goodT.measure_pos _ ⟨(1, 1), one_mem_goodT⟩
    exact hpos.ne' h
  · exact (NeZero.ne (ν Set.univ)) h

def avg (Φ : G → ℝ≥0∞) (g : G) : ℝ≥0∞ := ∫⁻ k in 𝒦, Φ (g * k) ∂μG

theorem avg_eq (Φ : G → ℝ≥0∞) (g : G) :
    avg Φ g = ∫⁻ k, indK (K := K) (L := L) (v := v) k * Φ (g * k) ∂μG := by
  rw [avg, ← lintegral_indicator measurableSet_K]
  refine lintegral_congr fun k => ?_
  by_cases hk : k ∈ 𝒦
  · rw [indicator_of_mem hk, indK_of_mem hk, one_mul]
  · rw [indicator_of_notMem hk, indK_of_not hk, zero_mul]

theorem measurable_avg {Φ : G → ℝ≥0∞} (hΦ : Measurable Φ) : Measurable (avg (K := K) (L := L) (v := v) Φ) := by
  have h : Measurable fun w : G × G => indK (K := K) (L := L) (v := v) w.2 * Φ (w.1 * w.2) :=
    (measurable_indK.comp measurable_snd).mul (hΦ.comp (measurable_fst.mul measurable_snd))
  have : avg (K := K) (L := L) (v := v) Φ = fun g => ∫⁻ k, indK (K := K) (L := L) (v := v) k * Φ (g * k) ∂μG :=
    funext (avg_eq Φ)
  rw [this]
  exact h.lintegral_prod_right'

theorem avg_mul_K {Φ : G → ℝ≥0∞} (g : G) {k₀ : G} (hk₀ : k₀ ∈ 𝒦) :
    avg (K := K) (L := L) (v := v) Φ (g * k₀) = avg Φ g := by
  rw [avg_eq, avg_eq]
  have h := lintegral_mul_left_eq_self (μ := μG)
    (fun k => indK (K := K) (L := L) (v := v) k * Φ (g * k)) k₀
  rw [← h]
  refine lintegral_congr fun k => ?_
  show indK k * Φ (g * k₀ * k) = indK (k₀ * k) * Φ (g * (k₀ * k))
  rw [indK_congr (K_mul_mem_iff_left hk₀), mul_assoc]

theorem lintegral_avg {Φ : G → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ g, avg (K := K) (L := L) (v := v) Φ g ∂μG = ∫⁻ g, Φ g ∂μG := by
  simp_rw [avg_eq]
  have hF : Measurable fun w : G × G => indK (K := K) (L := L) (v := v) w.2 * Φ (w.1 * w.2) :=
    (measurable_indK.comp measurable_snd).mul (hΦ.comp (measurable_fst.mul measurable_snd))
  rw [lintegral_lintegral_swap hF.aemeasurable]
  have h1 : ∀ k : G, ∫⁻ g, indK (K := K) (L := L) (v := v) k * Φ (g * k) ∂μG = indK k * ∫⁻ g, Φ g ∂μG := by
    intro k
    have hmk : Measurable fun g : G => Φ (g * k) := hΦ.comp (measurable_mul_const k)
    rw [lintegral_const_mul _ hmk]
    by_cases hk : k ∈ 𝒦
    · rw [lintegral_mul_right_K Φ hΦ hk]
    · rw [indK_of_not hk, zero_mul, zero_mul]
  simp_rw [h1]
  rw [lintegral_mul_const _ measurable_indK, lintegral_indK, one_mul]

theorem main_general {Φ : G → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ g, Φ g ∂μG = (Λ ν)⁻¹ * ∫⁻ p, D p * ∫⁻ x, avg Φ (ι (p, x)) ∂ν ∂ν² := by
  rw [coord_eq_Λ_mul ν (avg Φ) (measurable_avg hΦ) (fun g k hk => avg_mul_K g hk), lintegral_avg hΦ,
    ← mul_assoc, ENNReal.inv_mul_cancel (Λ_ne_zero ν) (Λ_ne_top ν), one_mul]

theorem main_invariant {Φ : G → ℝ≥0∞} (hΦ : Measurable Φ) (hΦK : ∀ g, ∀ k ∈ 𝒦, Φ (g * k) = Φ g) :
    ∫⁻ g, Φ g ∂μG = (Λ ν)⁻¹ * ∫⁻ p, D p * ∫⁻ x, Φ (ι (p, x)) ∂ν ∂ν² := by
  rw [coord_eq_Λ_mul ν Φ hΦ hΦK, ← mul_assoc, ENNReal.inv_mul_cancel (Λ_ne_zero ν) (Λ_ne_top ν), one_mul]

end Main

end KcSemiLocalIwasawaHaar

end

open scoped Classical in
open KcSemiLocalIwasawaHaar in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure] :
    ∃ κ : ENNReal, κ ≠ 0 ∧ κ ≠ ⊤ ∧
      (∀ Φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ENNReal,
        Measurable[AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)] Φ →
        (letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
         ∫⁻ g, Φ g ∂(AutomorphicForm.semiLocalHaar K L v)) =
          κ * ∫⁻ p : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K),
            (if h : IsUnit (!![p.1, 0; 0, p.2] : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).det then
                ENNReal.ofReal ‖Algebra.norm (v.adicCompletion K) (p.1 * p.2)‖⁻¹ *
                  ∫⁻ x : L ⊗[K] v.adicCompletion K,
                    (letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
                     ∫⁻ k in AutomorphicForm.semiLocalIntegralSet K L v,
                        Φ (Matrix.GeneralLinearGroup.mk'' _ h * AutomorphicForm.unipotentGL2 x * k)
                          ∂(AutomorphicForm.semiLocalHaar K L v)) ∂ν
              else 0) ∂(ν.prod ν)) ∧
      (∀ Φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ENNReal,
        Measurable[AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)] Φ →
        (∀ g, ∀ k ∈ AutomorphicForm.semiLocalIntegralSet K L v, Φ (g * k) = Φ g) →
        (letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
         ∫⁻ g, Φ g ∂(AutomorphicForm.semiLocalHaar K L v)) =
          κ * ∫⁻ p : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K),
            (if h : IsUnit (!![p.1, 0; 0, p.2] : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).det then
                ENNReal.ofReal ‖Algebra.norm (v.adicCompletion K) (p.1 * p.2)‖⁻¹ *
                  ∫⁻ x : L ⊗[K] v.adicCompletion K,
                    Φ (Matrix.GeneralLinearGroup.mk'' _ h * AutomorphicForm.unipotentGL2 x) ∂ν
              else 0) ∂(ν.prod ν)) := by
  refine ⟨(Λ ν)⁻¹, ENNReal.inv_ne_zero.2 (Λ_ne_top ν), ENNReal.inv_ne_top.2 (Λ_ne_zero ν),
    fun Φ hΦ => ?_, fun Φ hΦ hΦK => ?_⟩
  · rw [main_general ν hΦ]
    congr 1
    refine lintegral_congr fun p => ?_
    by_cases h : IsUnit (!![p.1, 0; 0, p.2] : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).det
    · have h1 : IsUnit (tm p).det := h
      rw [dif_pos h, D_of_mem (show p ∈ goodT from h1)]
      congr 1
      refine lintegral_congr fun x => ?_
      show avg Φ (uGL p * nGL x) = _
      rw [avg, uGL_of_mem h1]
      rfl
    · rw [dif_neg h, D_of_not (show p ∉ goodT from h), zero_mul]
  · rw [main_invariant ν hΦ hΦK]
    congr 1
    refine lintegral_congr fun p => ?_
    by_cases h : IsUnit (!![p.1, 0; 0, p.2] : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).det
    · have h1 : IsUnit (tm p).det := h
      rw [dif_pos h, D_of_mem (show p ∈ goodT from h1)]
      congr 1
      refine lintegral_congr fun x => ?_
      show Φ (uGL p * nGL x) = _
      rw [uGL_of_mem h1]
      rfl
    · rw [dif_neg h, D_of_not (show p ∉ goodT from h), zero_mul]

end S_AutomorphicForm_exists_forall_lintegral_semiLocalHaar_eq_mul_lintegral_torus_unipotentGL2_setLIntegral_semiLocalIntegralSet
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_lintegral_semiLocalHaar_eq_mul_lintegral_torus_unipotentGL2_setLIntegral_semiLocalIntegralSet (solution)
