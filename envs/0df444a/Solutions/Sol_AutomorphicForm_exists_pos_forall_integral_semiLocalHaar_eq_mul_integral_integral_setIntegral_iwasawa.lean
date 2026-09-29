-- Prove2me | solution 1 for AutomorphicForm.exists_pos_forall_integral_semiLocalHaar_eq_mul_integral_integral_setIntegral_iwasawa
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/3f5c08b8-4531-5cf8-a72b-9d0c2fc3f6f2

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Theorems.Thm_AutomorphicForm_exists_forall_lintegral_semiLocalHaar_eq_mul_lintegral_torus_unipotentGL2_setLIntegral_semiLocalIntegralSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_pos_forall_integral_semiLocalHaar_eq_mul_integral_integral_setIntegral_iwasawa
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 320000

open NumberField IsDedekindDomain MeasureTheory Set Function
open scoped ENNReal NNReal TensorProduct TensorProduct.RightActions Pointwise

noncomputable section

namespace Ws48IwasawaBochner

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
  refine Continuous.smul (f := fun x => (Algebra.norm F (f x))⁻¹) (g := fun x => adjE (f x)) ?_
    (continuous_adjE.comp hf)
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

private theorem _root_.Ws48IwasawaBochner.isHaarMeasure_semiLocalHaar : (AutomorphicForm.semiLocalHaar K L v).IsHaarMeasure :=
  AutomorphicForm.isHaarMeasure_semiLocalHaar K L v

p2m_export "Ws48IwasawaBochner" "isHaarMeasure_semiLocalHaar"
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
theorem sFinite_μ : SFinite μG := @instSFiniteOfSigmaFinite _ _ _ (sigmaFinite_μ (K := K) (L := L) (v := v))

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

section Bochner

variable [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
variable (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure]

open scoped Classical

attribute [local instance] borelSpace_Q sigmaFinite_μ sFinite_μ

local notation "ν²" => Measure.prod ν ν

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

def T (z : Q × ((L ⊗[K] v.adicCompletion K) × G)) : G := uGL z.1 * nGL z.2.1 * z.2.2

theorem measurable_T : Measurable (T : Q × ((L ⊗[K] v.adicCompletion K) × G) → G) :=
  ((measurable_uGL.comp measurable_fst).mul (measurable_nGL.comp (measurable_fst.comp measurable_snd))).mul
    (measurable_snd.comp measurable_snd)

def θ : Measure (Q × ((L ⊗[K] v.adicCompletion K) × G)) :=
  ((ν²).withDensity D).prod (ν.prod ((μG).restrict 𝒦))

def ρ : Measure G := Measure.map T (θ ν)

theorem lintegral_ρ {Φ : G → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ g, Φ g ∂(ρ ν) = ∫⁻ p, D p * ∫⁻ x, ∫⁻ k in 𝒦, Φ (uGL p * nGL x * k) ∂μG ∂ν ∂ν² := by
  have hm : Measurable fun z : Q × ((L ⊗[K] v.adicCompletion K) × G) => Φ (T z) := hΦ.comp measurable_T
  rw [ρ, lintegral_map hΦ measurable_T, θ, lintegral_prod _ hm.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul _ measurable_D hm.lintegral_prod_right']
  refine lintegral_congr fun p => ?_
  have hmp : Measurable fun yz : (L ⊗[K] v.adicCompletion K) × G => Φ (T (p, yz)) :=
    hm.comp (measurable_const.prodMk measurable_id)
  rw [Pi.mul_apply, lintegral_prod _ hmp.aemeasurable]
  rfl

theorem lintegral_card_rhs_eq (Φ : G → ℝ≥0∞) :
    (∫⁻ p : Q, (if h : IsUnit (!![p.1, 0; 0, p.2] : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).det then
        ENNReal.ofReal ‖Algebra.norm F (p.1 * p.2)‖⁻¹ *
          ∫⁻ x : L ⊗[K] v.adicCompletion K, ∫⁻ k in 𝒦,
            Φ (Matrix.GeneralLinearGroup.mk'' _ h * AutomorphicForm.unipotentGL2 x * k) ∂μG ∂ν
      else 0) ∂ν²) = ∫⁻ p, D p * ∫⁻ x, ∫⁻ k in 𝒦, Φ (uGL p * nGL x * k) ∂μG ∂ν ∂ν² := by
  refine lintegral_congr fun p => ?_
  by_cases h : IsUnit (!![p.1, 0; 0, p.2] : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).det
  · have h1 : IsUnit (tm p).det := h
    rw [dif_pos h, D_of_mem (show p ∈ goodT from h1)]
    congr 1
    refine lintegral_congr fun x => ?_
    rw [uGL_of_mem h1]
    rfl
  · rw [dif_neg h, D_of_not (show p ∉ goodT from h), zero_mul]

theorem exists_semiLocalHaar_eq_smul_ρ : ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ⊤ ∧ (μG) = κ • ρ ν := by
  obtain ⟨κ, hκ0, hκt, hgen, -⟩ :=
    AutomorphicForm.exists_forall_lintegral_semiLocalHaar_eq_mul_lintegral_torus_unipotentGL2_setLIntegral_semiLocalIntegralSet
      K L v ν
  refine ⟨κ, hκ0, hκt, Measure.ext_of_lintegral _ fun Φ hΦ => ?_⟩
  rw [lintegral_smul_measure, hgen Φ hΦ, lintegral_card_rhs_eq ν Φ, lintegral_ρ ν hΦ, smul_eq_mul]

theorem uGL_eq_diagUnits2 {p : Q} (h : IsUnit p.1 ∧ IsUnit p.2) :
    uGL p = LanglandsTunnell.CubicInduction.diagUnits2 h.1.unit h.2.unit := by
  have h1 : IsUnit (tm p).det := (mem_goodT_iff p).2 h
  refine Units.ext ?_
  rw [coe_uGL_of_mem h1, LanglandsTunnell.CubicInduction.coe_diagUnits2, IsUnit.unit_spec, IsUnit.unit_spec]
  rfl

theorem integral_eq_of_integrable {κ : ℝ≥0∞} (hκ0 : κ ≠ 0) (hκt : κ ≠ ⊤) (hμ : (μG) = κ • ρ ν)
    (Φ : G → ℂ) (hΦm : Measurable Φ) (hΦi : Integrable Φ (μG)) :
    ∫ g, Φ g ∂μG =
      ((κ.toReal : ℝ) : ℂ) * ∫ p : Q,
        (if h : IsUnit p.1 ∧ IsUnit p.2 then
          ((‖Algebra.norm (v.adicCompletion K) (p.1 * p.2)‖⁻¹ : ℝ) : ℂ) *
            ∫ ξ : (L ⊗[K] v.adicCompletion K), ∫ k in 𝒦,
              Φ (LanglandsTunnell.CubicInduction.diagUnits2 h.1.unit h.2.unit * AutomorphicForm.unipotentGL2 ξ * k)
              ∂μG ∂ν
         else 0) ∂ν² := by
  have hΦsm : AEStronglyMeasurable Φ (Measure.map T (θ ν)) := hΦm.aestronglyMeasurable

  have hρ : ρ ν = κ⁻¹ • μG := by
    rw [hμ, smul_smul, ENNReal.inv_mul_cancel hκ0 hκt, one_smul]
  have hΦρ : Integrable Φ (ρ ν) := by
    rw [hρ]; exact hΦi.smul_measure (ENNReal.inv_ne_top.2 hκ0)
  have hΦθ : Integrable (fun z => Φ (T z)) (θ ν) :=
    (integrable_map_measure hΦsm measurable_T.aemeasurable).1 hΦρ

  conv_lhs => rw [hμ]
  rw [integral_smul_measure, show ρ ν = Measure.map T (θ ν) from rfl,
    integral_map measurable_T.aemeasurable hΦsm]

  rw [show θ ν = ((ν²).withDensity D).prod (ν.prod ((μG).restrict 𝒦)) from rfl] at hΦθ ⊢
  rw [integral_prod _ hΦθ]

  have hae : ∀ᵐ p ∂((ν²).withDensity D),
      (∫ yz, Φ (T (p, yz)) ∂(ν.prod ((μG).restrict 𝒦))) =
        ∫ x, ∫ k in 𝒦, Φ (uGL p * nGL x * k) ∂μG ∂ν := by
    filter_upwards [hΦθ.prod_right_ae] with p hp
    rw [integral_prod _ hp]
    rfl
  rw [integral_congr_ae hae]

  have hD : (D : Q → ℝ≥0∞) = fun p => ((Real.toNNReal (Dr (K := K) (L := L) (v := v) p) : ℝ≥0) : ℝ≥0∞) := rfl
  rw [hD, integral_withDensity_eq_integral_smul measurable_Dr.real_toNNReal, ← Complex.real_smul]

  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  dsimp only
  by_cases h : IsUnit p.1 ∧ IsUnit p.2
  · have hp : p ∈ goodT := (mem_goodT_iff p).2 h
    rw [dif_pos h, Dr_of_mem hp, NNReal.smul_def, Real.coe_toNNReal _ (inv_nonneg.2 (norm_nonneg _)),
      Complex.real_smul, uGL_eq_diagUnits2 h]
    rfl
  · have hp : p ∉ goodT := fun hp => h ((mem_goodT_iff p).1 hp)
    rw [dif_neg h, Dr_of_not hp, Real.toNNReal_zero, zero_smul]

end Bochner

end Ws48IwasawaBochner

end

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped Classical in
open Ws48IwasawaBochner in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure] :
    letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
    ∃ κ : ℝ, 0 < κ ∧ ∀ Φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ,
      Measurable Φ → Integrable Φ (AutomorphicForm.semiLocalHaar K L v) →
      ∫ g, Φ g ∂(AutomorphicForm.semiLocalHaar K L v) =
        (κ : ℂ) * ∫ p : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K),
          (if h : IsUnit p.1 ∧ IsUnit p.2 then
            ((‖Algebra.norm (v.adicCompletion K) (p.1 * p.2)‖⁻¹ : ℝ) : ℂ) *
              ∫ ξ : (L ⊗[K] v.adicCompletion K), ∫ k in AutomorphicForm.semiLocalIntegralSet K L v,
                Φ (diagUnits2 h.1.unit h.2.unit * AutomorphicForm.unipotentGL2 ξ * k)
                ∂(AutomorphicForm.semiLocalHaar K L v) ∂ν
           else 0) ∂(ν.prod ν) := by
  obtain ⟨κ, hκ0, hκt, hμ⟩ := exists_semiLocalHaar_eq_smul_ρ (K := K) (L := L) (v := v) ν
  exact ⟨κ.toReal, ENNReal.toReal_pos hκ0 hκt, fun Φ hΦm hΦi =>
    integral_eq_of_integrable ν hκ0 hκt hμ Φ hΦm hΦi⟩

end S_AutomorphicForm_exists_pos_forall_integral_semiLocalHaar_eq_mul_integral_integral_setIntegral_iwasawa
end P2MW
export P2MW.S_AutomorphicForm_exists_pos_forall_integral_semiLocalHaar_eq_mul_integral_integral_setIntegral_iwasawa (solution)
