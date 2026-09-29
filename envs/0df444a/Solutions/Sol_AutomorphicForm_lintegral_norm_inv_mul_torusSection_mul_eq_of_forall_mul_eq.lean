-- Prove2me | solution 1 for AutomorphicForm.lintegral_norm_inv_mul_torusSection_mul_eq_of_forall_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/a551ba6e-bd01-5265-92a7-50eb77f320b2

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Theorems.Thm_NumberField_AdicCompletion_map_linearMap_eq_norm_det_inv_smul_of_isAddHaarMeasure
import Theorems.Thm_AutomorphicForm_twistedCentralizer_diagUnits2_eq_map_toTensorGL_centralizer_of_normString_eq_of_isUnit_sub
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_lintegral_norm_inv_mul_torusSection_mul_eq_of_forall_mul_eq
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 320000

open NumberField IsDedekindDomain MeasureTheory Set Function
open scoped ENNReal NNReal TensorProduct TensorProduct.RightActions Pointwise
open LanglandsTunnell.CubicInduction (diagUnits2)

noncomputable section

namespace SwKit

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

private theorem _root_.SwKit.isHaarMeasure_semiLocalHaar : (AutomorphicForm.semiLocalHaar K L v).IsHaarMeasure :=
  AutomorphicForm.isHaarMeasure_semiLocalHaar K L v

p2m_export "SwKit" "isHaarMeasure_semiLocalHaar"
attribute [local instance] borelSpace_GL isHaarMeasure_semiLocalHaar

theorem measurableMul_GL : MeasurableMul₂ G := inferInstance
theorem measurableInv_GL : MeasurableInv G := inferInstance

attribute [local instance] measurableMul_GL measurableInv_GL

theorem kit_end : True := trivial

section Sigma
variable (σ : L ≃ₐ[K] L)

def sigmaLin : E →ₗ[F] E where
  toFun := AutomorphicForm.sigmaTensor K L F σ
  map_add' x y := map_add _ x y
  map_smul' c x := by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, RingHom.id_apply]
    congr 1
    show (Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K F)) ((1 : L) ⊗ₜ[K] c) = (1 : L) ⊗ₜ[K] c
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    simp

theorem continuous_sigmaTensor : Continuous (AutomorphicForm.sigmaTensor K L F σ : E → E) :=
  IsModuleTopology.continuous_of_linearMap (sigmaLin (v := v) σ)

theorem continuous_sigmaGL : Continuous (AutomorphicForm.sigmaGL K L F σ : G → G) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) E)).matrix_map (continuous_sigmaTensor (v := v) σ)).congr
      (fun x => rfl)
  · exact ((Units.continuous_coe_inv (M := Matrix (Fin 2) (Fin 2) E)).matrix_map (continuous_sigmaTensor (v := v) σ)).congr
      (fun x => rfl)

theorem isClosed_twistedCentralizer (δ : G) :
    IsClosed ((AutomorphicForm.twistedCentralizer K L F σ δ : Subgroup G) : Set G) := by
  have : ((AutomorphicForm.twistedCentralizer K L F σ δ : Subgroup G) : Set G) =
      {t : G | t * δ * (AutomorphicForm.sigmaGL K L F σ t)⁻¹ = δ} := by
    ext t; exact AutomorphicForm.mem_sigmaCentralizer_iff
  rw [this]
  exact isClosed_eq ((continuous_id.mul continuous_const).mul (continuous_sigmaGL (v := v) σ).inv) continuous_const

end Sigma

theorem mem_centralizer_diagUnits2_iff (a b : Fˣ) (hab : a ≠ b) (g : GL (Fin 2) F) :
    g ∈ Subgroup.centralizer ({diagUnits2 a b} : Set (GL (Fin 2) F)) ↔
      ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 ∧
      ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  have hsub : IsUnit ((a : F) - (b : F)) :=
    isUnit_iff_ne_zero.2 (sub_ne_zero.2 fun h => hab (Units.ext h))
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro hg
    have hcomm := hg _ (Set.mem_singleton _)
    have hM := congrArg (fun x : GL (Fin 2) F => ((x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) hcomm
    simp only [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2] at hM
    have e01 := congrFun (congrFun hM 0) 1
    have e10 := congrFun (congrFun hM 1) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at e01 e10
    constructor
    · have : ((a : F) - (b : F)) * ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
        linear_combination e01
      exact (hsub.mul_right_eq_zero).1 this
    · have : ((a : F) - (b : F)) * ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
        linear_combination (-1 : F) * e10
      exact (hsub.mul_right_eq_zero).1 this
  · rintro ⟨h01, h10⟩ h hh
    rw [Set.mem_singleton_iff.1 hh]
    apply Units.ext
    simp only [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h01, h10, mul_comm]

theorem isInvInvariant_of_comm {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [LocallyCompactSpace Γ] [SecondCountableTopology Γ] [T2Space Γ]
    (T : Subgroup Γ) (hT : IsClosed (T : Set Γ)) (hcomm : ∀ s t : T, s * t = t * s)
    [MeasurableSpace T] [BorelSpace T] (τ : Measure T) [τ.IsHaarMeasure] : τ.IsInvInvariant := by
  letI : CommGroup T := { mul_comm := hcomm }
  haveI : LocallyCompactSpace T := hT.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology T :=
    (Topology.IsInducing.subtypeVal : Topology.IsInducing (Subtype.val : T → Γ)).secondCountableTopology
  haveI : TopologicalSpace.PseudoMetrizableSpace T := TopologicalSpace.PseudoMetrizableSpace.of_regularSpace_secondCountableTopology T
  haveI : SigmaCompactSpace T := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : τ.InnerRegular := inferInstance
  exact Measure.IsHaarMeasure.isInvInvariant_of_innerRegular τ

theorem toTensorGL_apply (m : GL (Fin 2) F) (i j : Fin 2) :
    ((AutomorphicForm.toTensorGL K L F m : G) : Matrix (Fin 2) (Fin 2) E) i j =
      (Algebra.TensorProduct.includeRight : F →ₐ[K] E) (((m : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j) := rfl

end SwKit

end

open NumberField IsDedekindDomain MeasureTheory
open scoped ENNReal NNReal TensorProduct TensorProduct.RightActions
open LanglandsTunnell.CubicInduction (diagUnits2)

attribute [local instance 9999] Algebra.toModule
attribute [local instance] SwKit.isTopologicalRing_E SwKit.t2Space_E SwKit.locallyCompactSpace_E SwKit.continuousSMul_E
  SwKit.isScalarTower_FEE SwKit.smulCommClass_FEE SwKit.finite_KL SwKit.secondCountableTopology_E
  SwKit.t2Space_GL SwKit.secondCountableTopology_GL SwKit.locallyCompactSpace_GL SwKit.isTopologicalGroup_GL
  SwKit.measurableSpace_GL SwKit.borelSpace_GL SwKit.measurableMul_GL SwKit.measurableInv_GL

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
open scoped Classical in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure]
    (α β : (L ⊗[K] v.adicCompletion K)ˣ) (a b : (v.adicCompletion K)ˣ) (hab : a ≠ b)
    (hN : AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
      AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a b))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β))
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)))
    (hτ' : @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)) τ')
    (β₁ β₂ : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K) → ℝ) (hβ₁m : Measurable β₁) (hβ₂m : Measurable β₂)
    (hβ₁0 : ∀ p, 0 ≤ β₁ p) (hβ₂0 : ∀ p, 0 ≤ β₂ p)
    (hβ₁ : ∀ p : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K), IsUnit p.1 → IsUnit p.2 →
      @integral _ ℝ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)) τ'
        (fun t => β₁ ((((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0) * p.1, (((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1) * p.2)) = 1)
    (hβ₂ : ∀ p : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K), IsUnit p.1 → IsUnit p.2 →
      @integral _ ℝ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)) τ'
        (fun t => β₂ ((((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0) * p.1, (((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1) * p.2)) = 1)
    (H : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K) → ENNReal) (hHm : Measurable H)
    (hH : ∀ (t : AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β)) (p : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K)),
      H ((((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0) * p.1, (((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1) * p.2) = H p) :
    ∫⁻ p : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K), (if IsUnit p.1 ∧ IsUnit p.2 then
        ENNReal.ofReal (‖Algebra.norm (v.adicCompletion K) (p.1 * p.2)‖⁻¹ * β₁ p) * H p else 0) ∂(ν.prod ν) =
    ∫⁻ p : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K), (if IsUnit p.1 ∧ IsUnit p.2 then
        ENNReal.ofReal (‖Algebra.norm (v.adicCompletion K) (p.1 * p.2)‖⁻¹ * β₂ p) * H p else 0) ∂(ν.prod ν)  := by
  classical

  let T := AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β)
  letI mT : MeasurableSpace T := AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)
  haveI : BorelSpace T := ⟨rfl⟩
  haveI hτ : τ'.IsHaarMeasure := hτ'
  have hTcl := SwKit.isClosed_twistedCentralizer (v := v) σ (diagUnits2 α β)
  haveI : LocallyCompactSpace T := hTcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology T := (Topology.IsInducing.subtypeVal).secondCountableTopology
  haveI : SigmaCompactSpace T := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaFinite τ' := by infer_instance
  haveI : SFinite τ' := by infer_instance

  have hTeq := AutomorphicForm.twistedCentralizer_diagUnits2_eq_map_toTensorGL_centralizer_of_normString_eq_of_isUnit_sub
    K L σ hgen (v.adicCompletion K) a b (isUnit_iff_ne_zero.2 (sub_ne_zero.2 fun h => hab (Units.ext h))) α β hN
  let e₀ : T → L ⊗[K] v.adicCompletion K := fun t => ((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0
  let e₁ : T → L ⊗[K] v.adicCompletion K := fun t => ((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1
  have hdiag : ∀ t : T,
      ((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 1 = 0 ∧
      ((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 0 = 0 := by
    intro t
    have ht : (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈
        (Subgroup.centralizer ({diagUnits2 a b} : Set (GL (Fin 2) (v.adicCompletion K)))).map (AutomorphicForm.toTensorGL K L (v.adicCompletion K)) := by
      rw [← hTeq]; exact t.2
    obtain ⟨m, hm, hmt⟩ := Subgroup.mem_map.1 ht
    rw [SwKit.mem_centralizer_diagUnits2_iff a b hab] at hm
    rw [← hmt]
    simp only [SwKit.toTensorGL_apply, hm.1, hm.2, map_zero, and_self]
  have hmul : ∀ s t : T, e₀ (s * t) = e₀ s * e₀ t ∧ e₁ (s * t) = e₁ s * e₁ t := by
    intro s t
    simp only [e₀, e₁, Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, (hdiag s).1, (hdiag s).2,
      (hdiag t).1, (hdiag t).2, mul_zero, zero_mul, add_zero, zero_add]
    exact ⟨trivial, trivial⟩
  have hone : e₀ 1 = 1 ∧ e₁ 1 = 1 := by
    simp only [e₀, e₁, Subgroup.coe_one, Units.val_one, Matrix.one_apply_eq]; exact ⟨trivial, trivial⟩
  have hinv : ∀ t : T, e₀ t⁻¹ * e₀ t = 1 ∧ e₁ t⁻¹ * e₁ t = 1 := by
    intro t
    have h := hmul t⁻¹ t
    rw [inv_mul_cancel, hone.1, hone.2] at h
    exact ⟨h.1.symm, h.2.symm⟩
  have hinv' : ∀ t : T, e₀ t * e₀ t⁻¹ = 1 ∧ e₁ t * e₁ t⁻¹ = 1 := by
    intro t; have h := hinv t⁻¹; rw [inv_inv] at h; exact h
  have hunit : ∀ t : T, IsUnit (e₀ t) ∧ IsUnit (e₁ t) :=
    fun t => ⟨IsUnit.of_mul_eq_one _ (hinv' t).1, IsUnit.of_mul_eq_one _ (hinv' t).2⟩
  have hcomm : ∀ s t : T, s * t = t * s := by
    intro s t
    apply Subtype.ext; apply Units.ext
    ext i j
    have hs := hdiag s; have ht := hdiag t
    fin_cases i <;> fin_cases j <;>
      simp [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hs.1, hs.2, ht.1, ht.2, mul_comm]
  haveI : τ'.IsInvInvariant := SwKit.isInvInvariant_of_comm T hTcl hcomm τ'

  have he₀c : Continuous e₀ := (Units.continuous_val.comp continuous_subtype_val).matrix_elem 0 0
  have he₁c : Continuous e₁ := (Units.continuous_val.comp continuous_subtype_val).matrix_elem 1 1
  have he₀m : Measurable e₀ := he₀c.measurable
  have he₁m : Measurable e₁ := he₁c.measurable

  let act : T → (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K) → (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K) :=
    fun t p => (e₀ t * p.1, e₁ t * p.2)
  have hact_mul : ∀ s t p, act (s * t) p = act s (act t p) := by
    intro s t p; simp only [act, (hmul s t).1, (hmul s t).2, mul_assoc]
  have hact_inv : ∀ t p, act t⁻¹ (act t p) = p := by
    intro t p; simp only [act, ← mul_assoc, (hinv t).1, (hinv t).2, one_mul]
  have hact_inv' : ∀ t p, act t (act t⁻¹ p) = p := by
    intro t p; simp only [act, ← mul_assoc, (hinv' t).1, (hinv' t).2, one_mul]
  have hact_m : ∀ t, Measurable (act t) := fun t =>
    (measurable_fst.const_mul _).prodMk (measurable_snd.const_mul _)
  have hact_m2 : Measurable (fun q : T × ((L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K)) => act q.1 q.2) :=
    ((he₀m.comp measurable_fst).mul (measurable_fst.comp measurable_snd)).prodMk
      ((he₁m.comp measurable_fst).mul (measurable_snd.comp measurable_snd))

  have hunit_act : ∀ t p, (IsUnit (act t p).1 ∧ IsUnit (act t p).2) ↔ (IsUnit p.1 ∧ IsUnit p.2) := by
    intro t p
    constructor
    · rintro ⟨h1, h2⟩
      have h1' : IsUnit (e₀ t⁻¹ * (e₀ t * p.1)) := (hunit t⁻¹).1.mul h1
      have h2' : IsUnit (e₁ t⁻¹ * (e₁ t * p.2)) := (hunit t⁻¹).2.mul h2
      rw [← mul_assoc, (hinv t).1, one_mul] at h1'
      rw [← mul_assoc, (hinv t).2, one_mul] at h2'
      exact ⟨h1', h2'⟩
    · rintro ⟨h1, h2⟩; exact ⟨(hunit t).1.mul h1, (hunit t).2.mul h2⟩

  let D : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K) → ℝ≥0∞ := fun p =>
    if IsUnit p.1 ∧ IsUnit p.2 then ENNReal.ofReal ‖Algebra.norm (v.adicCompletion K) (p.1 * p.2)‖⁻¹ else 0
  have hDm : Measurable D := by
    refine Measurable.ite ?_ ?_ measurable_const
    · exact (SwKit.isOpen_units.measurableSet.preimage measurable_fst).inter (SwKit.isOpen_units.measurableSet.preimage measurable_snd)
    · exact ENNReal.measurable_ofReal.comp ((SwKit.continuous_algebraNorm.comp (continuous_fst.mul continuous_snd)).norm.measurable.inv)
  have hD_act : ∀ t p, D (act t p) = (SwKit.wt (K := K) (L := L) (v := v) (e₀ t * e₁ t))⁻¹ * D p := by
    intro t p
    simp only [D]
    by_cases hp : IsUnit p.1 ∧ IsUnit p.2
    · rw [if_pos ((hunit_act t p).2 hp), if_pos hp]
      have hw := SwKit.wt_ne_zero (K := K) (L := L) (v := v) ((hunit t).1.mul (hunit t).2)
      simp only [act]
      rw [show e₀ t * p.1 * (e₁ t * p.2) = (e₀ t * e₁ t) * (p.1 * p.2) by ring, map_mul, norm_mul, mul_inv,
        ENNReal.ofReal_mul (inv_nonneg.2 (norm_nonneg _)), SwKit.wt,
        ENNReal.ofReal_inv_of_pos (norm_pos_iff.2 ((SwKit.isUnit_iff_norm_ne_zero _).1 ((hunit t).1.mul (hunit t).2)))]
    · rw [if_neg (fun h => hp ((hunit_act t p).1 h)), if_neg hp, mul_zero]

  have hform : ∀ (βx : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K) → ℝ), (∀ p, 0 ≤ βx p) →
      (fun p : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K) =>
        (if IsUnit p.1 ∧ IsUnit p.2 then ENNReal.ofReal (‖Algebra.norm (v.adicCompletion K) (p.1 * p.2)‖⁻¹ * βx p) * H p else 0)) =
      fun p => D p * ENNReal.ofReal (βx p) * H p := by
    intro βx hβx
    funext p
    by_cases hp : IsUnit p.1 ∧ IsUnit p.2
    · simp only [D, if_pos hp, ENNReal.ofReal_mul (inv_nonneg.2 (norm_nonneg _))]
    · simp only [D, if_neg hp, zero_mul]
  rw [hform β₁ hβ₁0, hform β₂ hβ₂0]

  have hsec : ∀ (βx : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K) → ℝ), (∀ p, 0 ≤ βx p) →
      (∀ p : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K), IsUnit p.1 → IsUnit p.2 → ∫ t : T, βx (act t p) ∂τ' = 1) →
      ∀ p : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K), IsUnit p.1 → IsUnit p.2 →
        ∫⁻ t : T, ENNReal.ofReal (βx (act t p)) ∂τ' = 1 := by
    intro βx hβx hβ p h1 h2
    have hI : Integrable (fun t : T => βx (act t p)) τ' := by
      by_contra hni
      have := hβ p h1 h2
      rw [integral_undef hni] at this
      exact zero_ne_one this
    rw [← ofReal_integral_eq_lintegral_ofReal hI (Filter.Eventually.of_forall fun t => hβx _), hβ p h1 h2, ENNReal.ofReal_one]
  have hsec1 := hsec β₁ hβ₁0 hβ₁
  have hsec2 := hsec β₂ hβ₂0 hβ₂

  have hβ₁act : Measurable (fun q : T × ((L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K)) => ENNReal.ofReal (β₁ (act q.1 q.2))) :=
    ENNReal.measurable_ofReal.comp (hβ₁m.comp hact_m2)
  have hβ₂act : Measurable (fun q : T × ((L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K)) => ENNReal.ofReal (β₂ (act q.1 q.2))) :=
    ENNReal.measurable_ofReal.comp (hβ₂m.comp hact_m2)
  have hinvT : Measurable (fun t : T => t⁻¹) := measurable_inv

  have step1 : ∫⁻ p, D p * ENNReal.ofReal (β₁ p) * H p ∂(ν.prod ν) =
      ∫⁻ p, ∫⁻ t : T, D p * ENNReal.ofReal (β₁ p) * H p * ENNReal.ofReal (β₂ (act t p)) ∂τ' ∂(ν.prod ν) := by
    refine lintegral_congr fun p => ?_
    have hmeas : Measurable (fun t : T => ENNReal.ofReal (β₂ (act t p))) :=
      ENNReal.measurable_ofReal.comp (hβ₂m.comp ((he₀m.mul_const _).prodMk (he₁m.mul_const _)))
    by_cases hp : IsUnit p.1 ∧ IsUnit p.2
    · rw [lintegral_const_mul _ hmeas, hsec2 p hp.1 hp.2, mul_one]
    · simp only [D, if_neg hp, zero_mul]
      first | exact lintegral_zero.symm | exact lintegral_zero

  have hF : Measurable (fun q : ((L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K)) × T =>
      D q.1 * ENNReal.ofReal (β₁ q.1) * H q.1 * ENNReal.ofReal (β₂ (act q.2 q.1))) :=
    (((hDm.comp measurable_fst).mul (ENNReal.measurable_ofReal.comp (hβ₁m.comp measurable_fst))).mul (hHm.comp measurable_fst)).mul
      (hβ₂act.comp (measurable_snd.prodMk measurable_fst))
  have step2 : ∫⁻ p, ∫⁻ t : T, D p * ENNReal.ofReal (β₁ p) * H p * ENNReal.ofReal (β₂ (act t p)) ∂τ' ∂(ν.prod ν) =
      ∫⁻ t : T, ∫⁻ p, D p * ENNReal.ofReal (β₁ p) * H p * ENNReal.ofReal (β₂ (act t p)) ∂(ν.prod ν) ∂τ' :=
    lintegral_lintegral_swap hF.aemeasurable

  have hmap : ∀ t : T, Measure.map (act t) (ν.prod ν) = (SwKit.wt (K := K) (L := L) (v := v) (e₀ t * e₁ t))⁻¹ • (ν.prod ν) := by
    intro t
    have h := Measure.map_prod_map (ν) (ν) (measurable_const_mul (e₀ t)) (measurable_const_mul (e₁ t))
    have hact : act t = Prod.map (fun x => e₀ t * x) (fun x => e₁ t * x) := by funext p; rfl
    rw [hact, ← h, SwKit.map_mul_left ν (hunit t).1, SwKit.map_mul_left ν (hunit t).2, Measure.prod_smul_right, Measure.prod_smul_left,
      smul_smul, SwKit.wt_mul, ENNReal.mul_inv (Or.inl (SwKit.wt_ne_zero (hunit t).1)) (Or.inr (SwKit.wt_ne_zero (hunit t).2)), mul_comm]
  have step3 : ∀ t : T,
      ∫⁻ p, D p * ENNReal.ofReal (β₁ p) * H p * ENNReal.ofReal (β₂ (act t p)) ∂(ν.prod ν) =
      ∫⁻ p, D p * ENNReal.ofReal (β₂ p) * H p * ENNReal.ofReal (β₁ (act t⁻¹ p)) ∂(ν.prod ν) := by
    intro t
    set w : ℝ≥0∞ := SwKit.wt (K := K) (L := L) (v := v) (e₀ t * e₁ t) with hw
    have hw0 : w ≠ 0 := SwKit.wt_ne_zero ((hunit t).1.mul (hunit t).2)
    have hwT : w ≠ ⊤ := SwKit.wt_ne_top _
    let Gf : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K) → ℝ≥0∞ := fun p =>
      D p * ENNReal.ofReal (β₂ p) * H p * ENNReal.ofReal (β₁ (act t⁻¹ p))
    have hGm : Measurable Gf :=
      (((hDm.mul (ENNReal.measurable_ofReal.comp hβ₂m)).mul hHm)).mul (ENNReal.measurable_ofReal.comp (hβ₁m.comp (hact_m t⁻¹)))

    have hA : ∫⁻ p, Gf (act t p) ∂(ν.prod ν) = w⁻¹ * ∫⁻ p, Gf p ∂(ν.prod ν) := by
      rw [← lintegral_map hGm (hact_m t), hmap t, lintegral_smul_measure, smul_eq_mul]

    have hB : ∀ p, Gf (act t p) = w⁻¹ * (D p * ENNReal.ofReal (β₁ p) * H p * ENNReal.ofReal (β₂ (act t p))) := by
      intro p
      simp only [Gf]
      rw [hD_act, hact_inv, hH t p]
      ring
    have hFt : Measurable (fun p : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K) =>
        D p * ENNReal.ofReal (β₁ p) * H p * ENNReal.ofReal (β₂ (act t p))) :=
      ((hDm.mul (ENNReal.measurable_ofReal.comp hβ₁m)).mul hHm).mul (ENNReal.measurable_ofReal.comp (hβ₂m.comp (hact_m t)))
    have hC : ∫⁻ p, Gf (act t p) ∂(ν.prod ν) = w⁻¹ * ∫⁻ p, D p * ENNReal.ofReal (β₁ p) * H p * ENNReal.ofReal (β₂ (act t p)) ∂(ν.prod ν) := by
      rw [← lintegral_const_mul _ hFt]
      exact lintegral_congr fun p => hB p
    rw [hA] at hC
    exact ((ENNReal.mul_right_inj (ENNReal.inv_ne_zero.2 hwT) (ENNReal.inv_ne_top.2 hw0)).1 hC).symm

  have hF' : Measurable (fun q : ((L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K)) × T =>
      D q.1 * ENNReal.ofReal (β₂ q.1) * H q.1 * ENNReal.ofReal (β₁ (act q.2⁻¹ q.1))) :=
    (((hDm.comp measurable_fst).mul (ENNReal.measurable_ofReal.comp (hβ₂m.comp measurable_fst))).mul (hHm.comp measurable_fst)).mul
      (hβ₁act.comp ((hinvT.comp measurable_snd).prodMk measurable_fst))
  have step4 : ∫⁻ t : T, ∫⁻ p, D p * ENNReal.ofReal (β₂ p) * H p * ENNReal.ofReal (β₁ (act t⁻¹ p)) ∂(ν.prod ν) ∂τ' =
      ∫⁻ p, ∫⁻ t : T, D p * ENNReal.ofReal (β₂ p) * H p * ENNReal.ofReal (β₁ (act t⁻¹ p)) ∂τ' ∂(ν.prod ν) :=
    (lintegral_lintegral_swap hF'.aemeasurable).symm
  have step5 : ∫⁻ p, ∫⁻ t : T, D p * ENNReal.ofReal (β₂ p) * H p * ENNReal.ofReal (β₁ (act t⁻¹ p)) ∂τ' ∂(ν.prod ν) =
      ∫⁻ p, D p * ENNReal.ofReal (β₂ p) * H p ∂(ν.prod ν) := by
    refine lintegral_congr fun p => ?_
    have hmeas : Measurable (fun t : T => ENNReal.ofReal (β₁ (act t⁻¹ p))) :=
      ENNReal.measurable_ofReal.comp (hβ₁m.comp (((he₀m.comp hinvT).mul_const _).prodMk ((he₁m.comp hinvT).mul_const _)))
    by_cases hp : IsUnit p.1 ∧ IsUnit p.2
    · rw [lintegral_const_mul _ hmeas, lintegral_inv_eq_self (fun t : T => ENNReal.ofReal (β₁ (act t p))), hsec1 p hp.1 hp.2, mul_one]
    · simp only [D, if_neg hp, zero_mul]
      first | exact lintegral_zero.symm | exact lintegral_zero
  rw [step1, step2, lintegral_congr step3, step4, step5]

end S_AutomorphicForm_lintegral_norm_inv_mul_torusSection_mul_eq_of_forall_mul_eq
end P2MW
export P2MW.S_AutomorphicForm_lintegral_norm_inv_mul_torusSection_mul_eq_of_forall_mul_eq (solution)
