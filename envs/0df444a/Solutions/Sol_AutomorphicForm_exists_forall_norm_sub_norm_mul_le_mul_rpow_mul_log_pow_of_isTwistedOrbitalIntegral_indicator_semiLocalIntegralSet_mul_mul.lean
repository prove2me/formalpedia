-- Prove2me | solution 1 for AutomorphicForm.exists_forall_norm_sub_norm_mul_le_mul_rpow_mul_log_pow_of_isTwistedOrbitalIntegral_indicator_semiLocalIntegralSet_mul_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/777313b2-e392-5633-b4a8-d9950e39e76a

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_NumberField_AdicCompletion_map_linearMap_eq_norm_det_inv_smul_of_isAddHaarMeasure
import Theorems.Thm_AutomorphicForm_lintegral_enorm_twistedConj_mul_semiLocalHaar_eq_mul_lintegral_lintegral_torus_unipotentChart_of_isTwistedSectionFnOn_of_diagonal
import Theorems.Thm_AutomorphicForm_exists_forall_lintegral_semiLocalHaar_eq_mul_lintegral_pi_norm_algebraNorm_det_inv_sq
import Theorems.Thm_AutomorphicForm_exists_linearMap_mul_sigmaTensor_sub_mul_and_det_eq_neg_one_pow_mul_norm_sub_norm
import Theorems.Thm_AutomorphicForm_exists_measurable_forall_integral_localCentralizer_toTensorGL_mul_eq_one_of_diagonal
import Theorems.Thm_AutomorphicForm_exists_forall_withDensity_norm_inv_setOf_norm_mem_and_mul_sigmaTensor_eq_mul_mul_le
import Theorems.Thm_AutomorphicForm_exists_forall_setLIntegral_withDensity_norm_inv_iSup_measure_setOf_upperTriangular_mem_doubleCoset_le
import Theorems.Thm_AutomorphicForm_twistedCentralizer_eq_map_toTensorGL_localCentralizer_and_exists_isHaarMeasure_map_eq_of_diagonal_of_norm_ne
import Theorems.Thm_AutomorphicForm_toTensorGL_mem_semiLocalIntegralSet_iff_mem_localIntegralSet
import Theorems.Thm_AutomorphicForm_exists_windowed_section_localCentralizer_toTensorGL_of_diagonal
import Theorems.Thm_AutomorphicForm_exists_forall_lowerUnipotent_eq_diag_mul_unipotent_mul_mem_semiLocalIntegralSet
import Theorems.Thm_MeasureTheory_lintegral_enorm_mul_eq_and_integral_mul_eq_of_forall_lintegral_comp_smul_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_AutomorphicForm_exists_forall_norm_sub_norm_mul_le_mul_rpow_mul_log_pow_of_isTwistedOrbitalIntegral_indicator_semiLocalIntegralSet_mul_mul
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.JPSSCubicLiftPackage.mk.sizeOf_spec AutomorphicForm.formalBaseChange_a AutomorphicForm.JPSSCubicLiftPackage.mk.injEq AutomorphicForm.formalBaseChange_b LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11 AutomorphicForm.gl2Weyl_val"

set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain MeasureTheory Set Function
open scoped ENNReal NNReal TensorProduct TensorProduct.RightActions Pointwise

noncomputable section

namespace K47C3

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
  refine Continuous.fun_smul (Continuous.inv₀ (continuous_algebraNorm.comp hf) fun x => ?_) (continuous_adjE.comp hf)
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

theorem measurable_wt : Measurable (wt : E → ℝ≥0∞) :=
  ENNReal.measurable_ofReal.comp (continuous_algebraNorm.norm).measurable

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

omit [NumberField L] [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)] in

theorem exists_ne_zero_norm_lt_one : ∃ c : F, c ≠ 0 ∧ ‖c‖ < 1 := by
  obtain ⟨x, hxv, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  set c : F := FinitePlace.embedding v (x : K) with hc
  have hc0 : c ≠ 0 := by
    intro h; apply hx0
    have h' : ((x : K) : F) = 0 := h
    have h2 : (x : K) = 0 := (algebraMap K F).injective (by rw [map_zero]; exact h')
    exact_mod_cast h2
  exact ⟨c, hc0, (FinitePlace.norm_lt_one_iff_mem (K := K) v x).2 hxv⟩

theorem measure_submodule_eq_zero (W : Submodule F E) (hW : W ≠ ⊤) : ν W = 0 := by
  by_contra hpos
  have hpos' : 0 < ν W := pos_iff_ne_zero.2 hpos
  have hclosed : IsClosed (W : Set E) := by
    letI : TopologicalSpace (E ⧸ W) := moduleTopology F (E ⧸ W)
    haveI : IsModuleTopology F (E ⧸ W) := ⟨rfl⟩
    haveI : ContinuousAdd (E ⧸ W) := IsModuleTopology.toContinuousAdd F _
    haveI : ContinuousSMul F (E ⧸ W) := IsModuleTopology.toContinuousSMul F _
    haveI : T2Space (E ⧸ W) := IsModuleTopology.t2Space F
    have hc : Continuous (W.mkQ : E → E ⧸ W) := IsModuleTopology.continuous_of_linearMap W.mkQ
    have : (W : Set E) = W.mkQ ⁻¹' {0} := by
      ext x; simp [Submodule.Quotient.mk_eq_zero]
    rw [this]
    exact isClosed_singleton.preimage hc
  haveI : ν.Regular := inferInstance
  have hnhds : (W : Set E) - (W : Set E) ∈ nhds (0 : E) :=
    Measure.sub_mem_nhds_zero_of_addHaar_pos ν (W : Set E) hclosed.measurableSet hpos'
  have hsub : (W : Set E) - (W : Set E) ⊆ W := by
    rintro _ ⟨x, hx, y, hy, rfl⟩; exact W.sub_mem hx hy
  have hWn : (W : Set E) ∈ nhds (0 : E) := Filter.mem_of_superset hnhds hsub
  obtain ⟨x, hx⟩ : ∃ x : E, x ∉ W := by
    by_contra h
    push Not at h
    exact hW (eq_top_iff.2 fun x _ => h x)
  have hcont : Continuous fun c : F => c • x := continuous_id.smul continuous_const
  have htend : Filter.Tendsto (fun c : F => c • x) (nhds 0) (nhds 0) := by
    simpa using hcont.tendsto 0
  have hev : ∀ᶠ c : F in nhds 0, c • x ∈ W := htend hWn
  obtain ⟨c₀, hc₀0, hc₀1⟩ := exists_ne_zero_norm_lt_one (K := K) (v := v)
  have hpow : Filter.Tendsto (fun n : ℕ => c₀ ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hc₀1
  obtain ⟨n, hn⟩ := (hpow.eventually hev).exists
  set c : F := c₀ ^ n with hc
  have hc0 : c ≠ 0 := pow_ne_zero n hc₀0
  have hcx : c • x ∈ W := hn
  apply hx
  have : x = c⁻¹ • (c • x) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [this]
  exact W.smul_mem c⁻¹ hcx

theorem measure_nonunits_eq_zero : ν {x : E | ¬ IsUnit x} = 0 := by
  haveI : IsArtinianRing E := IsArtinianRing.of_finite F E
  have hfin : {I : Ideal E | I.IsMaximal}.Finite := IsArtinianRing.setOf_isMaximal_finite E
  have hcover : {x : E | ¬ IsUnit x} ⊆ ⋃ I ∈ {I : Ideal E | I.IsMaximal}, (I : Set E) := by
    intro x hx
    obtain ⟨I, hI, hxI⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hx)
    exact Set.mem_biUnion hI hxI
  refine measure_mono_null hcover ?_
  refine (measure_biUnion_null_iff hfin.countable).2 fun I hI => ?_
  let W : Submodule F E :=
    { carrier := (I : Set E)
      add_mem' := fun ha hb => I.add_mem ha hb
      zero_mem' := I.zero_mem
      smul_mem' := fun c x hx => by
        have h1 : c • x = algebraMap F E c * x := Algebra.smul_def c x
        show c • x ∈ I
        rw [h1]
        exact I.mul_mem_left _ hx }
  have hW : W ≠ ⊤ := by
    intro h
    apply hI.ne_top
    rw [eq_top_iff]
    intro x _
    have : x ∈ W := by rw [h]; trivial
    exact this
  exact measure_submodule_eq_zero ν W hW

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

private theorem _root_.K47C3.isHaarMeasure_semiLocalHaar : (AutomorphicForm.semiLocalHaar K L v).IsHaarMeasure :=
  AutomorphicForm.isHaarMeasure_semiLocalHaar K L v

p2m_export "K47C3" "isHaarMeasure_semiLocalHaar"
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

section Sigma

variable (σ : L ≃ₐ[K] L)

theorem sigmaTensor_tmul (l : L) (c : F) :
    AutomorphicForm.sigmaTensor K L F σ (l ⊗ₜ[K] c) = σ l ⊗ₜ[K] c := by
  show (Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K F)) (l ⊗ₜ[K] c) = σ l ⊗ₜ[K] c
  rw [Algebra.TensorProduct.map_tmul]; rfl

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

theorem coe_sigmaGL (g : G) :
    ((AutomorphicForm.sigmaGL K L F σ g : G) : Matrix (Fin 2) (Fin 2) E) =
      (g : Matrix (Fin 2) (Fin 2) E).map (AutomorphicForm.sigmaTensor K L F σ) := rfl

theorem continuous_sigmaGL : Continuous (AutomorphicForm.sigmaGL K L F σ : G → G) := by
  refine continuous_GL_of (fun i j => ?_) (fun i j => ?_)
  · simp only [coe_sigmaGL, Matrix.map_apply]
    exact (continuous_sigmaTensor σ).comp (Units.continuous_val.matrix_elem i j)
  · have : ∀ x : G, (((AutomorphicForm.sigmaGL K L F σ x)⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) i j =
        AutomorphicForm.sigmaTensor K L F σ (((x⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) i j) := by
      intro x
      rw [← map_inv, coe_sigmaGL, Matrix.map_apply]
    simp_rw [this]
    exact (continuous_sigmaTensor σ).comp (Units.continuous_coe_inv.matrix_elem i j)

theorem measurable_sigmaGL : Measurable (AutomorphicForm.sigmaGL K L F σ : G → G) :=
  (continuous_sigmaGL σ).measurable

def emb (c : F) : E := (1 : L) ⊗ₜ[K] c

theorem emb_mul (c d : F) : emb (K := K) (L := L) (v := v) (c * d) = emb c * emb d := by
  simp [emb, Algebra.TensorProduct.tmul_mul_tmul]

theorem emb_one : emb (K := K) (L := L) (v := v) (1 : F) = 1 := rfl

theorem emb_zero : emb (K := K) (L := L) (v := v) (0 : F) = 0 := by simp [emb]

theorem isUnit_emb {c : F} (hc : c ≠ 0) : IsUnit (emb (K := K) (L := L) (v := v) c) := by
  refine ⟨⟨emb c, emb c⁻¹, ?_, ?_⟩, rfl⟩
  · rw [← emb_mul, mul_inv_cancel₀ hc, emb_one]
  · rw [← emb_mul, inv_mul_cancel₀ hc, emb_one]

theorem algebraMap_eq_emb (c : F) : algebraMap F E c = emb (K := K) (L := L) (v := v) c := rfl

theorem continuous_emb : Continuous (emb (K := K) (L := L) (v := v) : F → E) := by
  have : (emb (K := K) (L := L) (v := v) : F → E) = algebraMap F E := funext fun c => (algebraMap_eq_emb c).symm
  rw [this]
  exact continuous_algebraMap F E

theorem sigmaTensor_emb (c : F) :
    AutomorphicForm.sigmaTensor K L F σ (emb (K := K) (L := L) (v := v) c) = emb c := by
  rw [emb, sigmaTensor_tmul, map_one]

theorem coe_toTensorGL (t : GF) :
    ((AutomorphicForm.toTensorGL K L F t : G) : Matrix (Fin 2) (Fin 2) E) =
      (t : Matrix (Fin 2) (Fin 2) F).map emb := rfl

theorem sigmaGL_toTensorGL (t : GF) :
    AutomorphicForm.sigmaGL K L F σ (AutomorphicForm.toTensorGL K L F t) = AutomorphicForm.toTensorGL K L F t := by
  apply Units.ext
  rw [coe_sigmaGL, coe_toTensorGL, Matrix.map_map]
  congr 1
  funext c
  exact sigmaTensor_emb σ c

end Sigma

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

theorem measure_goodT_compl (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure] :
    (ν.prod ν) (goodTᶜ : Set Q) = 0 := by
  have hnull : ν {x : E | ¬ IsUnit x} = 0 := measure_nonunits_eq_zero ν
  have hsub : (goodTᶜ : Set Q) ⊆ (Prod.fst ⁻¹' {x : E | ¬ IsUnit x}) ∪ (Prod.snd ⁻¹' {x : E | ¬ IsUnit x}) := by
    intro p hp
    simp only [mem_compl_iff, mem_goodT_iff, not_and_or] at hp
    rcases hp with h | h
    · exact Or.inl h
    · exact Or.inr h
  refine measure_mono_null hsub (measure_union_null ?_ ?_)
  · rw [← Measure.map_apply measurable_fst isClosed_nonunits.measurableSet, Measure.map_fst_prod,
      Measure.smul_apply, smul_eq_mul, hnull, mul_zero]
  · rw [← Measure.map_apply measurable_snd isClosed_nonunits.measurableSet, Measure.map_snd_prod,
      Measure.smul_apply, smul_eq_mul, hnull, mul_zero]

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

section TorusF

variable {a b : v.adicCompletion K} {γ : GL (Fin 2) (v.adicCompletion K)}

theorem entries_eq_zero_of_mem (hab : a ≠ b) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b])
    {g : GF} (hg : g ∈ AutomorphicForm.localCentralizer K v γ) :
    (g : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 ∧ (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  rw [AutomorphicForm.localCentralizer, Subgroup.mem_centralizer_iff] at hg
  simp only [Set.mem_singleton_iff, forall_eq] at hg
  rw [Units.ext_iff, Units.val_mul, Units.val_mul, hγ] at hg
  have hab' : a - b ≠ 0 := sub_ne_zero.2 hab
  have h01 := congrFun (congrFun hg 0) 1
  have h10 := congrFun (congrFun hg 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h01 h10
  constructor
  · have : (a - b) * (g : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by linear_combination h01
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hab'
    · exact h
  · have : (a - b) * (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by linear_combination -h10
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hab'
    · exact h

theorem mul_comm_of_mem (hab : a ≠ b) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b])
    (s t : AutomorphicForm.localCentralizer K v γ) : s * t = t * s := by
  obtain ⟨hs01, hs10⟩ := entries_eq_zero_of_mem hab hγ s.2
  obtain ⟨ht01, ht10⟩ := entries_eq_zero_of_mem hab hγ t.2
  apply Subtype.ext
  apply Units.ext
  change ((s : GF) : Matrix (Fin 2) (Fin 2) F) * ((t : GF) : Matrix (Fin 2) (Fin 2) F) =
    ((t : GF) : Matrix (Fin 2) (Fin 2) F) * ((s : GF) : Matrix (Fin 2) (Fin 2) F)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hs01, hs10, ht01, ht10] <;> ring

def c1 (t : GF) : E := emb ((t : Matrix (Fin 2) (Fin 2) F) 0 0)
def c2 (t : GF) : E := emb ((t : Matrix (Fin 2) (Fin 2) F) 1 1)

theorem ne_zero_of_mem (hab : a ≠ b) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b])
    {g : GF} (hg : g ∈ AutomorphicForm.localCentralizer K v γ) :
    (g : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 ∧ (g : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
  obtain ⟨h01, h10⟩ := entries_eq_zero_of_mem hab hγ hg
  have hdet : (g : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := (Matrix.isUnits_det_units g).ne_zero
  rw [Matrix.det_fin_two, h01, zero_mul, sub_zero] at hdet
  exact ⟨left_ne_zero_of_mul hdet, right_ne_zero_of_mul hdet⟩

theorem isUnit_c1 (hab : a ≠ b) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b])
    (t : AutomorphicForm.localCentralizer K v γ) : IsUnit (c1 (K := K) (L := L) (t : GF)) :=
  isUnit_emb (ne_zero_of_mem hab hγ t.2).1

theorem isUnit_c2 (hab : a ≠ b) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b])
    (t : AutomorphicForm.localCentralizer K v γ) : IsUnit (c2 (K := K) (L := L) (t : GF)) :=
  isUnit_emb (ne_zero_of_mem hab hγ t.2).2

theorem continuous_c1 : Continuous (c1 (K := K) (L := L) (v := v) : GF → E) :=
  continuous_emb.comp (Units.continuous_val.matrix_elem 0 0)

theorem continuous_c2 : Continuous (c2 (K := K) (L := L) (v := v) : GF → E) :=
  continuous_emb.comp (Units.continuous_val.matrix_elem 1 1)

def act (t : GF) (p : Q) : Q := (c1 (K := K) (L := L) t * p.1, c2 (K := K) (L := L) t * p.2)

theorem continuous_act : Continuous fun z : GF × Q => act (K := K) (L := L) z.1 z.2 :=
  ((continuous_c1.comp continuous_fst).mul (continuous_fst.comp continuous_snd)).prodMk
    ((continuous_c2.comp continuous_fst).mul (continuous_snd.comp continuous_snd))

theorem continuous_act_left (t : GF) : Continuous (act (K := K) (L := L) t : Q → Q) :=
  continuous_act.comp (continuous_const.prodMk continuous_id)

theorem coe_toTensorGL_of_mem (hab : a ≠ b) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b])
    {t : GF} (ht : t ∈ AutomorphicForm.localCentralizer K v γ) :
    ((AutomorphicForm.toTensorGL K L F t : G) : Matrix (Fin 2) (Fin 2) E) = !![c1 t, 0; 0, c2 t] := by
  obtain ⟨h01, h10⟩ := entries_eq_zero_of_mem hab hγ ht
  rw [coe_toTensorGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply, c1, c2, h01, h10, emb_zero]

theorem toTensorGL_mul_uGL (hab : a ≠ b) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b])
    (t : AutomorphicForm.localCentralizer K v γ) {p : Q} (hp : p ∈ goodT) :
    AutomorphicForm.toTensorGL K L F (t : GF) * uGL p = uGL (act (K := K) (L := L) (t : GF) p) := by
  have hp' : act (K := K) (L := L) (t : GF) p ∈ goodT := by
    rw [mem_goodT_iff] at hp ⊢
    exact ⟨(isUnit_c1 hab hγ t).mul hp.1, (isUnit_c2 hab hγ t).mul hp.2⟩
  apply Units.ext
  rw [Units.val_mul, coe_uGL_of_mem hp, coe_uGL_of_mem hp', coe_toTensorGL_of_mem hab hγ t.2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tm, act, Matrix.mul_apply, Fin.sum_univ_two]

theorem act_mem_goodT_iff (hab : a ≠ b) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b])
    (t : AutomorphicForm.localCentralizer K v γ) (p : Q) :
    act (K := K) (L := L) (t : GF) p ∈ goodT ↔ p ∈ goodT := by
  rw [mem_goodT_iff, mem_goodT_iff, act]
  simp only [IsUnit.mul_iff, isUnit_c1 hab hγ t, isUnit_c2 hab hγ t, true_and]

theorem c1_mul_of_mem (hab : a ≠ b) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b])
    (s t : AutomorphicForm.localCentralizer K v γ) :
    c1 (K := K) (L := L) ((s * t : AutomorphicForm.localCentralizer K v γ) : GF) = c1 (s : GF) * c1 (t : GF) := by
  obtain ⟨-, ht10⟩ := entries_eq_zero_of_mem hab hγ t.2
  simp only [c1, Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, ht10, mul_zero, add_zero,
    emb_mul]

theorem c2_mul_of_mem (hab : a ≠ b) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b])
    (s t : AutomorphicForm.localCentralizer K v γ) :
    c2 (K := K) (L := L) ((s * t : AutomorphicForm.localCentralizer K v γ) : GF) = c2 (s : GF) * c2 (t : GF) := by
  obtain ⟨ht01, -⟩ := entries_eq_zero_of_mem hab hγ t.2
  simp only [c2, Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, ht01, mul_zero, zero_add,
    emb_mul]

theorem act_mul_of_mem (hab : a ≠ b) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b])
    (s t : AutomorphicForm.localCentralizer K v γ) (p : Q) :
    act (K := K) (L := L) ((s * t : AutomorphicForm.localCentralizer K v γ) : GF) p = act (s : GF) (act (t : GF) p) := by
  simp only [act, c1_mul_of_mem hab hγ, c2_mul_of_mem hab hγ, mul_assoc]

theorem act_one (p : Q) : act (K := K) (L := L) (1 : GF) p = p := by
  rcases p with ⟨p1, p2⟩
  simp [act, c1, c2, emb_one]

theorem act_inv_act (hab : a ≠ b) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b])
    (t : AutomorphicForm.localCentralizer K v γ) (p : Q) :
    act (K := K) (L := L) ((t⁻¹ : AutomorphicForm.localCentralizer K v γ) : GF) (act (t : GF) p) = p := by
  rw [← act_mul_of_mem hab hγ, inv_mul_cancel]
  exact act_one p

theorem act_act_inv (hab : a ≠ b) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b])
    (t : AutomorphicForm.localCentralizer K v γ) (p : Q) :
    act (K := K) (L := L) (t : GF) (act ((t⁻¹ : AutomorphicForm.localCentralizer K v γ) : GF) p) = p := by
  rw [← act_mul_of_mem hab hγ, mul_inv_cancel]
  exact act_one p

end TorusF

section Coords

variable [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
variable (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure]

open scoped Classical

attribute [local instance] borelSpace_Q

local notation "π" => Measure.pi fun _ : Fin 4 => ν
local notation "ν²" => Measure.prod ν ν

def GHyp (cG : ℝ≥0∞) : Prop :=
  ∀ H : G → ℝ≥0∞, Measurable H →
    ∫⁻ g, H g ∂(AutomorphicForm.semiLocalHaar K L v) =
      cG * ∫⁻ x : P, (if h : IsUnit (!![x 0, x 1; x 2, x 3] : Matrix (Fin 2) (Fin 2) E).det then
          H (Matrix.GeneralLinearGroup.mk'' _ h) else 0) *
        ENNReal.ofReal ((‖Algebra.norm F (!![x 0, x 1; x 2, x 3] : Matrix (Fin 2) (Fin 2) E).det‖ ^ 2)⁻¹) ∂π

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

def ρ : Measure Q := (ν²).withDensity D

scoped instance sigmaFinite_ρ : SigmaFinite (ρ (K := K) (L := L) ν) :=
  SigmaFinite.withDensity_of_ne_top (Filter.Eventually.of_forall fun p => (D_lt_top p).ne)

theorem lintegral_ρ {H : Q → ℝ≥0∞} (hH : Measurable H) : ∫⁻ p, H p ∂(ρ ν) = ∫⁻ p, D p * H p ∂ν² := by
  rw [ρ, lintegral_withDensity_eq_lintegral_mul _ measurable_D hH]; rfl

theorem integral_ρ (H : Q → ℂ) : ∫ p, H p ∂(ρ ν) = ∫ p, (Dr p : ℂ) * H p ∂ν² := by
  rw [ρ, integral_withDensity_eq_integral_toReal_smul measurable_D (Filter.Eventually.of_forall D_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [D_toReal, Complex.real_smul]

theorem ρ_goodT_compl : (ρ ν) (goodTᶜ : Set Q) = 0 :=
  withDensity_absolutelyContinuous _ _ (measure_goodT_compl ν)

end Coords

section Invariance

variable [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
variable (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure]
variable {a b : v.adicCompletion K} {γ : GL (Fin 2) (v.adicCompletion K)}

open scoped Classical

attribute [local instance] borelSpace_Q

local notation "ν²" => Measure.prod ν ν
local notation "A" => AutomorphicForm.localCentralizer K v γ

theorem D_act (hab : a ≠ b) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b]) (t : A) (p : Q) :
    D (K := K) (L := L) (v := v) p =
      wt (K := K) (L := L) (v := v) (c1 (K := K) (L := L) (t : GF) * c2 (t : GF)) * D (act (K := K) (L := L) (t : GF) p) := by
  by_cases hp : p ∈ goodT
  · have hp' : act (K := K) (L := L) (t : GF) p ∈ goodT := (act_mem_goodT_iff hab hγ t p).2 hp
    rw [D_of_mem hp, D_of_mem hp', wt]
    simp only [act]
    have hc : IsUnit (c1 (K := K) (L := L) (t : GF) * c2 (t : GF)) := (isUnit_c1 hab hγ t).mul (isUnit_c2 hab hγ t)
    set c : E := c1 (K := K) (L := L) (t : GF) * c2 (t : GF) with hcdef
    set n : E := p.1 * p.2 with hndef
    have hcn : 0 < ‖Algebra.norm F c‖ := norm_pos_iff.2 ((isUnit_iff_norm_ne_zero _).1 hc)
    have hrw : c1 (K := K) (L := L) (t : GF) * p.1 * (c2 (K := K) (L := L) (t : GF) * p.2) = c * n := by
      rw [hcdef, hndef]; ring
    have key : ‖Algebra.norm F (c * n)‖⁻¹ = ‖Algebra.norm F c‖⁻¹ * ‖Algebra.norm F n‖⁻¹ := by
      rw [map_mul, norm_mul, mul_inv]
    rw [hrw, key, ENNReal.ofReal_mul (inv_nonneg.2 hcn.le), ← mul_assoc, ← ENNReal.ofReal_mul hcn.le,
      mul_inv_cancel₀ hcn.ne', ENNReal.ofReal_one, one_mul]
  · have hp' : act (K := K) (L := L) (t : GF) p ∉ goodT := fun h => hp ((act_mem_goodT_iff hab hγ t p).1 h)
    rw [D_of_not hp, D_of_not hp', mul_zero]

theorem lintegral_comp_act_prod (hab : a ≠ b) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b]) (t : A)
    {H : Q → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ p, H (act (K := K) (L := L) (t : GF) p) ∂ν² =
      (wt (K := K) (L := L) (v := v) (c1 (K := K) (L := L) (t : GF)))⁻¹ * (wt (K := K) (L := L) (v := v) (c2 (K := K) (L := L) (t : GF)))⁻¹ *
        ∫⁻ p, H p ∂ν² := by
  have hm : Measurable fun p : Q => H (act (K := K) (L := L) (t : GF) p) :=
    hH.comp (continuous_act_left (t : GF)).measurable
  have h1 : ∫⁻ p, H (act (K := K) (L := L) (t : GF) p) ∂ν² =
      ∫⁻ x, ∫⁻ y, H (c1 (K := K) (L := L) (t : GF) * x, c2 (K := K) (L := L) (t : GF) * y) ∂ν ∂ν := by
    rw [lintegral_prod _ hm.aemeasurable]
    rfl
  have h2 : ∀ x : E, ∫⁻ y, H (c1 (K := K) (L := L) (t : GF) * x, c2 (K := K) (L := L) (t : GF) * y) ∂ν =
      (wt (K := K) (L := L) (v := v) (c2 (K := K) (L := L) (t : GF)))⁻¹ * ∫⁻ y, H (c1 (K := K) (L := L) (t : GF) * x, y) ∂ν := by
    intro x
    exact lintegral_comp_mul_left ν (fun y => H (c1 (K := K) (L := L) (t : GF) * x, y))
      (hH.comp (measurable_const.prodMk measurable_id)) (isUnit_c2 hab hγ t)
  have h3 : Measurable fun x : E => ∫⁻ y, H (x, y) ∂ν := hH.lintegral_prod_right'
  have h4 : ∫⁻ x, ∫⁻ y, H (c1 (K := K) (L := L) (t : GF) * x, y) ∂ν ∂ν =
      (wt (K := K) (L := L) (v := v) (c1 (K := K) (L := L) (t : GF)))⁻¹ * ∫⁻ x, ∫⁻ y, H (x, y) ∂ν ∂ν :=
    lintegral_comp_mul_left ν (fun x => ∫⁻ y, H (x, y) ∂ν) h3 (isUnit_c1 hab hγ t)
  rw [h1]
  simp_rw [h2]
  rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 (wt_ne_zero (isUnit_c2 hab hγ t))), h4,
    lintegral_prod _ hH.aemeasurable, ← mul_assoc, mul_comm ((wt _)⁻¹)]

theorem lintegral_comp_act (hab : a ≠ b) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b]) (t : A)
    {H : Q → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ p, H (act (K := K) (L := L) (t : GF) p) ∂(ρ ν) = ∫⁻ p, H p ∂(ρ ν) := by
  have hact : Measurable (act (K := K) (L := L) (t : GF) : Q → Q) := (continuous_act_left (t : GF)).measurable
  have hm : Measurable fun p : Q => H (act (K := K) (L := L) (t : GF) p) := hH.comp hact
  rw [lintegral_ρ ν hm, lintegral_ρ ν hH]
  have hDH : Measurable fun p : Q => D p * H p := measurable_D.mul hH
  set W : ℝ≥0∞ := wt (K := K) (L := L) (v := v) (c1 (K := K) (L := L) (t : GF) * c2 (t : GF)) with hW
  have h1 : ∀ p : Q, D p * H (act (K := K) (L := L) (t : GF) p) =
      W * (D (act (K := K) (L := L) (t : GF) p) * H (act (K := K) (L := L) (t : GF) p)) := by
    intro p; rw [D_act hab hγ t p, mul_assoc]
  simp_rw [h1]
  have hcancel : W * (wt (K := K) (L := L) (v := v) (c1 (K := K) (L := L) (t : GF)))⁻¹ *
      (wt (K := K) (L := L) (v := v) (c2 (K := K) (L := L) (t : GF)))⁻¹ = 1 := by
    rw [hW, wt_mul, show ∀ x y z w : ℝ≥0∞, x * y * z * w = (x * z) * (y * w) from fun x y z w => by ring,
      ENNReal.mul_inv_cancel (wt_ne_zero (isUnit_c1 hab hγ t)) (wt_ne_top _),
      ENNReal.mul_inv_cancel (wt_ne_zero (isUnit_c2 hab hγ t)) (wt_ne_top _), one_mul]
  rw [lintegral_const_mul' _ _ (wt_ne_top _), lintegral_comp_act_prod ν hab hγ t hDH, ← mul_assoc, ← mul_assoc,
    hcancel, one_mul]

end Invariance

section Indep

variable [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
variable (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure]
variable {a b : v.adicCompletion K} {γ : GL (Fin 2) (v.adicCompletion K)}

open scoped Classical

theorem t2Space_GF : T2Space GF := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → F))
  exact Units.isEmbedding_embedProduct.t2Space

theorem secondCountableTopology_GF : SecondCountableTopology GF := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) F) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → F))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

attribute [local instance] borelSpace_Q t2Space_GF secondCountableTopology_GF
  AutomorphicForm.locallyCompactSpace_localGL AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel
  AutomorphicForm.localCentralizerBorel

theorem borelSpace_A (γ : GF) :
    @BorelSpace (AutomorphicForm.localCentralizer K v γ) _ (AutomorphicForm.localCentralizerBorel K v γ) :=
  @BorelSpace.mk _ _ (AutomorphicForm.localCentralizerBorel K v γ) rfl

theorem locallyCompactSpace_A (γ : GF) : LocallyCompactSpace (AutomorphicForm.localCentralizer K v γ) :=
  (Set.isClosed_centralizer _).isClosedEmbedding_subtypeVal.locallyCompactSpace

theorem secondCountableTopology_A (γ : GF) : SecondCountableTopology (AutomorphicForm.localCentralizer K v γ) :=
  TopologicalSpace.Subtype.secondCountableTopology _

attribute [local instance] borelSpace_A locallyCompactSpace_A secondCountableTopology_A

local notation "ν²" => Measure.prod ν ν
local notation "A" => AutomorphicForm.localCentralizer K v γ

theorem isInvInvariant_of_isHaarMeasure (hab : a ≠ b) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b])
    (τ : Measure A) [τ.IsHaarMeasure] : τ.IsInvInvariant := by
  letI : CommGroup A :=
    { (inferInstance : Group A) with mul_comm := mul_comm_of_mem hab hγ }
  haveI : τ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure τ
  exact Measure.IsHaarMeasure.isInvInvariant_of_regular τ

theorem continuous_act_A (p : Q) : Continuous fun t : A => act (K := K) (L := L) (t : GF) p :=
  continuous_act.comp (continuous_subtype_val.prodMk continuous_const)

theorem measurable_act_uncurry :
    Measurable fun z : Q × A => act (K := K) (L := L) (z.2 : GF) z.1 :=
  (continuous_act.comp ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst)).measurable

@[reducible] def mulActionA (hab : a ≠ b) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b]) : MulAction A Q where
  smul t p := act (K := K) (L := L) (t : GF) p
  one_smul p := act_one p
  mul_smul s t p := act_mul_of_mem hab hγ s t p

theorem measurePreserving_act (hab : a ≠ b) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b]) (t : A) :
    MeasurePreserving (act (K := K) (L := L) (t : GF)) (ρ ν) (ρ ν) := by
  have hm : Measurable (act (K := K) (L := L) (t : GF) : Q → Q) := (continuous_act_left (t : GF)).measurable
  refine ⟨hm, ?_⟩
  ext s hs
  rw [Measure.map_apply hm hs, ← lintegral_indicator_one (hm hs), ← lintegral_indicator_one hs]
  have h1 : (fun p : Q => (act (K := K) (L := L) (t : GF) ⁻¹' s).indicator (1 : Q → ℝ≥0∞) p) =
      fun p : Q => s.indicator (1 : Q → ℝ≥0∞) (act (K := K) (L := L) (t : GF) p) := by
    funext p; simp [Set.indicator, Set.mem_preimage]
  rw [h1]
  exact lintegral_comp_act ν hab hγ t (measurable_one.indicator hs)

variable (τ : Measure (AutomorphicForm.localCentralizer K v γ)) [τ.IsHaarMeasure]

theorem indep (hab : a ≠ b) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b])
    {h : Q → ℂ} (hh : Measurable h) (hhinv : ∀ (t : A) (p : Q), h (act (K := K) (L := L) (t : GF) p) = h p)
    {w₁ w₂ : Q → ℝ} (hw₁ : Measurable w₁) (hw₂ : Measurable w₂) (hw₁0 : ∀ p, 0 ≤ w₁ p) (hw₂0 : ∀ p, 0 ≤ w₂ p)
    (hs₁ : ∀ p, h p ≠ 0 → ∫⁻ t : A, ENNReal.ofReal (w₁ (act (K := K) (L := L) (t : GF) p)) ∂τ = 1)
    (hs₂ : ∀ p, h p ≠ 0 → ∫⁻ t : A, ENNReal.ofReal (w₂ (act (K := K) (L := L) (t : GF) p)) ∂τ = 1) :
    ∫⁻ p, ‖h p‖ₑ * ENNReal.ofReal (w₁ p) ∂(ρ ν) = ∫⁻ p, ‖h p‖ₑ * ENNReal.ofReal (w₂ p) ∂(ρ ν) ∧
      (Integrable (fun p => h p * (w₁ p : ℂ)) (ρ ν) →
        Integrable (fun p => h p * (w₂ p : ℂ)) (ρ ν) ∧
          ∫ p, h p * (w₁ p : ℂ) ∂(ρ ν) = ∫ p, h p * (w₂ p : ℂ) ∂(ρ ν)) := by
  haveI := isInvInvariant_of_isHaarMeasure hab hγ τ
  have hact : Measurable fun z : A × Q => act (K := K) (L := L) (z.1 : GF) z.2 :=
    (continuous_act.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)).measurable
  have hρ : ∀ t : A, MeasurePreserving (act (K := K) (L := L) (t : GF)) (ρ ν) (ρ ν) := fun t =>
    measurePreserving_act ν hab hγ t
  exact @MeasureTheory.lintegral_enorm_mul_eq_and_integral_mul_eq_of_forall_lintegral_comp_smul_eq_one
    A Q _ (mulActionA hab hγ) _ _ _ hact τ _ _ (ρ ν) _ hρ h hh hhinv w₁ w₂ hw₁ hw₂ hw₁0 hw₂0 hs₁ hs₂

end Indep

section Twist

variable {a b : v.adicCompletion K} {γ : GL (Fin 2) (v.adicCompletion K)}
variable (σ : L ≃ₐ[K] L) {δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)}

local notation "A" => AutomorphicForm.localCentralizer K v γ

theorem toTensorGL_mul_diag (hab : a ≠ b) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b])
    (hδ₀₁ : (δ : Matrix (Fin 2) (Fin 2) E) 0 1 = 0) (hδ₁₀ : (δ : Matrix (Fin 2) (Fin 2) E) 1 0 = 0) (t : A) :
    AutomorphicForm.toTensorGL K L F (t : GF) * δ = δ * AutomorphicForm.toTensorGL K L F (t : GF) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_toTensorGL_of_mem hab hγ t.2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hδ₀₁, hδ₁₀, mul_comm]

theorem twConj_mul (hab : a ≠ b) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b])
    (hδ₀₁ : (δ : Matrix (Fin 2) (Fin 2) E) 0 1 = 0) (hδ₁₀ : (δ : Matrix (Fin 2) (Fin 2) E) 1 0 = 0) (t : A) (x : G) :
    (AutomorphicForm.toTensorGL K L F (t : GF) * x)⁻¹ * δ *
        AutomorphicForm.sigmaGL K L F σ (AutomorphicForm.toTensorGL K L F (t : GF) * x) =
      x⁻¹ * δ * AutomorphicForm.sigmaGL K L F σ x := by
  set X := AutomorphicForm.toTensorGL K L F (t : GF) with hX
  have hc : X * δ = δ * X := toTensorGL_mul_diag hab hγ hδ₀₁ hδ₁₀ t
  rw [map_mul, sigmaGL_toTensorGL, mul_inv_rev]
  calc x⁻¹ * X⁻¹ * δ * (X * AutomorphicForm.sigmaGL K L F σ x)
      = x⁻¹ * (X⁻¹ * (δ * X)) * AutomorphicForm.sigmaGL K L F σ x := by group
    _ = x⁻¹ * (X⁻¹ * (X * δ)) * AutomorphicForm.sigmaGL K L F σ x := by rw [hc]
    _ = x⁻¹ * δ * AutomorphicForm.sigmaGL K L F σ x := by group

end Twist

section Coset

variable [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
variable {γ : GL (Fin 2) (v.adicCompletion K)}
variable (σ : L ≃ₐ[K] L) {δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)}

open scoped Classical

attribute [local instance] t2Space_GF secondCountableTopology_GF
  AutomorphicForm.locallyCompactSpace_localGL AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel
  AutomorphicForm.localCentralizerBorel borelSpace_A locallyCompactSpace_A secondCountableTopology_A

local notation "A" => AutomorphicForm.localCentralizer K v γ
local notation "Tw" => AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ

theorem continuous_toTensorGL : Continuous (AutomorphicForm.toTensorGL K L F : GF → G) := by
  refine continuous_GL_of (fun i j => ?_) (fun i j => ?_)
  · simp only [coe_toTensorGL, Matrix.map_apply]
    exact continuous_emb.comp (Units.continuous_val.matrix_elem i j)
  · have : ∀ t : GF, (((AutomorphicForm.toTensorGL K L F t)⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) i j =
        emb (((t⁻¹ : GF) : Matrix (Fin 2) (Fin 2) F) i j) := by
      intro t; rw [← map_inv, coe_toTensorGL, Matrix.map_apply]
    simp_rw [this]
    exact continuous_emb.comp (Units.continuous_coe_inv.matrix_elem i j)

theorem measurable_toTensorGL_A : Measurable fun t : A => AutomorphicForm.toTensorGL K L F (t : GF) :=
  (continuous_toTensorGL.comp continuous_subtype_val).measurable

theorem integral_tw_eq (τ : Measure A)
    (τ' : @Measure Tw (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hττ' : @Measure.map _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ)
        (AutomorphicForm.glBorelOf E) Subtype.val τ' =
      Measure.map (fun s : A => AutomorphicForm.toTensorGL K L F (s : GF)) τ)
    {w : G → ℝ} (hwm : Measurable w) (x : G) :
    (letI := AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ
     ∫ c : Tw, w ((c : G) * x) ∂τ') = ∫ t : A, w (AutomorphicForm.toTensorGL K L F (t : GF) * x) ∂τ := by
  letI := AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ
  haveI : BorelSpace Tw := ⟨rfl⟩
  have hval : Measurable (Subtype.val : Tw → G) := continuous_subtype_val.measurable
  have hg : Measurable fun g : G => w (g * x) := hwm.comp (measurable_id.mul_const x)
  have h1 : ∫ c : Tw, w ((c : G) * x) ∂τ' = ∫ g, w (g * x) ∂(Measure.map (Subtype.val : Tw → G) τ') :=
    (integral_map hval.aemeasurable hg.aestronglyMeasurable).symm
  rw [h1, hττ', integral_map measurable_toTensorGL_A.aemeasurable hg.aestronglyMeasurable]

theorem lintegral_section (τ : Measure A)
    (τ' : @Measure Tw (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hττ' : @Measure.map _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ)
        (AutomorphicForm.glBorelOf E) Subtype.val τ' =
      Measure.map (fun s : A => AutomorphicForm.toTensorGL K L F (s : GF)) τ)
    {φ : G → ℂ} {w : G → ℝ} (hw : AutomorphicForm.IsTwistedSectionFnOn K L F σ δ τ' φ w)
    (x : G) (hx : φ (x⁻¹ * δ * AutomorphicForm.sigmaGL K L F σ x) ≠ 0) :
    ∫⁻ t : A, ENNReal.ofReal (w (AutomorphicForm.toTensorGL K L F (t : GF) * x)) ∂τ = 1 := by
  obtain ⟨hw0, hwm, -, hsec⟩ := hw
  have h1 : ∫ t : A, w (AutomorphicForm.toTensorGL K L F (t : GF) * x) ∂τ = 1 := by
    rw [← integral_tw_eq σ τ τ' hττ' hwm x]; exact hsec x hx
  have hint : Integrable (fun t : A => w (AutomorphicForm.toTensorGL K L F (t : GF) * x)) τ := by
    by_contra h
    rw [integral_undef h] at h1
    exact zero_ne_one h1
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun t => hw0 _), h1,
    ENNReal.ofReal_one]

end Coset

section Main

variable [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
variable (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure]
variable {a b : v.adicCompletion K} {γ : GL (Fin 2) (v.adicCompletion K)}
variable (σ : L ≃ₐ[K] L) {δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)}

open scoped Classical

attribute [local instance] borelSpace_Q t2Space_GF secondCountableTopology_GF
  AutomorphicForm.locallyCompactSpace_localGL AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel
  AutomorphicForm.localCentralizerBorel borelSpace_A locallyCompactSpace_A secondCountableTopology_A

local notation "ν²" => Measure.prod ν ν
local notation "A" => AutomorphicForm.localCentralizer K v γ
local notation "Tw" => AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ

def Φf (δ : G) (φ : G → ℂ) (q p : Q) : ℂ :=
  φ ((uGL p * sGL q)⁻¹ * δ * AutomorphicForm.sigmaGL K L F σ (uGL p * sGL q))

theorem measurable_twConj : Measurable fun x : G => x⁻¹ * δ * AutomorphicForm.sigmaGL K L F σ x :=
  (measurable_inv.mul_const δ).mul (measurable_sigmaGL σ)

theorem measurable_Φf_uncurry {φ : G → ℂ} (hφm : Measurable φ) :
    Measurable fun z : Q × Q => Φf σ δ φ z.1 z.2 := by
  have hx : Measurable fun z : Q × Q => uGL z.2 * sGL z.1 :=
    (measurable_uGL.comp measurable_snd).mul (measurable_sGL.comp measurable_fst)
  exact hφm.comp ((measurable_twConj σ).comp hx)

theorem measurable_Φf {φ : G → ℂ} (hφm : Measurable φ) (q : Q) : Measurable (Φf σ δ φ q) := by
  show Measurable fun p : Q => φ ((uGL p * sGL q)⁻¹ * δ * AutomorphicForm.sigmaGL K L F σ (uGL p * sGL q))
  have hx : Measurable fun p : Q => uGL p * sGL q := measurable_uGL.mul_const _
  exact hφm.comp ((measurable_twConj σ).comp hx)

def hf (δ : G) (φ : G → ℂ) (q p : Q) : ℂ := if p ∈ goodT then Φf σ δ φ q p else 0

theorem measurable_hf {φ : G → ℂ} (hφm : Measurable φ) (q : Q) : Measurable (hf σ δ φ q) :=
  Measurable.ite measurableSet_goodT (measurable_Φf σ hφm q) measurable_const

theorem hf_ae_eq {φ : G → ℂ} (q : Q) : (hf σ δ φ q : Q → ℂ) =ᵐ[ρ ν] Φf σ δ φ q := by
  filter_upwards [(measure_eq_zero_iff_ae_notMem (μ := ρ ν)).1 (ρ_goodT_compl ν)] with p hp
  have hp' : p ∈ goodT := not_not.1 hp
  simp [hf, hp']

theorem hf_act (hab : a ≠ b) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b])
    (hδ₀₁ : (δ : Matrix (Fin 2) (Fin 2) E) 0 1 = 0) (hδ₁₀ : (δ : Matrix (Fin 2) (Fin 2) E) 1 0 = 0)
    (φ : G → ℂ) (q : Q) (t : A) (p : Q) :
    hf σ δ φ q (act (K := K) (L := L) (t : GF) p) = hf σ δ φ q p := by
  by_cases hp : p ∈ goodT
  · have hp' : act (K := K) (L := L) (t : GF) p ∈ goodT := (act_mem_goodT_iff hab hγ t p).2 hp
    simp only [hf, if_pos hp, if_pos hp', Φf]
    rw [← toTensorGL_mul_uGL hab hγ t hp, mul_assoc (AutomorphicForm.toTensorGL K L F (t : GF)) (uGL p) (sGL q),
      twConj_mul σ hab hγ hδ₀₁ hδ₁₀ t (uGL p * sGL q)]
  · have hp' : act (K := K) (L := L) (t : GF) p ∉ goodT := fun h => hp ((act_mem_goodT_iff hab hγ t p).1 h)
    simp [hf, hp, hp']

theorem mem_goodT_of_hf_ne_zero {φ : G → ℂ} {q p : Q} (h : hf σ δ φ q p ≠ 0) : p ∈ goodT := by
  by_contra hp; exact h (by simp [hf, hp])

theorem Φf_ne_zero_of_hf_ne_zero {φ : G → ℂ} {q p : Q} (h : hf σ δ φ q p ≠ 0) : Φf σ δ φ q p ≠ 0 := by
  intro h0; apply h; simp [hf, h0]

theorem section_w (hab : a ≠ b) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b]) (τ : Measure A)
    (τ' : @Measure Tw (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hττ' : @Measure.map _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ)
        (AutomorphicForm.glBorelOf E) Subtype.val τ' =
      Measure.map (fun s : A => AutomorphicForm.toTensorGL K L F (s : GF)) τ)
    {φ : G → ℂ} {w : G → ℝ} (hw : AutomorphicForm.IsTwistedSectionFnOn K L F σ δ τ' φ w) (q p : Q)
    (hp : hf σ δ φ q p ≠ 0) :
    ∫⁻ t : A, ENNReal.ofReal (w (uGL (act (K := K) (L := L) (t : GF) p) * sGL q)) ∂τ = 1 := by
  have hgood := mem_goodT_of_hf_ne_zero σ hp
  have h1 : ∀ t : A, uGL (act (K := K) (L := L) (t : GF) p) * sGL q =
      AutomorphicForm.toTensorGL K L F (t : GF) * (uGL p * sGL q) := by
    intro t; rw [← toTensorGL_mul_uGL hab hγ t hgood, mul_assoc (AutomorphicForm.toTensorGL K L F (t : GF)) (uGL p) (sGL q)]
  simp_rw [h1]
  exact lintegral_section σ τ τ' hττ' hw (uGL p * sGL q) (Φf_ne_zero_of_hf_ne_zero σ hp)

theorem section_β (hab : a ≠ b) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b]) (τ : Measure A)
    {β : G → ℝ} (hβ0 : ∀ x, 0 ≤ β x)
    (hβ : ∀ u : G, (u : Matrix (Fin 2) (Fin 2) E) 0 1 = 0 → (u : Matrix (Fin 2) (Fin 2) E) 1 0 = 0 →
      ∫ t : A, β (AutomorphicForm.toTensorGL K L F (t : GF) * u) ∂τ = 1)
    {φ : G → ℂ} (q p : Q) (hp : hf σ δ φ q p ≠ 0) :
    ∫⁻ t : A, ENNReal.ofReal (β (uGL (act (K := K) (L := L) (t : GF) p))) ∂τ = 1 := by
  have hgood := mem_goodT_of_hf_ne_zero σ hp
  simp_rw [← toTensorGL_mul_uGL hab hγ _ hgood]
  have h01 : ((uGL p : G) : Matrix (Fin 2) (Fin 2) E) 0 1 = 0 := by rw [coe_uGL_of_mem hgood]; rfl
  have h10 : ((uGL p : G) : Matrix (Fin 2) (Fin 2) E) 1 0 = 0 := by rw [coe_uGL_of_mem hgood]; rfl
  have h1 : ∫ t : A, β (AutomorphicForm.toTensorGL K L F (t : GF) * uGL p) ∂τ = 1 := hβ (uGL p) h01 h10
  have hint : Integrable (fun t : A => β (AutomorphicForm.toTensorGL K L F (t : GF) * uGL p)) τ := by
    by_contra h
    rw [integral_undef h] at h1
    exact zero_ne_one h1
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun t => hβ0 _), h1,
    ENNReal.ofReal_one]

variable (τ : Measure (AutomorphicForm.localCentralizer K v γ)) [τ.IsHaarMeasure]

theorem lintegral_enorm_unfold {cG : ℝ≥0∞} (hG : GHyp ν cG)
    (hab : a ≠ b) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b])
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ)
    (hδ₀₁ : (δ : Matrix (Fin 2) (Fin 2) E) 0 1 = 0) (hδ₁₀ : (δ : Matrix (Fin 2) (Fin 2) E) 1 0 = 0)
    (τ' : @Measure Tw (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hττ' : @Measure.map _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ)
        (AutomorphicForm.glBorelOf E) Subtype.val τ' =
      Measure.map (fun s : A => AutomorphicForm.toTensorGL K L F (s : GF)) τ)
    {β : G → ℝ} (hβm : Measurable β) (hβ0 : ∀ x, 0 ≤ β x)
    (hβ : ∀ u : G, (u : Matrix (Fin 2) (Fin 2) E) 0 1 = 0 → (u : Matrix (Fin 2) (Fin 2) E) 1 0 = 0 →
      ∫ t : A, β (AutomorphicForm.toTensorGL K L F (t : GF) * u) ∂τ = 1)
    {φ : G → ℂ} (hφm : Measurable φ) {w : G → ℝ} (hw : AutomorphicForm.IsTwistedSectionFnOn K L F σ δ τ' φ w) :
    ∫⁻ x, ‖φ (x⁻¹ * δ * AutomorphicForm.sigmaGL K L F σ x)‖ₑ * ENNReal.ofReal (w x)
        ∂(AutomorphicForm.semiLocalHaar K L v) =
      cG * ∫⁻ q, ∫⁻ p, D p * (‖Φf σ δ φ q p‖ₑ * ENNReal.ofReal (β (uGL p))) ∂ν² ∂ν² := by
  have h := AutomorphicForm.lintegral_enorm_twistedConj_mul_semiLocalHaar_eq_mul_lintegral_lintegral_torus_unipotentChart_of_isTwistedSectionFnOn_of_diagonal
    K L σ v ν cG hG a b hab γ hγ τ hτ δ hδ₀₁ hδ₁₀ τ' hττ' β hβm hβ0 hβ φ hφm w hw
  rw [h]
  congr 1
  refine lintegral_congr fun q => lintegral_congr fun p => ?_
  by_cases hp : IsUnit (!![p.1, 0; 0, p.2] : Matrix (Fin 2) (Fin 2) E).det
  · have h1 : IsUnit (tm p).det := hp
    have h2 : IsUnit (!![1 + q.1 * q.2, q.1; q.2, 1] : Matrix (Fin 2) (Fin 2) E).det := isUnit_det_sm q
    rw [dif_pos hp, dif_pos h2, D_of_mem (show p ∈ goodT from h1), mul_comm]
    simp only [Φf]
    rw [uGL_of_mem h1, ← mk''_sm q h2]
    rfl
  · rw [dif_neg hp, D_of_not (show p ∉ goodT from hp), zero_mul, zero_mul]

end Main

section Hecke

local notation "𝒦" => AutomorphicForm.semiLocalIntegralSet K L v

def Sset (g : G) : Set G := 𝒦 * {g} * 𝒦

omit [NumberField L] in
theorem mem_Sset_iff (g h : G) : h ∈ Sset (K := K) (L := L) (v := v) g ↔ ∃ k₁ ∈ 𝒦, ∃ k₂ ∈ 𝒦, h = k₁ * g * k₂ := by
  simp only [Sset, Set.mem_mul, Set.mem_singleton_iff]
  constructor
  · rintro ⟨_, ⟨k₁, hk₁, _, rfl, rfl⟩, k₂, hk₂, rfl⟩
    exact ⟨k₁, hk₁, k₂, hk₂, rfl⟩
  · rintro ⟨k₁, hk₁, k₂, hk₂, rfl⟩
    exact ⟨k₁ * g, ⟨k₁, hk₁, g, rfl, rfl⟩, k₂, hk₂, rfl⟩

theorem mem_semiLocalIntegers_iff (x : E) :
    x ∈ AutomorphicForm.semiLocalIntegers K L v ↔
      x ∈ (HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v).range := by
  rw [AlgHom.mem_range]; rfl

theorem mul_mem_K {k₁ k₂ : G} (h₁ : k₁ ∈ 𝒦) (h₂ : k₂ ∈ 𝒦) : k₁ * k₂ ∈ 𝒦 := by
  simp only [AutomorphicForm.semiLocalIntegralSet, AutomorphicForm.mem_integralUnitsSet,
    mem_semiLocalIntegers_iff] at h₁ h₂ ⊢
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [Units.val_mul, Matrix.mul_apply]
    exact Subalgebra.sum_mem _ fun k _ => Subalgebra.mul_mem _ (h₁.1 i k) (h₂.1 k j)
  · rw [mul_inv_rev, Units.val_mul, Matrix.mul_apply]
    exact Subalgebra.sum_mem _ fun k _ => Subalgebra.mul_mem _ (h₂.2 i k) (h₁.2 k j)

theorem inv_mem_K {k : G} (h : k ∈ 𝒦) : k⁻¹ ∈ 𝒦 := by
  simp only [AutomorphicForm.semiLocalIntegralSet, AutomorphicForm.mem_integralUnitsSet] at h ⊢
  rw [inv_inv]
  exact ⟨h.2, h.1⟩

theorem sigmaTensor_mem_semiLocalIntegers (σ : L ≃ₐ[K] L) {x : E} (hx : x ∈ AutomorphicForm.semiLocalIntegers K L v) :
    AutomorphicForm.sigmaTensor K L F σ x ∈ AutomorphicForm.semiLocalIntegers K L v := by
  obtain ⟨s, rfl⟩ := hx
  induction s using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; exact AutomorphicForm.zero_mem_semiLocalIntegers K L v
  | tmul b y =>
      rw [HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul, sigmaTensor_tmul]
      have hb : IsIntegral ℤ (σ (b : L)) := map_isIntegral_int σ.toAlgHom.toRingHom (RingOfIntegers.isIntegral_coe b)
      refine ⟨(⟨σ (b : L), hb⟩ : 𝓞 L) ⊗ₜ y, ?_⟩
      rw [HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul]
      rfl
  | add s t hs ht =>
      rw [map_add, map_add]
      rw [mem_semiLocalIntegers_iff] at hs ht ⊢
      exact Subalgebra.add_mem _ hs ht

theorem sigmaGL_mem_K (σ : L ≃ₐ[K] L) {k : G} (h : k ∈ 𝒦) : AutomorphicForm.sigmaGL K L F σ k ∈ 𝒦 := by
  simp only [AutomorphicForm.semiLocalIntegralSet, AutomorphicForm.mem_integralUnitsSet] at h ⊢
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [coe_sigmaGL, Matrix.map_apply]
    exact sigmaTensor_mem_semiLocalIntegers σ (h.1 i j)
  · rw [← map_inv, coe_sigmaGL, Matrix.map_apply]
    exact sigmaTensor_mem_semiLocalIntegers σ (h.2 i j)

theorem mul_mem_Sset {g h k : G} (hh : h ∈ Sset (K := K) (L := L) (v := v) g) (hk : k ∈ 𝒦) :
    h * k ∈ Sset (K := K) (L := L) (v := v) g := by
  obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := (mem_Sset_iff g h).1 hh
  exact (mem_Sset_iff g _).2 ⟨k₁, hk₁, k₂ * k, mul_mem_K hk₂ hk, by group⟩

theorem mem_mul_Sset {g h k : G} (hh : h ∈ Sset (K := K) (L := L) (v := v) g) (hk : k ∈ 𝒦) :
    k * h ∈ Sset (K := K) (L := L) (v := v) g := by
  obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := (mem_Sset_iff g h).1 hh
  exact (mem_Sset_iff g _).2 ⟨k * k₁, mul_mem_K hk hk₁, k₂, hk₂, by group⟩

theorem twConj_mul_mem_Sset_iff (σ : L ≃ₐ[K] L) (δ g x : G) {k : G} (hk : k ∈ 𝒦) :
    (x * k)⁻¹ * δ * AutomorphicForm.sigmaGL K L F σ (x * k) ∈ Sset (K := K) (L := L) (v := v) g ↔
      x⁻¹ * δ * AutomorphicForm.sigmaGL K L F σ x ∈ Sset (K := K) (L := L) (v := v) g := by
  have h1 : (x * k)⁻¹ * δ * AutomorphicForm.sigmaGL K L F σ (x * k) =
      k⁻¹ * (x⁻¹ * δ * AutomorphicForm.sigmaGL K L F σ x) * AutomorphicForm.sigmaGL K L F σ k := by
    rw [map_mul, mul_inv_rev]; group
  rw [h1]
  constructor
  · intro h
    have h2 := mem_mul_Sset (mul_mem_Sset h (inv_mem_K (sigmaGL_mem_K σ hk))) hk
    simpa [mul_assoc] using h2
  · intro h
    exact mul_mem_Sset (mem_mul_Sset h (inv_mem_K hk)) (sigmaGL_mem_K σ hk)

theorem isOpen_Sset (g : G) : IsOpen (Sset (K := K) (L := L) (v := v) g) := by
  haveI := isTopologicalGroup_GL (K := K) (L := L) (v := v)
  unfold Sset
  exact ((AutomorphicForm.isOpen_semiLocalIntegralSet K L v).mul_right).mul_right

theorem Sset_eq_image (g : G) :
    Sset (K := K) (L := L) (v := v) g = (fun p : G × G => p.1 * g * p.2) '' ((𝒦) ×ˢ (𝒦)) := by
  ext h
  rw [mem_Sset_iff]
  simp only [Set.mem_image, Set.mem_prod, Prod.exists]
  constructor
  · rintro ⟨k₁, hk₁, k₂, hk₂, rfl⟩; exact ⟨k₁, k₂, ⟨hk₁, hk₂⟩, rfl⟩
  · rintro ⟨k₁, k₂, ⟨hk₁, hk₂⟩, rfl⟩; exact ⟨k₁, hk₁, k₂, hk₂, rfl⟩

theorem isCompact_Sset (g : G) : IsCompact (Sset (K := K) (L := L) (v := v) g) := by
  haveI := isTopologicalGroup_GL (K := K) (L := L) (v := v)
  rw [Sset_eq_image]
  exact ((AutomorphicForm.isCompact_semiLocalIntegralSet K L v).prod
    (AutomorphicForm.isCompact_semiLocalIntegralSet K L v)).image (by fun_prop)

theorem smul_K_subset_Sset (g : G) : (fun x : G => g * x) '' (𝒦) ⊆ Sset (K := K) (L := L) (v := v) g := by
  rintro _ ⟨k, hk, rfl⟩
  exact (mem_Sset_iff g _).2 ⟨1, AutomorphicForm.one_mem_semiLocalIntegralSet K L v, k, hk, by rw [one_mul]⟩

section Meas

variable [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]

theorem measurableSet_Sset (g : G) : MeasurableSet (Sset (K := K) (L := L) (v := v) g) :=
  (isOpen_Sset g).measurableSet

theorem measurable_indicator_Sset (g : G) :
    Measurable ((Sset (K := K) (L := L) (v := v) g).indicator fun _ => (1 : ℂ)) :=
  (measurable_const.indicator (measurableSet_Sset g))

end Meas

end Hecke

section Slice

variable [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
variable (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure]

def V (g : G) (α β : E) : ℝ≥0∞ :=
  ν {ξ : E | ∃ h ∈ Sset (K := K) (L := L) (v := v) g, (h : Matrix (Fin 2) (Fin 2) E) = !![α, ξ; 0, β]}

theorem V_le_iSup (g : G) (α β : E) : V ν g α β ≤ ⨆ β', V ν g α β' := le_iSup (fun β' => V ν g α β') β

def Mset (g : G) : Set (Q × E) :=
  {w | ∃ h ∈ Sset (K := K) (L := L) (v := v) g, (h : Matrix (Fin 2) (Fin 2) E) = !![w.1.1, w.2; 0, w.1.2]}

theorem Mset_eq_image (g : G) : Mset (K := K) (L := L) (v := v) g =
    (fun h : G => ((((h : Matrix (Fin 2) (Fin 2) E) 0 0, (h : Matrix (Fin 2) (Fin 2) E) 1 1) : Q),
      (h : Matrix (Fin 2) (Fin 2) E) 0 1)) ''
      (Sset (K := K) (L := L) (v := v) g ∩ {h : G | (h : Matrix (Fin 2) (Fin 2) E) 1 0 = 0}) := by
  ext ⟨⟨α, β⟩, ξ⟩
  simp only [Mset, Set.mem_setOf_eq, Set.mem_image, Set.mem_inter_iff]
  constructor
  · rintro ⟨h, hh, hcoe⟩
    refine ⟨h, ⟨hh, by rw [hcoe]; rfl⟩, ?_⟩
    rw [hcoe]; rfl
  · rintro ⟨h, ⟨hh, h10⟩, hw⟩
    simp only [Prod.mk.injEq] at hw
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hw
    refine ⟨h, hh, ?_⟩
    ext i j; fin_cases i <;> fin_cases j <;> simp [h10]

theorem isClosed_Mset (g : G) : IsClosed (Mset (K := K) (L := L) (v := v) g) := by
  rw [Mset_eq_image]
  refine (IsCompact.image ?_ ?_).isClosed
  · exact (isCompact_Sset g).inter_right
      (isClosed_eq ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) E)).matrix_elem 1 0) continuous_const)
  · have hc := (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) E))
    exact (((hc.matrix_elem 0 0).prodMk (hc.matrix_elem 1 1)).prodMk (hc.matrix_elem 0 1))

theorem measurableSet_Mset (g : G) : MeasurableSet (Mset (K := K) (L := L) (v := v) g) :=
  (isClosed_Mset g).measurableSet

theorem sliceSet_eq_preimage (g : G) (α β : E) :
    {ξ : E | ∃ h ∈ Sset (K := K) (L := L) (v := v) g, (h : Matrix (Fin 2) (Fin 2) E) = !![α, ξ; 0, β]} =
      Prod.mk ((α, β) : Q) ⁻¹' Mset (K := K) (L := L) (v := v) g := rfl

theorem measurableSet_sliceSet (g : G) (α β : E) :
    MeasurableSet {ξ : E | ∃ h ∈ Sset (K := K) (L := L) (v := v) g, (h : Matrix (Fin 2) (Fin 2) E) = !![α, ξ; 0, β]} := by
  rw [sliceSet_eq_preimage]
  exact measurable_prodMk_left (measurableSet_Mset g)

theorem measurable_V (g : G) : Measurable fun z : Q => V ν g z.1 z.2 := by
  have : (fun z : Q => V ν g z.1 z.2) = fun z : Q => ν (Prod.mk z ⁻¹' Mset (K := K) (L := L) (v := v) g) := by
    funext z; rfl
  rw [this]
  exact measurable_measure_prodMk_left (measurableSet_Mset g)

theorem V_lt_top (g : G) (α β : E) : V ν g α β < ⊤ := by
  refine lt_of_le_of_lt (measure_mono ?_) (((isCompact_Sset (K := K) (L := L) (v := v) g).image
    ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) E)).matrix_elem 0 1)).measure_lt_top (μ := ν))
  rintro ξ ⟨h, hh, hcoe⟩
  refine ⟨h, hh, ?_⟩
  show (h : Matrix (Fin 2) (Fin 2) E) 0 1 = ξ
  rw [hcoe]; rfl

end Slice

section Twc

variable (σ : L ≃ₐ[K] L)

def twE (c p : E) : E := Ring.inverse p * c * AutomorphicForm.sigmaTensor K L F σ p

theorem isUnit_sigmaTensor {p : E} (hp : IsUnit p) : IsUnit (AutomorphicForm.sigmaTensor K L F σ p) :=
  hp.map _

theorem sigmaTensor_symm_apply (x : E) :
    AutomorphicForm.sigmaTensor K L F σ.symm (AutomorphicForm.sigmaTensor K L F σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul l c => rw [sigmaTensor_tmul, sigmaTensor_tmul, AlgEquiv.symm_apply_apply]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem sigmaTensor_apply_symm (x : E) :
    AutomorphicForm.sigmaTensor K L F σ (AutomorphicForm.sigmaTensor K L F σ.symm x) = x := by
  have h := sigmaTensor_symm_apply (K := K) (L := L) (v := v) σ.symm x
  rwa [AlgEquiv.symm_symm] at h

def sigmaAlgEquiv : E ≃ₐ[F] E :=
  AlgEquiv.ofLinearEquiv
    { toLinearMap := sigmaLin (K := K) (L := L) (v := v) σ
      invFun := AutomorphicForm.sigmaTensor K L F σ.symm
      left_inv := fun x => sigmaTensor_symm_apply σ x
      right_inv := fun x => sigmaTensor_apply_symm σ x }
    (map_one (AutomorphicForm.sigmaTensor K L F σ))
    (fun x y => map_mul (AutomorphicForm.sigmaTensor K L F σ) x y)

theorem sigmaAlgEquiv_apply (x : E) :
    sigmaAlgEquiv (K := K) (L := L) (v := v) σ x = AutomorphicForm.sigmaTensor K L F σ x := rfl

theorem algebraNorm_sigmaTensor (p : E) : Algebra.norm F (AutomorphicForm.sigmaTensor K L F σ p) = Algebra.norm F p := by
  rw [← sigmaAlgEquiv_apply σ p]
  exact Algebra.norm_eq_of_algEquiv (sigmaAlgEquiv σ) p

theorem algebraNorm_twE {c p : E} (hp : IsUnit p) : Algebra.norm F (twE (K := K) (L := L) (v := v) σ c p) = Algebra.norm F c := by
  have h1 : Algebra.norm F (Ring.inverse p) * Algebra.norm F p = 1 := by
    rw [← map_mul, Ring.inverse_mul_cancel p hp, map_one]
  unfold twE
  rw [map_mul, map_mul, algebraNorm_sigmaTensor]
  calc Algebra.norm F (Ring.inverse p) * Algebra.norm F c * Algebra.norm F p
      = Algebra.norm F (Ring.inverse p) * Algebra.norm F p * Algebra.norm F c := by ring
    _ = Algebra.norm F c := by rw [h1, one_mul]

theorem isUnit_twE {c p : E} (hc : IsUnit c) (hp : IsUnit p) : IsUnit (twE (K := K) (L := L) (v := v) σ c p) := by
  unfold twE
  have h1 : Ring.inverse p = ((hp.unit⁻¹ : Eˣ) : E) := by
    rw [← Ring.inverse_unit hp.unit, IsUnit.unit_spec]
  rw [h1]
  exact ((hp.unit⁻¹).isUnit.mul hc).mul (isUnit_sigmaTensor σ hp)

theorem coe_twConj_uGL_sGL {δ : G} (hδ₀₁ : (δ : Matrix (Fin 2) (Fin 2) E) 0 1 = 0)
    (hδ₁₀ : (δ : Matrix (Fin 2) (Fin 2) E) 1 0 = 0) {p : Q} (hp : p ∈ goodT) (x : E) :
    (((uGL p * sGL (x, 0))⁻¹ * δ * AutomorphicForm.sigmaGL K L F σ (uGL p * sGL (x, 0)) : G) :
        Matrix (Fin 2) (Fin 2) E) =
      !![twE σ ((δ : Matrix (Fin 2) (Fin 2) E) 0 0) p.1,
          twE σ ((δ : Matrix (Fin 2) (Fin 2) E) 0 0) p.1 * AutomorphicForm.sigmaTensor K L F σ x -
            twE σ ((δ : Matrix (Fin 2) (Fin 2) E) 1 1) p.2 * x;
        0, twE σ ((δ : Matrix (Fin 2) (Fin 2) E) 1 1) p.2] := by
  obtain ⟨hp1, hp2⟩ := (mem_goodT_iff p).1 hp
  have hδ : (δ : Matrix (Fin 2) (Fin 2) E) = !![(δ : Matrix (Fin 2) (Fin 2) E) 0 0, 0; 0, (δ : Matrix (Fin 2) (Fin 2) E) 1 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [hδ₀₁, hδ₁₀]

  have hinv : (((uGL p)⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) = !![Ring.inverse p.1, 0; 0, Ring.inverse p.2] := by
    have hl : (!![Ring.inverse p.1, 0; 0, Ring.inverse p.2] : Matrix (Fin 2) (Fin 2) E) * ((uGL p : G) : Matrix (Fin 2) (Fin 2) E) = 1 := by
      rw [coe_uGL_of_mem hp]
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [tm, Matrix.mul_apply, Fin.sum_univ_two, Ring.inverse_mul_cancel _ hp1, Ring.inverse_mul_cancel _ hp2]
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) E => M * (((uGL p)⁻¹ : G) : Matrix (Fin 2) (Fin 2) E)) hl
    simp only [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one, one_mul] at this
    exact this.symm
  rw [mul_inv_rev, map_mul, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, hinv, coe_sigmaGL, coe_sigmaGL,
    coe_uGL_of_mem hp, coe_sGL]
  conv_lhs => rw [hδ]
  have hsinv : (((sGL ((x, (0 : E)) : Q))⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) = smi (x, 0) := rfl
  rw [hsinv]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [tm, sm, smi, twE, Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, map_zero, map_one] <;> try ring

end Twc

section Absorb

variable [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
variable (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure]

local notation "𝒦" => AutomorphicForm.semiLocalIntegralSet K L v

theorem exists_absorb :
    ∃ Yn : E → ℝ≥0∞, Measurable Yn ∧ ∫⁻ y, Yn y ∂ν ≠ ⊤ ∧
      ∀ y : E, ∃ η c : E, IsUnit η ∧ Yn y = (wt (K := K) (L := L) (v := v) (η ^ 2))⁻¹ ∧
        ∃ k : G, k ∈ 𝒦 ∧ ∀ (x : E) (p : Q), p ∈ goodT →
          uGL p * sGL (x, y) = uGL (p.1 * Ring.inverse η, p.2 * η) * sGL (η ^ 2 * x + c, 0) * k := by
  obtain ⟨Y, hYm, hYfin, hY⟩ :=
    AutomorphicForm.exists_forall_lowerUnipotent_eq_diag_mul_unipotent_mul_mem_semiLocalIntegralSet K L v ν
  refine ⟨Y, hYm, hYfin, fun y => ?_⟩
  obtain ⟨η, t, hη, hYy, k, hk, hmat⟩ := hY y
  refine ⟨η, t, hη, ?_, k, hk, fun x p hp => ?_⟩
  · rw [hYy]; rfl
  · obtain ⟨hp1, hp2⟩ := (mem_goodT_iff p).1 hp
    have hηi : IsUnit (Ring.inverse η) := by
      have : Ring.inverse η = ((hη.unit⁻¹ : Eˣ) : E) := by rw [← Ring.inverse_unit hη.unit, IsUnit.unit_spec]
      rw [this]; exact Units.isUnit _
    have hp' : ((p.1 * Ring.inverse η, p.2 * η) : Q) ∈ goodT := by
      rw [mem_goodT_iff]; exact ⟨hp1.mul hηi, hp2.mul hη⟩
    have hkey : Ring.inverse η * η ^ 2 = η := by
      rw [pow_two, ← mul_assoc, Ring.inverse_mul_cancel η hη, one_mul]
    have hsm : sm ((x, y) : Q) = !![1, x; 0, 1] * !![1, 0; y, 1] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [sm, Matrix.mul_apply, Fin.sum_univ_two, mul_comm x y]
    have hM : tm p * (!![1, x; 0, 1] * (!![Ring.inverse η, 0; 0, η] * !![1, t; 0, 1])) =
        tm ((p.1 * Ring.inverse η, p.2 * η) : Q) * sm ((η ^ 2 * x + t, (0 : E)) : Q) := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [tm, sm, Matrix.mul_apply, Fin.sum_univ_two]
      · linear_combination (-(p.1 * x)) * hkey
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_uGL_of_mem hp, coe_uGL_of_mem hp', coe_sGL, coe_sGL, hsm,
      hmat, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    congr 1
    rw [← hM]
    simp only [Matrix.mul_assoc]

end Absorb

section Facts

variable [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
variable (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure]

theorem isCompact_window (n : ℕ) :
    IsCompact {y : F | ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ n ≤ ‖y‖ ∧ ‖y‖ ≤ 1} ∧
      (0 : F) ∉ {y : F | ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ n ≤ ‖y‖ ∧ ‖y‖ ≤ 1} := by
  have hq : 0 < ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ n := by
    apply pow_pos
    rw [inv_pos, Nat.cast_pos, Nat.pos_iff_ne_zero, ne_eq, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  constructor
  · have hcl : IsClosed {y : F | ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ n ≤ ‖y‖ ∧ ‖y‖ ≤ 1} :=
      (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
    refine (isCompact_closedBall (0 : F) 1).of_isClosed_subset hcl ?_
    intro y hy
    simpa [Metric.mem_closedBall, dist_zero_right] using hy.2
  · intro h
    simp only [Set.mem_setOf_eq, norm_zero] at h
    linarith [h.1]

def Uint : Set E :=
  {u : E | u ∈ AutomorphicForm.semiLocalIntegers K L v ∧ ∃ u' ∈ AutomorphicForm.semiLocalIntegers K L v, u * u' = 1}

theorem one_mem_Uint : (1 : E) ∈ Uint (K := K) (L := L) (v := v) :=
  ⟨AutomorphicForm.one_mem_semiLocalIntegers K L v, 1, AutomorphicForm.one_mem_semiLocalIntegers K L v, mul_one 1⟩

theorem isUnit_of_mem_Uint {u : E} (hu : u ∈ Uint (K := K) (L := L) (v := v)) : IsUnit u := by
  obtain ⟨-, u', -, h⟩ := hu
  exact IsUnit.of_mul_eq_one u' h

theorem det_mem_Uint {k : G} (hk : k ∈ AutomorphicForm.semiLocalIntegralSet K L v) :
    ((Matrix.GeneralLinearGroup.det k : Eˣ) : E) ∈ Uint (K := K) (L := L) (v := v) := by
  simp only [AutomorphicForm.semiLocalIntegralSet, AutomorphicForm.mem_integralUnitsSet, mem_semiLocalIntegers_iff] at hk
  have hmem : ∀ M : Matrix (Fin 2) (Fin 2) E,
      (∀ i j, M i j ∈ (HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v).range) →
        M.det ∈ AutomorphicForm.semiLocalIntegers K L v := by
    intro M hM
    rw [mem_semiLocalIntegers_iff, Matrix.det_fin_two]
    exact Subalgebra.sub_mem _ (Subalgebra.mul_mem _ (hM 0 0) (hM 1 1)) (Subalgebra.mul_mem _ (hM 0 1) (hM 1 0))
  refine ⟨hmem _ hk.1, ((Matrix.GeneralLinearGroup.det k⁻¹ : Eˣ) : E), hmem _ hk.2, ?_⟩
  rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

theorem Uint_eq_image : Uint (K := K) (L := L) (v := v) =
    Prod.fst '' {z : E × E | z ∈ (AutomorphicForm.semiLocalIntegers K L v) ×ˢ (AutomorphicForm.semiLocalIntegers K L v) ∧ z.1 * z.2 = 1} := by
  ext u
  simp only [Uint, Set.mem_setOf_eq, Set.mem_image, Set.mem_prod, Prod.exists, exists_and_right, exists_eq_right]
  constructor
  · rintro ⟨hu, u', hu', h⟩; exact ⟨u', ⟨⟨hu, hu'⟩, h⟩⟩
  · rintro ⟨u', ⟨⟨hu, hu'⟩, h⟩⟩; exact ⟨hu, u', hu', h⟩

theorem isCompact_Uint : IsCompact (Uint (K := K) (L := L) (v := v)) := by
  rw [Uint_eq_image]
  refine IsCompact.image ?_ continuous_fst
  refine (((AutomorphicForm.isCompact_semiLocalIntegers K L v).prod
    (AutomorphicForm.isCompact_semiLocalIntegers K L v)).inter_right ?_)
  exact isClosed_eq (continuous_fst.mul continuous_snd) continuous_const

theorem inv_mem_Uint {u : E} (hu : u ∈ Uint (K := K) (L := L) (v := v)) :
    ∃ u' ∈ Uint (K := K) (L := L) (v := v), u * u' = 1 := by
  obtain ⟨hu, u', hu', h⟩ := hu
  exact ⟨u', ⟨hu', u, hu, by rw [mul_comm, h]⟩, h⟩

theorem mul_mem_semiLocalIntegers {x y : E} (hx : x ∈ AutomorphicForm.semiLocalIntegers K L v)
    (hy : y ∈ AutomorphicForm.semiLocalIntegers K L v) : x * y ∈ AutomorphicForm.semiLocalIntegers K L v := by
  rw [mem_semiLocalIntegers_iff] at hx hy ⊢
  exact Subalgebra.mul_mem _ hx hy

include ν in

theorem norm_algebraNorm_eq_one_of_mem_Uint {u : E} (hu : u ∈ Uint (K := K) (L := L) (v := v)) :
    ‖Algebra.norm F u‖ = 1 := by
  set O : Set E := AutomorphicForm.semiLocalIntegers K L v with hO
  have hO0 : ν O ≠ 0 := (AutomorphicForm.isOpen_semiLocalIntegers K L v).measure_ne_zero ν ⟨1, AutomorphicForm.one_mem_semiLocalIntegers K L v⟩
  have hOtop : ν O ≠ ⊤ := (AutomorphicForm.isCompact_semiLocalIntegers K L v).measure_lt_top.ne
  have hOm : MeasurableSet O := (AutomorphicForm.isOpen_semiLocalIntegers K L v).measurableSet

  have key : ∀ c : E, c ∈ Uint (K := K) (L := L) (v := v) → wt (K := K) (L := L) (v := v) c ≤ 1 := by
    intro c hc
    have hcu : IsUnit c := isUnit_of_mem_Uint hc
    have hsub : O ⊆ (fun x : E => c * x) ⁻¹' O := fun x hx => mul_mem_semiLocalIntegers hc.1 hx
    have h1 : ν O ≤ (wt (K := K) (L := L) (v := v) c)⁻¹ * ν O := by
      calc ν O ≤ ν ((fun x : E => c * x) ⁻¹' O) := measure_mono hsub
        _ = (Measure.map (fun x : E => c * x) ν) O := (Measure.map_apply (measurable_const_mul c) hOm).symm
        _ = (wt (K := K) (L := L) (v := v) c)⁻¹ * ν O := by rw [map_mul_left ν hcu, Measure.smul_apply, smul_eq_mul]
    have h2 : 1 ≤ (wt (K := K) (L := L) (v := v) c)⁻¹ := by
      rw [← ENNReal.mul_le_mul_iff_left hO0 hOtop, one_mul]; exact h1
    exact ENNReal.one_le_inv.1 h2
  obtain ⟨u', hu', huu'⟩ := inv_mem_Uint hu
  have h1 := key u hu
  have h2 := key u' hu'
  have h3 : wt (K := K) (L := L) (v := v) u * wt u' = 1 := by
    rw [← wt_mul, huu', wt, map_one, norm_one, ENNReal.ofReal_one]
  have h4 : wt (K := K) (L := L) (v := v) u = 1 := by
    refine le_antisymm h1 ?_
    calc (1 : ℝ≥0∞) = wt (K := K) (L := L) (v := v) u * wt u' := h3.symm
      _ ≤ wt (K := K) (L := L) (v := v) u * 1 := by gcongr
      _ = _ := mul_one _
  have : ENNReal.ofReal ‖Algebra.norm F u‖ = 1 := h4
  rwa [ENNReal.ofReal_eq_one] at this

theorem exists_diag_mem_K {ε : E} (hε : ε ∈ Uint (K := K) (L := L) (v := v)) :
    ∃ d : G, d ∈ AutomorphicForm.semiLocalIntegralSet K L v ∧ (d : Matrix (Fin 2) (Fin 2) E) = !![ε, 0; 0, 1] := by
  obtain ⟨hε1, ε', hε', h⟩ := hε
  refine ⟨⟨!![ε, 0; 0, 1], !![ε', 0; 0, 1], ?_, ?_⟩, ?_, rfl⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm ε' ε, h]
  · simp only [AutomorphicForm.semiLocalIntegralSet, AutomorphicForm.mem_integralUnitsSet]
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · fin_cases i <;> fin_cases j <;>
        simp [hε1, AutomorphicForm.zero_mem_semiLocalIntegers, AutomorphicForm.one_mem_semiLocalIntegers]
    · show (!![ε', 0; 0, 1] : Matrix (Fin 2) (Fin 2) E) i j ∈ _
      fin_cases i <;> fin_cases j <;>
        simp [hε', AutomorphicForm.zero_mem_semiLocalIntegers, AutomorphicForm.one_mem_semiLocalIntegers]

theorem setOf_slice_mul_Uint {ε : E} (hε : ε ∈ Uint (K := K) (L := L) (v := v)) (g : G) (α β : E) :
    {ξ : E | ∃ h ∈ Sset (K := K) (L := L) (v := v) g, (h : Matrix (Fin 2) (Fin 2) E) = !![α * ε, ξ; 0, β]} ⊆
      {ξ : E | ∃ h ∈ Sset (K := K) (L := L) (v := v) g, (h : Matrix (Fin 2) (Fin 2) E) = !![α, ξ; 0, β]} := by
  obtain ⟨ε', hε', hεε'⟩ := inv_mem_Uint hε
  obtain ⟨d, hd, hdcoe⟩ := exists_diag_mem_K hε'
  rintro ξ ⟨h, hh, hcoe⟩
  refine ⟨h * d, mul_mem_Sset hh hd, ?_⟩
  rw [Units.val_mul, hcoe, hdcoe]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_assoc, hεε']

theorem V_mul_Uint {ε : E} (hε : ε ∈ Uint (K := K) (L := L) (v := v)) (g : G) (α β : E) :
    V ν g (α * ε) β = V ν g α β := by
  obtain ⟨ε', hε', hεε'⟩ := inv_mem_Uint hε
  unfold V
  refine le_antisymm (measure_mono (setOf_slice_mul_Uint hε g α β)) ?_
  have h := setOf_slice_mul_Uint (K := K) (L := L) (v := v) hε' g (α * ε) β
  rw [mul_assoc, hεε', mul_one] at h
  exact measure_mono h

theorem mul_mem_Uint {u w : E} (hu : u ∈ Uint (K := K) (L := L) (v := v)) (hw : w ∈ Uint (K := K) (L := L) (v := v)) :
    u * w ∈ Uint (K := K) (L := L) (v := v) := by
  obtain ⟨hu1, u', hu', hu2⟩ := hu
  obtain ⟨hw1, w', hw', hw2⟩ := hw
  refine ⟨mul_mem_semiLocalIntegers hu1 hw1, u' * w', mul_mem_semiLocalIntegers hu' hw', ?_⟩
  calc u * w * (u' * w') = (u * u') * (w * w') := by ring
    _ = 1 := by rw [hu2, hw2, one_mul]

theorem exists_diag_mem_K' {ε : E} (hε : ε ∈ Uint (K := K) (L := L) (v := v)) :
    ∃ d : G, d ∈ AutomorphicForm.semiLocalIntegralSet K L v ∧ (d : Matrix (Fin 2) (Fin 2) E) = !![1, 0; 0, ε] := by
  obtain ⟨hε1, ε', hε', h⟩ := hε
  refine ⟨⟨!![1, 0; 0, ε], !![1, 0; 0, ε'], ?_, ?_⟩, ?_, rfl⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm ε' ε, h]
  · simp only [AutomorphicForm.semiLocalIntegralSet, AutomorphicForm.mem_integralUnitsSet]
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · fin_cases i <;> fin_cases j <;>
        simp [hε1, AutomorphicForm.zero_mem_semiLocalIntegers, AutomorphicForm.one_mem_semiLocalIntegers]
    · show (!![1, 0; 0, ε'] : Matrix (Fin 2) (Fin 2) E) i j ∈ _
      fin_cases i <;> fin_cases j <;>
        simp [hε', AutomorphicForm.zero_mem_semiLocalIntegers, AutomorphicForm.one_mem_semiLocalIntegers]

set_option maxHeartbeats 20000000 in

theorem V_mul_Uint_right {ε : E} (hε : ε ∈ Uint (K := K) (L := L) (v := v)) (g : G) (α β : E) :
    V ν g α (β * ε) = V ν g α β := by
  obtain ⟨ε', hε', hεε'⟩ := inv_mem_Uint hε
  have hε'u : IsUnit ε' := isUnit_of_mem_Uint hε'
  obtain ⟨d, hd, hdcoe⟩ := exists_diag_mem_K' (K := K) (L := L) (v := v) hε
  obtain ⟨d', hd', hd'coe⟩ := exists_diag_mem_K' (K := K) (L := L) (v := v) hε'
  have hset : {ξ : E | ∃ h ∈ Sset (K := K) (L := L) (v := v) g, (h : Matrix (Fin 2) (Fin 2) E) = !![α, ξ; 0, β * ε]} =
      (fun ξ => ε' * ξ) ⁻¹' {ξ : E | ∃ h ∈ Sset (K := K) (L := L) (v := v) g, (h : Matrix (Fin 2) (Fin 2) E) = !![α, ξ; 0, β]} := by
    ext ξ
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    constructor
    · rintro ⟨h, hh, hcoe⟩
      refine ⟨h * d', mul_mem_Sset hh hd', ?_⟩
      rw [Units.val_mul, hcoe, hd'coe]
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm ξ ε', mul_assoc, hεε']
    · rintro ⟨h, hh, hcoe⟩
      refine ⟨h * d, mul_mem_Sset hh hd, ?_⟩
      rw [Units.val_mul, hcoe, hdcoe]
      have : ε' * ξ * ε = ξ := by rw [mul_comm ε' ξ, mul_assoc, mul_comm ε' ε, hεε', mul_one]
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, this]
  unfold V
  rw [hset, ← Measure.map_apply (measurable_const_mul ε') (measurableSet_sliceSet g α β), map_mul_left ν hε'u,
    Measure.smul_apply, smul_eq_mul]
  have : wt (K := K) (L := L) (v := v) ε' = 1 := by
    rw [wt, norm_algebraNorm_eq_one_of_mem_Uint ν hε', ENNReal.ofReal_one]
  rw [this, inv_one, one_mul]

theorem exists_mass_Uint :
    ∃ m₀ : ℝ≥0∞, m₀ ≠ 0 ∧ m₀ ≠ ⊤ ∧ ∀ α : E, IsUnit α →
      (ν.withDensity fun b => ENNReal.ofReal ‖Algebra.norm F b‖⁻¹) {b : E | ∃ u ∈ Uint (K := K) (L := L) (v := v), b = α * u} = m₀ := by
  set m : Measure E := ν.withDensity fun b => ENNReal.ofReal ‖Algebra.norm F b‖⁻¹ with hm

  have hD : ∀ {c : E}, IsUnit c → ∀ b : E,
      ENNReal.ofReal ‖Algebra.norm F b‖⁻¹ = wt (K := K) (L := L) (v := v) c * ENNReal.ofReal ‖Algebra.norm F (c * b)‖⁻¹ := by
    intro c hc b
    have hc0 : ‖Algebra.norm F c‖ ≠ 0 := norm_ne_zero_iff.2 ((isUnit_iff_norm_ne_zero c).1 hc)
    rw [wt, map_mul, norm_mul, mul_inv, ← ENNReal.ofReal_mul (norm_nonneg _), ← mul_assoc,
      mul_inv_cancel₀ hc0, one_mul]
  have hmeasD : Measurable fun b : E => ENNReal.ofReal ‖Algebra.norm F b‖⁻¹ :=
    ENNReal.measurable_ofReal.comp (continuous_algebraNorm.norm).measurable.inv

  have hinv : ∀ {c : E}, IsUnit c → ∀ {S : Set E}, MeasurableSet S → m ((fun b => c * b) ⁻¹' S) = m S := by
    intro c hc S hS
    rw [hm, withDensity_apply _ ((measurable_const_mul c) hS), withDensity_apply _ hS,
      ← lintegral_indicator hS, ← lintegral_indicator ((measurable_const_mul c) hS)]
    have h1 : ∀ b : E, ((fun b => c * b) ⁻¹' S).indicator (fun b => ENNReal.ofReal ‖Algebra.norm F b‖⁻¹) b =
        wt (K := K) (L := L) (v := v) c * S.indicator (fun b => ENNReal.ofReal ‖Algebra.norm F b‖⁻¹) (c * b) := by
      intro b
      by_cases hb : c * b ∈ S
      · rw [Set.indicator_of_mem (show b ∈ (fun b => c * b) ⁻¹' S from hb), Set.indicator_of_mem hb, hD hc b]
      · rw [Set.indicator_of_notMem (show b ∉ (fun b => c * b) ⁻¹' S from hb), Set.indicator_of_notMem hb, mul_zero]
    simp_rw [h1]
    rw [lintegral_const_mul' _ _ (wt_ne_top _),
      lintegral_comp_mul_left ν (S.indicator fun b => ENNReal.ofReal ‖Algebra.norm F b‖⁻¹) (hmeasD.indicator hS) hc,
      ← mul_assoc, ENNReal.mul_inv_cancel (wt_ne_zero hc) (wt_ne_top _), one_mul]

  have hUopen : IsOpen (Uint (K := K) (L := L) (v := v)) := by
    have hU : Uint (K := K) (L := L) (v := v) =
        {u : E | IsUnit u ∧ u ∈ AutomorphicForm.semiLocalIntegers K L v ∧ Ring.inverse u ∈ AutomorphicForm.semiLocalIntegers K L v} := by
      ext u
      constructor
      · intro hu
        obtain ⟨hu1, u', hu', h⟩ := hu
        have hunit : IsUnit u := IsUnit.of_mul_eq_one u' h
        refine ⟨hunit, hu1, ?_⟩
        have : Ring.inverse u = u' := by
          calc Ring.inverse u = Ring.inverse u * (u * u') := by rw [h, mul_one]
            _ = u' := by rw [← mul_assoc, Ring.inverse_mul_cancel u hunit, one_mul]
        rw [this]; exact hu'
      · rintro ⟨hunit, hu1, hinv'⟩
        exact ⟨hu1, Ring.inverse u, hinv', Ring.mul_inverse_cancel u hunit⟩
    rw [hU]
    have hopen_units : IsOpen {x : E | IsUnit x} := isOpen_units
    have hcont : Continuous fun x : {x : E // IsUnit x} => Ring.inverse (x : E) :=
      continuous_ringInverse_comp continuous_subtype_val fun x => x.2
    have hO := AutomorphicForm.isOpen_semiLocalIntegers K L v
    have h1 : IsOpen {x : {x : E // IsUnit x} | (x : E) ∈ AutomorphicForm.semiLocalIntegers K L v ∧
        Ring.inverse (x : E) ∈ AutomorphicForm.semiLocalIntegers K L v} :=
      (hO.preimage continuous_subtype_val).inter (hO.preimage hcont)
    have h2 := hopen_units.isOpenMap_subtype_val _ h1
    have hEq : {u : E | IsUnit u ∧ u ∈ AutomorphicForm.semiLocalIntegers K L v ∧
        Ring.inverse u ∈ AutomorphicForm.semiLocalIntegers K L v} =
        Subtype.val '' {x : {x : E // IsUnit x} | (x : E) ∈ AutomorphicForm.semiLocalIntegers K L v ∧
          Ring.inverse (x : E) ∈ AutomorphicForm.semiLocalIntegers K L v} := by
      ext u
      constructor
      · rintro ⟨hu, h1, h2⟩; exact ⟨⟨u, hu⟩, ⟨h1, h2⟩, rfl⟩
      · rintro ⟨x, ⟨h1, h2⟩, rfl⟩; exact ⟨x.2, h1, h2⟩
    rw [hEq]; exact h2
  have hUm : MeasurableSet (Uint (K := K) (L := L) (v := v)) := hUopen.measurableSet

  have hmU : m (Uint (K := K) (L := L) (v := v)) = ν (Uint (K := K) (L := L) (v := v)) := by
    rw [hm, withDensity_apply _ hUm]
    have : ∀ b ∈ Uint (K := K) (L := L) (v := v), ENNReal.ofReal ‖Algebra.norm F b‖⁻¹ = 1 := by
      intro b hb; rw [norm_algebraNorm_eq_one_of_mem_Uint ν hb, inv_one, ENNReal.ofReal_one]
    rw [setLIntegral_congr_fun hUm this, setLIntegral_one]
  refine ⟨m (Uint (K := K) (L := L) (v := v)), ?_, ?_, ?_⟩
  · rw [hmU]; exact hUopen.measure_ne_zero ν ⟨1, one_mem_Uint⟩
  · rw [hmU]; exact (isCompact_Uint.measure_lt_top).ne
  · intro α hα
    have hset : {b : E | ∃ u ∈ Uint (K := K) (L := L) (v := v), b = α * u} =
        (fun b => Ring.inverse α * b) ⁻¹' Uint (K := K) (L := L) (v := v) := by
      ext b
      simp only [Set.mem_setOf_eq, Set.mem_preimage]
      constructor
      · rintro ⟨u, hu, rfl⟩
        rwa [← mul_assoc, Ring.inverse_mul_cancel α hα, one_mul]
      · intro hb
        exact ⟨Ring.inverse α * b, hb, by rw [← mul_assoc, Ring.mul_inverse_cancel α hα, one_mul]⟩
    rw [hset]
    have hαi : IsUnit (Ring.inverse α) := by
      have : Ring.inverse α = ((hα.unit⁻¹ : Eˣ) : E) := by rw [← Ring.inverse_unit hα.unit, IsUnit.unit_spec]
      rw [this]; exact Units.isUnit _
    exact hinv hαi hUm

theorem one_le_semiLocalHaar_Sset_and_ne_top (g : G) :
    1 ≤ AutomorphicForm.semiLocalHaar K L v (Sset (K := K) (L := L) (v := v) g) ∧
      AutomorphicForm.semiLocalHaar K L v (Sset (K := K) (L := L) (v := v) g) ≠ ⊤ := by
  haveI := isTopologicalGroup_GL (K := K) (L := L) (v := v)
  constructor
  · have h1 : AutomorphicForm.semiLocalHaar K L v ((fun x : G => g * x) '' AutomorphicForm.semiLocalIntegralSet K L v) = 1 := by
      have : (fun x : G => g * x) '' AutomorphicForm.semiLocalIntegralSet K L v =
          (fun x : G => g⁻¹ * x) ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v := by
        ext x; simp only [Set.mem_image, Set.mem_preimage]
        constructor
        · rintro ⟨k, hk, rfl⟩; simpa using hk
        · intro hx; exact ⟨g⁻¹ * x, hx, by group⟩
      rw [this, measure_preimage_mul, AutomorphicForm.semiLocalHaar_semiLocalIntegralSet]
    rw [← h1]
    exact measure_mono (smul_K_subset_Sset g)
  · exact (isCompact_Sset g).measure_lt_top.ne

end Facts

section Assembly

variable [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
variable (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure]
variable {a b : v.adicCompletion K} {γ : GL (Fin 2) (v.adicCompletion K)}
variable (σ : L ≃ₐ[K] L) {δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)}

open scoped Classical

attribute [local instance] borelSpace_Q t2Space_GF secondCountableTopology_GF
  AutomorphicForm.locallyCompactSpace_localGL AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel
  AutomorphicForm.localCentralizerBorel borelSpace_A locallyCompactSpace_A secondCountableTopology_A

local notation "ν²" => Measure.prod ν ν
local notation "A" => AutomorphicForm.localCentralizer K v γ
local notation "Tw" => AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ
local notation "𝒦" => AutomorphicForm.semiLocalIntegralSet K L v

variable (τ : Measure (AutomorphicForm.localCentralizer K v γ)) [τ.IsHaarMeasure]

def φS (g : G) : G → ℂ := (Sset (K := K) (L := L) (v := v) g).indicator fun _ => (1 : ℂ)

theorem measurable_φS (g : G) : Measurable (φS (K := K) (L := L) (v := v) g) :=
  measurable_indicator_Sset g

theorem enorm_φS (g x : G) :
    ‖φS (K := K) (L := L) (v := v) g x‖ₑ = (Sset (K := K) (L := L) (v := v) g).indicator (fun _ => (1 : ℝ≥0∞)) x := by
  unfold φS
  by_cases hx : x ∈ Sset (K := K) (L := L) (v := v) g <;> simp [hx]

def Q0 (g δ : G) (β : G → ℝ) : ℝ≥0∞ :=
  ∫⁻ p, D p * (V ν g (twE σ ((δ : Matrix (Fin 2) (Fin 2) E) 0 0) p.1) (twE σ ((δ : Matrix (Fin 2) (Fin 2) E) 1 1) p.2) *
    ENNReal.ofReal (β (uGL p))) ∂ν²

set_option maxHeartbeats 20000000 in
theorem measurableMul₂_E : MeasurableMul₂ E := inferInstance
set_option maxHeartbeats 20000000 in
theorem measurableAdd₂_E : MeasurableAdd₂ E := inferInstance
set_option maxHeartbeats 20000000 in
theorem measurableSub₂_E : MeasurableSub₂ E := inferInstance

attribute [local instance] measurableMul₂_E measurableAdd₂_E measurableSub₂_E

theorem measurable_ringInverse : Measurable (Ring.inverse : E → E) := by
  refine measurable_of_restrict_of_restrict_compl (isOpen_units (K := K) (L := L) (v := v)).measurableSet ?_ ?_
  · have hc : Continuous (({x : E | IsUnit x}).restrict (Ring.inverse : E → E)) :=
      continuous_ringInverse_comp continuous_subtype_val (fun x => x.2)
    exact hc.measurable
  · have : ({x : E | IsUnit x}ᶜ).domRestrict (Ring.inverse : E → E) = fun _ => 0 := by
      funext x; exact Ring.inverse_non_unit _ x.2
    rw [this]; exact measurable_const

theorem measurable_twE (c : E) : Measurable fun p : E => twE (K := K) (L := L) (v := v) σ c p :=
  ((measurable_ringInverse.mul_const c).mul (continuous_sigmaTensor (v := v) σ).measurable)

theorem lintegral_comp_mul_pair {c₁ c₂ : E} (h₁ : IsUnit c₁) (h₂ : IsUnit c₂) {H : Q → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ p, H (c₁ * p.1, c₂ * p.2) ∂ν² = (wt (K := K) (L := L) (v := v) c₁)⁻¹ * (wt (K := K) (L := L) (v := v) c₂)⁻¹ * ∫⁻ p, H p ∂ν² := by
  have hm : Measurable fun p : Q => H (c₁ * p.1, c₂ * p.2) :=
    hH.comp ((measurable_fst.const_mul c₁).prodMk (measurable_snd.const_mul c₂))
  have h1 : ∫⁻ p, H (c₁ * p.1, c₂ * p.2) ∂ν² = ∫⁻ x, ∫⁻ y, H (c₁ * x, c₂ * y) ∂ν ∂ν := by
    rw [lintegral_prod _ hm.aemeasurable]
  have h2 : ∀ x : E, ∫⁻ y, H (c₁ * x, c₂ * y) ∂ν = (wt (K := K) (L := L) (v := v) c₂)⁻¹ * ∫⁻ y, H (c₁ * x, y) ∂ν := fun x =>
    lintegral_comp_mul_left ν (fun y => H (c₁ * x, y)) (hH.comp (measurable_const.prodMk measurable_id)) h₂
  have h3 : Measurable fun x : E => ∫⁻ y, H (x, y) ∂ν := hH.lintegral_prod_right'
  have h4 : ∫⁻ x, ∫⁻ y, H (c₁ * x, y) ∂ν ∂ν = (wt (K := K) (L := L) (v := v) c₁)⁻¹ * ∫⁻ x, ∫⁻ y, H (x, y) ∂ν ∂ν :=
    lintegral_comp_mul_left ν (fun x => ∫⁻ y, H (x, y) ∂ν) h3 h₁
  rw [h1]
  simp_rw [h2]
  rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 (wt_ne_zero h₂)), h4, lintegral_prod _ hH.aemeasurable,
    ← mul_assoc, mul_comm ((wt _)⁻¹)]

theorem section_β_of_mem (hab : a ≠ b) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b])
    {β : G → ℝ} (hβ0 : ∀ x, 0 ≤ β x)
    (hβ : ∀ u : G, (u : Matrix (Fin 2) (Fin 2) E) 0 1 = 0 → (u : Matrix (Fin 2) (Fin 2) E) 1 0 = 0 →
      ∫ t : A, β (AutomorphicForm.toTensorGL K L F (t : GF) * u) ∂τ = 1)
    {p : Q} (hgood : p ∈ goodT) :
    ∫⁻ t : A, ENNReal.ofReal (β (uGL (act (K := K) (L := L) (t : GF) p))) ∂τ = 1 := by
  simp_rw [← toTensorGL_mul_uGL hab hγ _ hgood]
  have h01 : ((uGL p : G) : Matrix (Fin 2) (Fin 2) E) 0 1 = 0 := by rw [coe_uGL_of_mem hgood]; rfl
  have h10 : ((uGL p : G) : Matrix (Fin 2) (Fin 2) E) 1 0 = 0 := by rw [coe_uGL_of_mem hgood]; rfl
  have h1 : ∫ t : A, β (AutomorphicForm.toTensorGL K L F (t : GF) * uGL p) ∂τ = 1 := hβ (uGL p) h01 h10
  have hint : Integrable (fun t : A => β (AutomorphicForm.toTensorGL K L F (t : GF) * uGL p)) τ := by
    by_contra h
    rw [integral_undef h] at h1
    exact zero_ne_one h1
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun t => hβ0 _), h1,
    ENNReal.ofReal_one]

theorem mul_twE {c p : E} (hp : IsUnit p) :
    p * twE (K := K) (L := L) (v := v) σ c p = c * AutomorphicForm.sigmaTensor K L F σ p := by
  unfold twE
  rw [← mul_assoc, ← mul_assoc, Ring.mul_inverse_cancel p hp, one_mul]

theorem twE_emb_mul (hab : a ≠ b) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b]) (t : A)
    (c : E) {p : E} (hp : IsUnit p) :
    twE (K := K) (L := L) (v := v) σ c (c1 (K := K) (L := L) (t : GF) * p) = twE σ c p ∧
      twE (K := K) (L := L) (v := v) σ c (c2 (K := K) (L := L) (t : GF) * p) = twE σ c p := by
  have key : ∀ {e : E}, IsUnit e → AutomorphicForm.sigmaTensor K L F σ e = e →
      twE (K := K) (L := L) (v := v) σ c (e * p) = twE σ c p := by
    intro e he hσe
    have hep : IsUnit (e * p) := he.mul hp
    apply hep.mul_left_cancel
    rw [mul_twE σ hep, map_mul, hσe, mul_assoc, mul_twE σ hp]
    ring
  exact ⟨key (isUnit_c1 hab hγ t) (sigmaTensor_emb σ _), key (isUnit_c2 hab hγ t) (sigmaTensor_emb σ _)⟩

theorem enorm_φS_twConj_mul (g X : G) {k : G} (hk : k ∈ 𝒦) :
    ‖φS (K := K) (L := L) (v := v) g ((X * k)⁻¹ * δ * AutomorphicForm.sigmaGL K L F σ (X * k))‖ₑ =
      ‖φS (K := K) (L := L) (v := v) g (X⁻¹ * δ * AutomorphicForm.sigmaGL K L F σ X)‖ₑ := by
  rw [enorm_φS, enorm_φS]
  by_cases h : X⁻¹ * δ * AutomorphicForm.sigmaGL K L F σ X ∈ Sset (K := K) (L := L) (v := v) g
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((twConj_mul_mem_Sset_iff σ δ g X hk).2 h)]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((twConj_mul_mem_Sset_iff σ δ g X hk).1 h'))]

def sliceInd (g : G) (α β ξ : E) : ℝ≥0∞ :=
  {ξ' : E | ∃ h ∈ Sset (K := K) (L := L) (v := v) g, (h : Matrix (Fin 2) (Fin 2) E) = !![α, ξ'; 0, β]}.indicator (fun _ => 1) ξ

theorem lintegral_sliceInd (g : G) (α β : E) : ∫⁻ ξ, sliceInd (K := K) (L := L) (v := v) g α β ξ ∂ν = V ν g α β := by
  unfold sliceInd V
  rw [lintegral_indicator (measurableSet_sliceSet g α β), setLIntegral_one]

theorem sliceInd_eq_indicator_Mset (g : G) (α β ξ : E) :
    sliceInd (K := K) (L := L) (v := v) g α β ξ = (Mset (K := K) (L := L) (v := v) g).indicator (fun _ => (1 : ℝ≥0∞)) (((α, β) : Q), ξ) := by
  simp only [sliceInd, Mset, Set.indicator, Set.mem_setOf_eq]

theorem measurable_sliceInd (g : G) :
    Measurable fun z : Q × E => sliceInd (K := K) (L := L) (v := v) g z.1.1 z.1.2 z.2 := by
  have : (fun z : Q × E => sliceInd (K := K) (L := L) (v := v) g z.1.1 z.1.2 z.2) =
      (Mset (K := K) (L := L) (v := v) g).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext z; rw [sliceInd_eq_indicator_Mset]
  rw [this]
  exact measurable_const.indicator (measurableSet_Mset g)

theorem enorm_φS_twConj_uGL_sGL (g : G)
    (hδ₀₁ : (δ : Matrix (Fin 2) (Fin 2) E) 0 1 = 0) (hδ₁₀ : (δ : Matrix (Fin 2) (Fin 2) E) 1 0 = 0)
    {q : Q} (hq : q ∈ goodT) (x : E) :
    ‖φS (K := K) (L := L) (v := v) g ((uGL q * sGL (x, 0))⁻¹ * δ * AutomorphicForm.sigmaGL K L F σ (uGL q * sGL (x, 0)))‖ₑ =
      sliceInd (K := K) (L := L) (v := v) g (twE σ ((δ : Matrix (Fin 2) (Fin 2) E) 0 0) q.1)
        (twE σ ((δ : Matrix (Fin 2) (Fin 2) E) 1 1) q.2)
        (twE σ ((δ : Matrix (Fin 2) (Fin 2) E) 0 0) q.1 * AutomorphicForm.sigmaTensor K L F σ x -
          twE σ ((δ : Matrix (Fin 2) (Fin 2) E) 1 1) q.2 * x) := by
  rw [enorm_φS, sliceInd]
  set X : G := (uGL q * sGL (x, 0))⁻¹ * δ * AutomorphicForm.sigmaGL K L F σ (uGL q * sGL (x, 0)) with hX
  have hcoe := coe_twConj_uGL_sGL (K := K) (L := L) (v := v) σ hδ₀₁ hδ₁₀ hq x
  have hiff : X ∈ Sset (K := K) (L := L) (v := v) g ↔
      (twE σ ((δ : Matrix (Fin 2) (Fin 2) E) 0 0) q.1 * AutomorphicForm.sigmaTensor K L F σ x -
          twE σ ((δ : Matrix (Fin 2) (Fin 2) E) 1 1) q.2 * x) ∈
        {ξ' : E | ∃ h ∈ Sset (K := K) (L := L) (v := v) g, (h : Matrix (Fin 2) (Fin 2) E) =
          !![twE σ ((δ : Matrix (Fin 2) (Fin 2) E) 0 0) q.1, ξ'; 0, twE σ ((δ : Matrix (Fin 2) (Fin 2) E) 1 1) q.2]} := by
    constructor
    · intro h; exact ⟨X, h, hcoe⟩
    · rintro ⟨h, hh, hh'⟩
      have : h = X := Units.ext (by rw [hh', ← hcoe])
      rwa [this] at hh
  by_cases h : X ∈ Sset (K := K) (L := L) (v := v) g
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hiff.1 h)]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (hiff.2 h'))]

theorem lintegral_indicator_comp_sub [IsGalois K L] (hgen : ∀ τ₀ : L ≃ₐ[K] L, τ₀ ∈ Subgroup.zpowers σ)
    {A₀ B₀ : E} (hA : IsUnit A₀) (hB : IsUnit B₀) (hN : Algebra.norm F A₀ ≠ Algebra.norm F B₀)
    {S : Set E} (hS : MeasurableSet S) :
    ∫⁻ x, S.indicator (fun _ => (1 : ℝ≥0∞)) (A₀ * AutomorphicForm.sigmaTensor K L F σ x - B₀ * x) ∂ν =
      (ENNReal.ofReal ‖Algebra.norm F A₀ - Algebra.norm F B₀‖)⁻¹ * ν S := by
  obtain ⟨T, hT, hdet⟩ :=
    AutomorphicForm.exists_linearMap_mul_sigmaTensor_sub_mul_and_det_eq_neg_one_pow_mul_norm_sub_norm
      K L σ hgen v hA.unit hB.unit
  rw [IsUnit.unit_spec, IsUnit.unit_spec] at hT hdet
  have hnorm : ‖LinearMap.det T‖ = ‖Algebra.norm F A₀ - Algebra.norm F B₀‖ := by
    rw [hdet, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, ← norm_neg, neg_sub]
  have hdet0 : LinearMap.det T ≠ 0 := by
    rw [← norm_ne_zero_iff, hnorm, norm_ne_zero_iff]; exact sub_ne_zero.2 hN
  have hTm : Measurable (T : E → E) := (IsModuleTopology.continuous_of_linearMap T).measurable
  have h1 : (fun x => S.indicator (fun _ => (1 : ℝ≥0∞)) (A₀ * AutomorphicForm.sigmaTensor K L F σ x - B₀ * x)) =
      fun x => S.indicator (fun _ => (1 : ℝ≥0∞)) (T x) := by
    funext x; rw [hT]
  rw [h1, ← lintegral_map (measurable_const.indicator hS) hTm,
    NumberField.AdicCompletion.map_linearMap_eq_norm_det_inv_smul_of_isAddHaarMeasure K v E ν T hdet0,
    lintegral_smul_measure, lintegral_indicator hS, setLIntegral_one, smul_eq_mul, hnorm,
    ENNReal.ofReal_inv_of_pos (norm_pos_iff.2 (sub_ne_zero.2 hN))]

def shiftT (η : E) (p : Q) : Q := (p.1 * Ring.inverse η, p.2 * η)

theorem measurable_shiftT (η : E) : Measurable (shiftT (K := K) (L := L) (v := v) η) :=
  (measurable_fst.mul_const _).prodMk (measurable_snd.mul_const _)

theorem shiftT_apply (η : E) (p : Q) : shiftT (K := K) (L := L) (v := v) η p = (p.1 * Ring.inverse η, p.2 * η) := rfl

def indT (δ g : G) (q : Q) (x' : E) : ℝ≥0∞ :=
  sliceInd (K := K) (L := L) (v := v) g (twE σ ((δ : Matrix (Fin 2) (Fin 2) E) 0 0) q.1)
    (twE σ ((δ : Matrix (Fin 2) (Fin 2) E) 1 1) q.2)
    (twE σ ((δ : Matrix (Fin 2) (Fin 2) E) 0 0) q.1 * AutomorphicForm.sigmaTensor K L F σ x' -
      twE σ ((δ : Matrix (Fin 2) (Fin 2) E) 1 1) q.2 * x')

set_option maxHeartbeats 20000000 in
theorem measurable_indT (δ g : G) : Measurable fun z : Q × E => indT (K := K) (L := L) (v := v) σ δ g z.1 z.2 := by
  have hA : Measurable fun z : Q × E => twE (K := K) (L := L) (v := v) σ ((δ : Matrix (Fin 2) (Fin 2) E) 0 0) z.1.1 :=
    (measurable_twE σ _).comp (measurable_fst.comp measurable_fst)
  have hB : Measurable fun z : Q × E => twE (K := K) (L := L) (v := v) σ ((δ : Matrix (Fin 2) (Fin 2) E) 1 1) z.1.2 :=
    (measurable_twE σ _).comp (measurable_snd.comp measurable_fst)
  have hσ : Measurable fun z : Q × E => AutomorphicForm.sigmaTensor K L F σ z.2 :=
    (continuous_sigmaTensor (v := v) σ).measurable.comp measurable_snd
  have hξ : Measurable fun z : Q × E =>
      twE (K := K) (L := L) (v := v) σ ((δ : Matrix (Fin 2) (Fin 2) E) 0 0) z.1.1 * AutomorphicForm.sigmaTensor K L F σ z.2 -
        twE σ ((δ : Matrix (Fin 2) (Fin 2) E) 1 1) z.1.2 * z.2 :=
    (hA.mul hσ).sub (hB.mul measurable_snd)
  exact (measurable_sliceInd (K := K) (L := L) (v := v) g).comp ((hA.prodMk hB).prodMk hξ)

attribute [irreducible] indT

set_option maxHeartbeats 40000000 in
theorem measurable_indT_left (δ g : G) (q : Q) :
    Measurable fun x : E => indT (K := K) (L := L) (v := v) σ δ g q x :=
  (measurable_indT σ δ g).comp (measurable_const.prodMk measurable_id)

set_option maxHeartbeats 40000000 in
theorem measurable_indT_shift (δ g : G) (η c : E) :
    Measurable fun z : E × Q => indT (K := K) (L := L) (v := v) σ δ g (shiftT (K := K) (L := L) (v := v) η z.2) (η ^ 2 * z.1 + c) := by
  have hc : Continuous fun z : E × Q => ((shiftT (K := K) (L := L) (v := v) η z.2, η ^ 2 * z.1 + c) : Q × E) := by
    refine Continuous.prodMk ?_ ((continuous_const.mul continuous_fst).add continuous_const)
    exact ((continuous_fst.comp continuous_snd).mul continuous_const).prodMk
      ((continuous_snd.comp continuous_snd).mul continuous_const)
  exact (measurable_indT σ δ g).comp hc.measurable

attribute [irreducible] shiftT

set_option maxHeartbeats 40000000 in

theorem slice (g : G) [IsGalois K L] (hgen : ∀ τ₀ : L ≃ₐ[K] L, τ₀ ∈ Subgroup.zpowers σ)
    (hab : a ≠ b) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b])
    (hδ₀₁ : (δ : Matrix (Fin 2) (Fin 2) E) 0 1 = 0) (hδ₁₀ : (δ : Matrix (Fin 2) (Fin 2) E) 1 0 = 0)
    (hN : Algebra.norm F ((δ : Matrix (Fin 2) (Fin 2) E) 0 0) ≠ Algebra.norm F ((δ : Matrix (Fin 2) (Fin 2) E) 1 1))
    {β : G → ℝ} (hβm : Measurable β) (hβ0 : ∀ x, 0 ≤ β x)
    (hβ : ∀ u : G, (u : Matrix (Fin 2) (Fin 2) E) 0 1 = 0 → (u : Matrix (Fin 2) (Fin 2) E) 1 0 = 0 →
      ∫ t : A, β (AutomorphicForm.toTensorGL K L F (t : GF) * u) ∂τ = 1)
    {y η c : E} (hη : IsUnit η) {k : G} (hk : k ∈ 𝒦)
    (habs : ∀ (x : E) (p : Q), p ∈ goodT →
      uGL p * sGL (x, y) = uGL (p.1 * Ring.inverse η, p.2 * η) * sGL (η ^ 2 * x + c, 0) * k) :
    ∫⁻ x, ∫⁻ p, D p * (‖Φf σ δ (φS (K := K) (L := L) (v := v) g) (x, y) p‖ₑ * ENNReal.ofReal (β (uGL p))) ∂ν² ∂ν =
      (wt (K := K) (L := L) (v := v) (η ^ 2))⁻¹ *
        ((ENNReal.ofReal ‖Algebra.norm F ((δ : Matrix (Fin 2) (Fin 2) E) 0 0) -
            Algebra.norm F ((δ : Matrix (Fin 2) (Fin 2) E) 1 1)‖)⁻¹ * Q0 ν σ g δ β) := by

  have hδdet : IsUnit ((δ : Matrix (Fin 2) (Fin 2) E).det) := Matrix.isUnits_det_units δ
  rw [Matrix.det_fin_two, hδ₀₁, zero_mul, sub_zero, IsUnit.mul_iff] at hδdet
  obtain ⟨hd0u, hd1u⟩ := hδdet
  set d0 : E := (δ : Matrix (Fin 2) (Fin 2) E) 0 0 with hd0
  set d1 : E := (δ : Matrix (Fin 2) (Fin 2) E) 1 1 with hd1
  set dd : ℝ≥0∞ := (ENNReal.ofReal ‖Algebra.norm F d0 - Algebra.norm F d1‖)⁻¹ with hdd
  have hηi : IsUnit (Ring.inverse η) := by
    have : Ring.inverse η = ((hη.unit⁻¹ : Eˣ) : E) := by rw [← Ring.inverse_unit hη.unit, IsUnit.unit_spec]
    rw [this]; exact Units.isUnit _
  have hη2 : IsUnit (η ^ 2) := hη.pow 2

  have hm_good : ∀ {p : Q}, p ∈ goodT → shiftT (K := K) (L := L) (v := v) η p ∈ goodT := by
    intro p hp
    rw [shiftT_apply]
    rw [mem_goodT_iff] at hp ⊢
    exact ⟨hp.1.mul hηi, hp.2.mul hη⟩

  have hpt : ∀ (x : E) (p : Q),
      D p * (‖Φf σ δ (φS (K := K) (L := L) (v := v) g) (x, y) p‖ₑ * ENNReal.ofReal (β (uGL p))) =
        D p * (indT (K := K) (L := L) (v := v) σ δ g (shiftT (K := K) (L := L) (v := v) η p) (η ^ 2 * x + c) * ENNReal.ofReal (β (uGL p))) := by
    intro x p
    by_cases hp : p ∈ goodT
    · congr 2
      simp only [Φf]
      rw [habs x p hp, enorm_φS_twConj_mul σ (δ := δ) g _ hk, indT, ← shiftT_apply]
      exact enorm_φS_twConj_uGL_sGL σ g hδ₀₁ hδ₁₀ (hm_good hp) _
    · rw [D_of_not hp, zero_mul, zero_mul]
  simp_rw [hpt]

  have hFm : Measurable fun z : E × Q => D z.2 *
      (indT (K := K) (L := L) (v := v) σ δ g (shiftT (K := K) (L := L) (v := v) η z.2) (η ^ 2 * z.1 + c) * ENNReal.ofReal (β (uGL z.2))) :=
    (measurable_D.comp measurable_snd).mul
      ((measurable_indT_shift σ δ g η c).mul (ENNReal.measurable_ofReal.comp (hβm.comp (measurable_uGL.comp measurable_snd))))

  rw [lintegral_lintegral_swap hFm.aemeasurable]

  have hinner : ∀ p : Q, p ∈ goodT →
      ∫⁻ x, indT (K := K) (L := L) (v := v) σ δ g (shiftT (K := K) (L := L) (v := v) η p) (η ^ 2 * x + c) ∂ν = (wt (K := K) (L := L) (v := v) (η ^ 2))⁻¹ * (dd * V ν g (twE σ d0 (shiftT (K := K) (L := L) (v := v) η p).1) (twE σ d1 (shiftT (K := K) (L := L) (v := v) η p).2)) := by
    intro p hp
    have hq := hm_good hp
    obtain ⟨hq1, hq2⟩ := (mem_goodT_iff _).1 hq
    have hmeas : Measurable (indT (K := K) (L := L) (v := v) σ δ g (shiftT (K := K) (L := L) (v := v) η p)) :=
      measurable_indT_left σ δ g _
    have h1 : ∫⁻ x, indT (K := K) (L := L) (v := v) σ δ g (shiftT (K := K) (L := L) (v := v) η p) (η ^ 2 * x + c) ∂ν = (wt (K := K) (L := L) (v := v) (η ^ 2))⁻¹ * ∫⁻ x, indT (K := K) (L := L) (v := v) σ δ g (shiftT (K := K) (L := L) (v := v) η p) (x + c) ∂ν :=
      lintegral_comp_mul_left ν (fun x => indT (K := K) (L := L) (v := v) σ δ g (shiftT (K := K) (L := L) (v := v) η p) (x + c)) (hmeas.comp (measurable_id.add_const c)) hη2
    rw [h1, lintegral_add_right_eq_self (μ := ν) (indT (K := K) (L := L) (v := v) σ δ g (shiftT (K := K) (L := L) (v := v) η p)) c]
    congr 1
    have hA : IsUnit (twE (K := K) (L := L) (v := v) σ d0 (shiftT (K := K) (L := L) (v := v) η p).1) := isUnit_twE σ hd0u hq1
    have hB : IsUnit (twE (K := K) (L := L) (v := v) σ d1 (shiftT (K := K) (L := L) (v := v) η p).2) := isUnit_twE σ hd1u hq2
    have hNe : Algebra.norm F (twE (K := K) (L := L) (v := v) σ d0 (shiftT (K := K) (L := L) (v := v) η p).1) ≠ Algebra.norm F (twE (K := K) (L := L) (v := v) σ d1 (shiftT (K := K) (L := L) (v := v) η p).2) := by
      rw [algebraNorm_twE σ hq1, algebraNorm_twE σ hq2]; exact hN
    simp only [indT, sliceInd]
    rw [lintegral_indicator_comp_sub ν σ hgen hA hB hNe (measurableSet_sliceSet g _ _), algebraNorm_twE σ hq1,
      algebraNorm_twE σ hq2]
    rfl
  have hstep3 : ∀ p : Q, ∫⁻ x, D p * (indT (K := K) (L := L) (v := v) σ δ g (shiftT (K := K) (L := L) (v := v) η p) (η ^ 2 * x + c) * ENNReal.ofReal (β (uGL p))) ∂ν =
      (wt (K := K) (L := L) (v := v) (η ^ 2))⁻¹ * (dd * (D p * (V ν g (twE σ d0 (shiftT (K := K) (L := L) (v := v) η p).1) (twE σ d1 (shiftT (K := K) (L := L) (v := v) η p).2) *
        ENNReal.ofReal (β (uGL p))))) := by
    intro p
    by_cases hp : p ∈ goodT
    · have hmeas : Measurable fun x => indT (K := K) (L := L) (v := v) σ δ g (shiftT (K := K) (L := L) (v := v) η p) (η ^ 2 * x + c) :=
        (measurable_indT_left σ δ g _).comp ((continuous_const.mul continuous_id).add continuous_const).measurable
      rw [lintegral_const_mul'' _ ?_, lintegral_mul_const _ hmeas, hinner p hp]
      · ring
      · exact (hmeas.mul_const _).aemeasurable
    · simp only [D_of_not hp, zero_mul, lintegral_zero, mul_zero]
  simp_rw [hstep3]
  rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 (wt_ne_zero hη2)),
    lintegral_const_mul' _ _ (by rw [hdd]; exact ENNReal.inv_ne_top.2 (by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le, norm_pos_iff]; exact sub_ne_zero.2 hN))]
  congr 2

  set Vm : Q → ℝ≥0∞ := fun q => V ν g (twE σ d0 q.1) (twE σ d1 q.2) with hVm
  have hVmM : Measurable Vm := (measurable_V ν g).comp
    (by
      have h1 : Measurable fun q : Q => twE (K := K) (L := L) (v := v) σ d0 q.1 := (measurable_twE σ d0).comp measurable_fst
      have h2 : Measurable fun q : Q => twE (K := K) (L := L) (v := v) σ d1 q.2 := (measurable_twE σ d1).comp measurable_snd
      exact h1.prodMk h2)
  set w₁ : Q → ℝ := fun q => β (uGL (q.1 * η, q.2 * Ring.inverse η)) with hw₁
  have hw₁m : Measurable w₁ := hβm.comp (measurable_uGL.comp ((measurable_fst.mul_const _).prodMk (measurable_snd.mul_const _)))
  have hsub : ∫⁻ p, D p * (Vm (shiftT (K := K) (L := L) (v := v) η p) * ENNReal.ofReal (β (uGL p))) ∂ν² = ∫⁻ p, D p * (Vm p * ENNReal.ofReal (w₁ p)) ∂ν² := by

    have hH : Measurable fun p : Q => D p * (Vm p * ENNReal.ofReal (w₁ p)) :=
      measurable_D.mul (hVmM.mul (ENNReal.measurable_ofReal.comp hw₁m))
    have h := lintegral_comp_mul_pair ν hηi hη hH
    have hone : (wt (K := K) (L := L) (v := v) (Ring.inverse η))⁻¹ * (wt (K := K) (L := L) (v := v) η)⁻¹ = 1 := by
      rw [← ENNReal.mul_inv (Or.inl (wt_ne_zero hηi)) (Or.inl (wt_ne_top _)), ← wt_mul, Ring.inverse_mul_cancel η hη, wt,
        map_one, norm_one, ENNReal.ofReal_one, inv_one]
    rw [hone, one_mul] at h
    rw [← h]
    refine lintegral_congr fun p => ?_
    have hmp : shiftT (K := K) (L := L) (v := v) η p = (Ring.inverse η * p.1, η * p.2) := by rw [shiftT_apply]; simp only [mul_comm]
    have hback : ((Ring.inverse η * p.1) * η, (η * p.2) * Ring.inverse η) = p := by
      ext
      · show Ring.inverse η * p.1 * η = p.1
        rw [mul_comm, ← mul_assoc, Ring.mul_inverse_cancel η hη, one_mul]
      · show η * p.2 * Ring.inverse η = p.2
        rw [mul_comm, ← mul_assoc, Ring.inverse_mul_cancel η hη, one_mul]
    have hD : D (K := K) (L := L) (v := v) (Ring.inverse η * p.1, η * p.2) = D p := by
      by_cases hp : p ∈ goodT
      · have hq : (Ring.inverse η * p.1, η * p.2) ∈ goodT := by rw [← hmp]; exact hm_good hp
        rw [D_of_mem hq, D_of_mem hp]
        congr 2
        show ‖Algebra.norm F (Ring.inverse η * p.1 * (η * p.2))‖ = ‖Algebra.norm F (p.1 * p.2)‖
        have : Ring.inverse η * p.1 * (η * p.2) = (Ring.inverse η * η) * (p.1 * p.2) := by ring
        rw [this, Ring.inverse_mul_cancel η hη, one_mul]
      · have hq : (Ring.inverse η * p.1, η * p.2) ∉ goodT := by
          intro hq; apply hp
          rw [mem_goodT_iff] at hq ⊢
          have e1 : η * (Ring.inverse η * p.1) = p.1 := by rw [← mul_assoc, Ring.mul_inverse_cancel η hη, one_mul]
          have e2 : Ring.inverse η * (η * p.2) = p.2 := by rw [← mul_assoc, Ring.inverse_mul_cancel η hη, one_mul]
          exact ⟨e1 ▸ hη.mul hq.1, e2 ▸ hηi.mul hq.2⟩
        rw [D_of_not hq, D_of_not hp]
    rw [hmp, hD]
    simp only [hw₁, hback]
  rw [show (∫⁻ p, D p * (V ν g (twE σ d0 (shiftT (K := K) (L := L) (v := v) η p).1) (twE σ d1 (shiftT (K := K) (L := L) (v := v) η p).2) * ENNReal.ofReal (β (uGL p))) ∂ν²) =
    ∫⁻ p, D p * (Vm (shiftT (K := K) (L := L) (v := v) η p) * ENNReal.ofReal (β (uGL p))) ∂ν² from rfl, hsub]

  show ∫⁻ p, D p * (Vm p * ENNReal.ofReal (w₁ p)) ∂ν² = ∫⁻ p, D p * (Vm p * ENNReal.ofReal (β (uGL p))) ∂ν²
  set h : Q → ℂ := fun p => if p ∈ goodT then ((Vm p).toReal : ℂ) else 0 with hh
  have hhm : Measurable h :=
    Measurable.ite measurableSet_goodT (Complex.measurable_ofReal.comp hVmM.ennreal_toReal) measurable_const
  have henorm : ∀ p, D (K := K) (L := L) (v := v) p * ‖h p‖ₑ = D p * Vm p := by
    intro p; by_cases hp : p ∈ goodT
    · simp only [hh, if_pos hp]
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal (V_lt_top ν g _ _).ne]
    · rw [D_of_not hp, zero_mul, zero_mul]
  have hhinv : ∀ (t : A) (p : Q), h (act (K := K) (L := L) (t : GF) p) = h p := by
    intro t p
    by_cases hp : p ∈ goodT
    · have hp' := (act_mem_goodT_iff hab hγ t p).2 hp
      obtain ⟨hp1, hp2⟩ := (mem_goodT_iff p).1 hp
      have e1 := (twE_emb_mul σ hab hγ t d0 hp1).1
      have e2 := (twE_emb_mul σ hab hγ t d1 hp2).2
      simp only [hh, if_pos hp, if_pos hp', hVm]
      show (((V ν g (twE σ d0 (c1 (K := K) (L := L) (t : GF) * p.1)) (twE σ d1 (c2 (K := K) (L := L) (t : GF) * p.2))).toReal : ℝ) : ℂ) =
        (((V ν g (twE σ d0 p.1) (twE σ d1 p.2)).toReal : ℝ) : ℂ)
      rw [e1, e2]
    · have hp' : act (K := K) (L := L) (t : GF) p ∉ goodT := fun h' => hp ((act_mem_goodT_iff hab hγ t p).1 h')
      simp only [hh, if_neg hp, if_neg hp']
  have hne : ∀ p, h p ≠ 0 → p ∈ goodT := by
    intro p hp0; by_contra hp; exact hp0 (by simp only [hh, if_neg hp])
  have hs₂ : ∀ p, h p ≠ 0 → ∫⁻ t : A, ENNReal.ofReal (β (uGL (act (K := K) (L := L) (t : GF) p))) ∂τ = 1 :=
    fun p hp0 => section_β_of_mem τ hab hγ hβ0 hβ (hne p hp0)
  have hs₁ : ∀ p, h p ≠ 0 → ∫⁻ t : A, ENNReal.ofReal (w₁ (act (K := K) (L := L) (t : GF) p)) ∂τ = 1 := by
    intro p hp0
    have hp := hne p hp0
    have hp' : (p.1 * η, p.2 * Ring.inverse η) ∈ goodT := by
      rw [mem_goodT_iff] at hp ⊢; exact ⟨hp.1.mul hη, hp.2.mul hηi⟩
    have : ∀ t : A, w₁ (act (K := K) (L := L) (t : GF) p) =
        β (uGL (act (K := K) (L := L) (t : GF) (p.1 * η, p.2 * Ring.inverse η))) := by
      intro t; simp only [hw₁, act, mul_assoc]
    simp_rw [this]
    exact section_β_of_mem τ hab hγ hβ0 hβ hp'
  have hw₂m : Measurable (fun p : Q => β (uGL p)) := hβm.comp measurable_uGL
  have key := (indep ν τ hab hγ hhm hhinv hw₁m hw₂m (fun p => hβ0 _) (fun p => hβ0 _) hs₁ hs₂).1
  have hH₁ : Measurable (fun p : Q => ‖h p‖ₑ * ENNReal.ofReal (w₁ p)) := hhm.enorm.mul (ENNReal.measurable_ofReal.comp hw₁m)
  have hH₂ : Measurable (fun p : Q => ‖h p‖ₑ * ENNReal.ofReal (β (uGL p))) := hhm.enorm.mul (ENNReal.measurable_ofReal.comp hw₂m)
  rw [lintegral_ρ ν hH₁, lintegral_ρ ν hH₂] at key
  simp_rw [← mul_assoc, henorm, mul_assoc] at key
  exact key

theorem total (g : G) [IsGalois K L] (hgen : ∀ τ₀ : L ≃ₐ[K] L, τ₀ ∈ Subgroup.zpowers σ)
    (hab : a ≠ b) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b])
    (hδ₀₁ : (δ : Matrix (Fin 2) (Fin 2) E) 0 1 = 0) (hδ₁₀ : (δ : Matrix (Fin 2) (Fin 2) E) 1 0 = 0)
    (hN : Algebra.norm F ((δ : Matrix (Fin 2) (Fin 2) E) 0 0) ≠ Algebra.norm F ((δ : Matrix (Fin 2) (Fin 2) E) 1 1))
    {β : G → ℝ} (hβm : Measurable β) (hβ0 : ∀ x, 0 ≤ β x)
    (hβ : ∀ u : G, (u : Matrix (Fin 2) (Fin 2) E) 0 1 = 0 → (u : Matrix (Fin 2) (Fin 2) E) 1 0 = 0 →
      ∫ t : A, β (AutomorphicForm.toTensorGL K L F (t : GF) * u) ∂τ = 1)
    {Yn : E → ℝ≥0∞} (hYm : Measurable Yn)
    (hY : ∀ y : E, ∃ η c : E, IsUnit η ∧ Yn y = (wt (K := K) (L := L) (v := v) (η ^ 2))⁻¹ ∧
        ∃ k : G, k ∈ 𝒦 ∧ ∀ (x : E) (p : Q), p ∈ goodT →
          uGL p * sGL (x, y) = uGL (p.1 * Ring.inverse η, p.2 * η) * sGL (η ^ 2 * x + c, 0) * k) :
    ∫⁻ q, ∫⁻ p, D p * (‖Φf σ δ (φS (K := K) (L := L) (v := v) g) q p‖ₑ * ENNReal.ofReal (β (uGL p))) ∂ν² ∂ν² =
      (∫⁻ y, Yn y ∂ν) *
        ((ENNReal.ofReal ‖Algebra.norm F ((δ : Matrix (Fin 2) (Fin 2) E) 0 0) -
            Algebra.norm F ((δ : Matrix (Fin 2) (Fin 2) E) 1 1)‖)⁻¹ * Q0 ν σ g δ β) := by
  set Fq : Q → Q → ℝ≥0∞ := fun q p =>
    D p * (‖Φf σ δ (φS (K := K) (L := L) (v := v) g) q p‖ₑ * ENNReal.ofReal (β (uGL p))) with hFq
  have hF : Measurable fun z : Q × Q => Fq z.1 z.2 :=
    (measurable_D.comp measurable_snd).mul
      (((measurable_Φf_uncurry σ (measurable_φS g)).enorm).mul
        (ENNReal.measurable_ofReal.comp (hβm.comp (measurable_uGL.comp measurable_snd))))
  have hG : Measurable fun q : Q => ∫⁻ p, Fq q p ∂ν² := hF.lintegral_prod_right'
  show (∫⁻ q, ∫⁻ p, Fq q p ∂ν² ∂ν²) = _
  rw [lintegral_prod _ hG.aemeasurable]
  have hG2 : Measurable fun z : E × E => ∫⁻ p, Fq (z.1, z.2) p ∂ν² := by simpa using hG
  rw [lintegral_lintegral_swap hG2.aemeasurable]
  have hslice : ∀ y : E, ∫⁻ x, ∫⁻ p, Fq (x, y) p ∂ν² ∂ν =
      Yn y * ((ENNReal.ofReal ‖Algebra.norm F ((δ : Matrix (Fin 2) (Fin 2) E) 0 0) -
            Algebra.norm F ((δ : Matrix (Fin 2) (Fin 2) E) 1 1)‖)⁻¹ * Q0 ν σ g δ β) := by
    intro y
    obtain ⟨η, c, hη, hYn, k, hk, habs⟩ := hY y
    rw [hYn]
    exact slice ν σ τ g hgen hab hγ hδ₀₁ hδ₁₀ hN hβm hβ0 hβ hη hk habs
  rw [lintegral_congr hslice, lintegral_mul_const _ hYm]

set_option maxHeartbeats 40000000 in
theorem measurable_Q0_integrand (g δ : G) {β : G → ℝ} (hβm : Measurable β) :
    Measurable fun p : Q => D (K := K) (L := L) (v := v) p *
      (V ν g (twE σ ((δ : Matrix (Fin 2) (Fin 2) E) 0 0) p.1) (twE σ ((δ : Matrix (Fin 2) (Fin 2) E) 1 1) p.2) *
        ENNReal.ofReal (β (uGL p))) := by
  have h1 : Measurable fun p : Q => twE (K := K) (L := L) (v := v) σ ((δ : Matrix (Fin 2) (Fin 2) E) 0 0) p.1 :=
    (measurable_twE σ _).comp measurable_fst
  have h2 : Measurable fun p : Q => twE (K := K) (L := L) (v := v) σ ((δ : Matrix (Fin 2) (Fin 2) E) 1 1) p.2 :=
    (measurable_twE σ _).comp measurable_snd
  have h3 : Measurable fun p : Q => V ν g (twE σ ((δ : Matrix (Fin 2) (Fin 2) E) 0 0) p.1) (twE σ ((δ : Matrix (Fin 2) (Fin 2) E) 1 1) p.2) :=
    (measurable_V ν g).comp (h1.prodMk h2)
  exact measurable_D.mul (h3.mul (ENNReal.measurable_ofReal.comp (hβm.comp measurable_uGL)))

set_option maxHeartbeats 40000000 in

theorem Q0_le (g : G)
    (hδ₀₁ : (δ : Matrix (Fin 2) (Fin 2) E) 0 1 = 0) (hδ₁₀ : (δ : Matrix (Fin 2) (Fin 2) E) 1 0 = 0)
    (hN : Algebra.norm F ((δ : Matrix (Fin 2) (Fin 2) E) 0 0) ≠ Algebra.norm F ((δ : Matrix (Fin 2) (Fin 2) E) 1 1))
    (W : Set F) (hWc : IsClosed W)
    (m₀ : ℝ≥0∞) (hm₀ : m₀ ≠ 0) (hm₀' : m₀ ≠ ⊤)
    (hm₀U : ∀ α : E, IsUnit α → (ν.withDensity fun b => ENNReal.ofReal ‖Algebra.norm F b‖⁻¹)
      {b : E | ∃ u ∈ Uint (K := K) (L := L) (v := v), b = α * u} = m₀)
    (C_V : ℝ≥0∞)
    (hVOL : ∀ (c : Eˣ) (p' : E),
      (ν.withDensity fun b => ENNReal.ofReal ‖Algebra.norm F b‖⁻¹)
        {b : E | IsUnit b ∧ Algebra.norm F b ∈ W ∧
          ∃ u ∈ Uint (K := K) (L := L) (v := v), (c : E) * AutomorphicForm.sigmaTensor K L F σ b = b * p' * u} ≤ C_V)
    (C_H : ℝ≥0∞) (Apow : ℕ)
    (hHT : ∀ r : ℝ, ∫⁻ α in {α : E | ‖Algebra.norm F α‖ = r},
        (⨆ β' : E, ν {ξ : E | ∃ h ∈ AutomorphicForm.semiLocalIntegralSet K L v * {g} * AutomorphicForm.semiLocalIntegralSet K L v,
            (h : Matrix (Fin 2) (Fin 2) E) = !![α, ξ; 0, β']})
          ∂(ν.withDensity fun b => ENNReal.ofReal ‖Algebra.norm F b‖⁻¹) ≤
        C_H * ENNReal.ofReal
          ((‖Algebra.norm F ((Matrix.GeneralLinearGroup.det g : Eˣ) : E)‖ *
              (AutomorphicForm.semiLocalHaar K L v (Sset (K := K) (L := L) (v := v) g)).toReal) ^ ((1 : ℝ) / 2) *
            (1 + Real.log (AutomorphicForm.semiLocalHaar K L v (Sset (K := K) (L := L) (v := v) g)).toReal) ^ Apow))
    {β : G → ℝ} (hβm : Measurable β) (hβ0 : ∀ x, 0 ≤ β x) (hβ1 : ∀ x, β x ≤ 1)
    (hβW : ∀ p : Q, p ∈ goodT → β (uGL p) ≠ 0 → Algebra.norm F p.1 ∈ W ∧ Algebra.norm F p.2 ∈ W) :
    Q0 ν σ g δ β ≤ C_V * (m₀⁻¹ * (C_V * (C_H * ENNReal.ofReal
          ((‖Algebra.norm F ((Matrix.GeneralLinearGroup.det g : Eˣ) : E)‖ *
              (AutomorphicForm.semiLocalHaar K L v (Sset (K := K) (L := L) (v := v) g)).toReal) ^ ((1 : ℝ) / 2) *
            (1 + Real.log (AutomorphicForm.semiLocalHaar K L v (Sset (K := K) (L := L) (v := v) g)).toReal) ^ Apow)))) := by

  have hδdet : IsUnit ((δ : Matrix (Fin 2) (Fin 2) E).det) := Matrix.isUnits_det_units δ
  rw [Matrix.det_fin_two, hδ₀₁, zero_mul, sub_zero, IsUnit.mul_iff] at hδdet
  obtain ⟨hd0u, hd1u⟩ := hδdet
  set d0 : E := (δ : Matrix (Fin 2) (Fin 2) E) 0 0 with hd0
  set d1 : E := (δ : Matrix (Fin 2) (Fin 2) E) 1 1 with hd1
  set dg : E := ((Matrix.GeneralLinearGroup.det g : Eˣ) : E) with hdg
  set Dn : E → ℝ≥0∞ := fun b => ENNReal.ofReal ‖Algebra.norm F b‖⁻¹ with hDn
  have hDnm : Measurable Dn := ENNReal.measurable_ofReal.comp (continuous_algebraNorm.norm).measurable.inv
  set mW : Measure E := ν.withDensity Dn with hmW
  set X : ℝ≥0∞ := ENNReal.ofReal
          ((‖Algebra.norm F dg‖ *
              (AutomorphicForm.semiLocalHaar K L v (Sset (K := K) (L := L) (v := v) g)).toReal) ^ ((1 : ℝ) / 2) *
            (1 + Real.log (AutomorphicForm.semiLocalHaar K L v (Sset (K := K) (L := L) (v := v) g)).toReal) ^ Apow) with hX

  set Vd : E → ℝ≥0∞ := fun α => V ν g α (Ring.inverse α * dg) with hVd
  have hVdm : Measurable Vd :=
    (measurable_V ν g).comp (measurable_id.prodMk (measurable_ringInverse.mul_const dg))
  have hVd_top : ∀ α, Vd α ≠ ⊤ := fun α => (V_lt_top ν g _ _).ne
  have hVd_le : ∀ α, Vd α ≤ ⨆ β' : E, V ν g α β' := fun α => le_iSup (fun β' => V ν g α β') _

  have hA : ∀ {α β' : E}, IsUnit α → V ν g α β' ≠ 0 →
      ∃ u ∈ Uint (K := K) (L := L) (v := v), β' = Ring.inverse α * dg * u ∧ V ν g α β' = Vd α := by
    intro α β' hα hV
    obtain ⟨ξ, h', hh', hcoe⟩ := nonempty_of_measure_ne_zero hV
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := (mem_Sset_iff g h').1 hh'
    have hdet : α * β' = ((Matrix.GeneralLinearGroup.det k₁ : Eˣ) : E) * dg *
        ((Matrix.GeneralLinearGroup.det k₂ : Eˣ) : E) := by
      have : ((Matrix.GeneralLinearGroup.det (k₁ * g * k₂) : Eˣ) : E) = α * β' := by
        show ((k₁ * g * k₂ : G) : Matrix (Fin 2) (Fin 2) E).det = _
        rw [hcoe, Matrix.det_fin_two_of]; ring
      rw [map_mul, map_mul, Units.val_mul, Units.val_mul] at this
      exact this.symm
    set u : E := ((Matrix.GeneralLinearGroup.det k₁ : Eˣ) : E) * ((Matrix.GeneralLinearGroup.det k₂ : Eˣ) : E) with hu
    have huU : u ∈ Uint (K := K) (L := L) (v := v) := mul_mem_Uint (det_mem_Uint hk₁) (det_mem_Uint hk₂)
    have hβ' : β' = Ring.inverse α * dg * u := by
      calc β' = (Ring.inverse α * α) * β' := by rw [Ring.inverse_mul_cancel α hα, one_mul]
        _ = Ring.inverse α * (α * β') := by ring
        _ = Ring.inverse α * (((Matrix.GeneralLinearGroup.det k₁ : Eˣ) : E) * dg *
              ((Matrix.GeneralLinearGroup.det k₂ : Eˣ) : E)) := by rw [hdet]
        _ = Ring.inverse α * dg * u := by simp only [hu]; ring
    refine ⟨u, huU, hβ', ?_⟩
    rw [hβ']
    exact V_mul_Uint_right ν huU g α _

  have hVdU : ∀ {α u : E}, IsUnit α → u ∈ Uint (K := K) (L := L) (v := v) → Vd (α * u) = Vd α := by
    intro α u hα hu
    obtain ⟨u', hu', huu'⟩ := inv_mem_Uint hu
    have hinv : Ring.inverse (α * u) = Ring.inverse α * u' := by
      have h1 : (α * u) * (Ring.inverse α * u') = 1 := by
        calc (α * u) * (Ring.inverse α * u') = (α * Ring.inverse α) * (u * u') := by ring
          _ = 1 := by rw [Ring.mul_inverse_cancel α hα, huu', one_mul]
      calc Ring.inverse (α * u) = Ring.inverse (α * u) * ((α * u) * (Ring.inverse α * u')) := by rw [h1, mul_one]
        _ = Ring.inverse α * u' := by
          rw [← mul_assoc, Ring.inverse_mul_cancel _ (hα.mul (isUnit_of_mem_Uint hu)), one_mul]
    simp only [hVd]
    rw [V_mul_Uint ν hu g, hinv, show Ring.inverse α * u' * dg = Ring.inverse α * dg * u' by ring,
      V_mul_Uint_right ν hu' g]

  set Wu : Set E := {p1 : E | IsUnit p1 ∧ Algebra.norm F p1 ∈ W} with hWu
  have hWum : MeasurableSet Wu :=
    (isOpen_units (K := K) (L := L) (v := v)).measurableSet.inter (hWc.preimage continuous_algebraNorm).measurableSet
  set G1 : E → ℝ≥0∞ := fun p1 => Wu.indicator (fun _ => 1) p1 * Dn p1 * Vd (twE σ d0 p1) with hG1
  have hG1m : Measurable G1 :=
    ((measurable_const.indicator hWum).mul hDnm).mul (hVdm.comp (measurable_twE σ d0))
  have hG1top : ∀ p1, G1 p1 ≠ ⊤ := by
    intro p1
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ?_ ENNReal.ofReal_ne_top) (hVd_top _)
    by_cases h : p1 ∈ Wu <;> simp [h]
  set T : E → Set E := fun p1 => {b : E | IsUnit b ∧ Algebra.norm F b ∈ W ∧
      ∃ u ∈ Uint (K := K) (L := L) (v := v), (hd1u.unit : E) * AutomorphicForm.sigmaTensor K L F σ b =
        b * (Ring.inverse (twE σ d0 p1) * dg) * u} with hT
  set G2 : E → E → ℝ≥0∞ := fun p1 p2 => (T p1).indicator Dn p2 with hG2
  have hpt : ∀ p : Q, D (K := K) (L := L) (v := v) p *
      (V ν g (twE σ d0 p.1) (twE σ d1 p.2) * ENNReal.ofReal (β (uGL p))) ≤ G1 p.1 * G2 p.1 p.2 := by
    intro p
    by_cases hp : p ∈ goodT
    swap
    · rw [D_of_not hp, zero_mul]; exact zero_le
    obtain ⟨hp1, hp2⟩ := (mem_goodT_iff p).1 hp
    by_cases hb : β (uGL p) = 0
    · rw [hb, ENNReal.ofReal_zero, mul_zero, mul_zero]; exact zero_le
    obtain ⟨hW1, hW2⟩ := hβW p hp hb
    by_cases hV : V ν g (twE σ d0 p.1) (twE σ d1 p.2) = 0
    · rw [hV, zero_mul, mul_zero]; exact zero_le
    have hAu : IsUnit (twE (K := K) (L := L) (v := v) σ d0 p.1) := isUnit_twE σ hd0u hp1
    obtain ⟨u, hu, hB, hVeq⟩ := hA hAu hV
    have hTm : p.2 ∈ T p.1 := by
      refine ⟨hp2, hW2, u, hu, ?_⟩
      rw [IsUnit.unit_spec, ← mul_twE σ hp2, hB]; ring
    have hD : D (K := K) (L := L) (v := v) p = Dn p.1 * Dn p.2 := by
      rw [D_of_mem hp]
      simp only [hDn]
      rw [map_mul, norm_mul, mul_inv, ENNReal.ofReal_mul (inv_nonneg.2 (norm_nonneg _))]
    have hβle : ENNReal.ofReal (β (uGL p)) ≤ 1 := ENNReal.ofReal_le_one.2 (hβ1 _)
    have hG1v : G1 p.1 = Dn p.1 * Vd (twE σ d0 p.1) := by
      simp only [hG1]; rw [Set.indicator_of_mem (show p.1 ∈ Wu from ⟨hp1, hW1⟩), one_mul]
    have hG2v : G2 p.1 p.2 = Dn p.2 := by simp only [hG2]; rw [Set.indicator_of_mem hTm]
    rw [hD, hVeq, hG1v, hG2v]
    calc Dn p.1 * Dn p.2 * (Vd (twE σ d0 p.1) * ENNReal.ofReal (β (uGL p)))
        ≤ Dn p.1 * Dn p.2 * (Vd (twE σ d0 p.1) * 1) := by gcongr
      _ = Dn p.1 * Vd (twE σ d0 p.1) * Dn p.2 := by ring

  have hinner : ∀ p1 : E, ∫⁻ p2, G2 p1 p2 ∂ν ≤ C_V := by
    intro p1
    calc ∫⁻ p2, G2 p1 p2 ∂ν ≤ ∫⁻ p2 in T p1, Dn p2 ∂ν := lintegral_indicator_le _ _
      _ = mW (T p1) := (withDensity_apply' _ _).symm
      _ ≤ C_V := hVOL hd1u.unit (Ring.inverse (twE σ d0 p1) * dg)
  have hQ0m : Measurable fun p : Q => D (K := K) (L := L) (v := v) p *
      (V ν g (twE σ d0 p.1) (twE σ d1 p.2) * ENNReal.ofReal (β (uGL p))) :=
    measurable_Q0_integrand ν σ g δ hβm
  have hstep1 : Q0 ν σ g δ β ≤ C_V * ∫⁻ p1, G1 p1 ∂ν := by
    unfold Q0
    rw [lintegral_prod _ hQ0m.aemeasurable]
    calc ∫⁻ p1, ∫⁻ p2, D (K := K) (L := L) (v := v) (p1, p2) *
          (V ν g (twE σ d0 (p1, p2).1) (twE σ d1 (p1, p2).2) * ENNReal.ofReal (β (uGL (p1, p2)))) ∂ν ∂ν
        ≤ ∫⁻ p1, ∫⁻ p2, G1 p1 * G2 p1 p2 ∂ν ∂ν :=
          lintegral_mono fun p1 => lintegral_mono fun p2 => hpt (p1, p2)
      _ = ∫⁻ p1, G1 p1 * ∫⁻ p2, G2 p1 p2 ∂ν ∂ν :=
          lintegral_congr fun p1 => lintegral_const_mul' _ _ (hG1top p1)
      _ ≤ ∫⁻ p1, G1 p1 * C_V ∂ν := lintegral_mono fun p1 => by gcongr; exact hinner p1
      _ = (∫⁻ p1, G1 p1 ∂ν) * C_V := lintegral_mul_const _ hG1m
      _ = C_V * ∫⁻ p1, G1 p1 ∂ν := mul_comm _ _

  have hS_meas : ∀ α : E, MeasurableSet ((fun b => Ring.inverse α * b) ⁻¹' Uint (K := K) (L := L) (v := v)) := fun α =>
    isCompact_Uint.isClosed.measurableSet.preimage (measurable_const_mul _)
  have hS_eq : ∀ {α : E}, IsUnit α → {b : E | ∃ u ∈ Uint (K := K) (L := L) (v := v), b = α * u} =
      (fun b => Ring.inverse α * b) ⁻¹' Uint (K := K) (L := L) (v := v) := by
    intro α hα
    ext b
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    constructor
    · rintro ⟨u, hu, rfl⟩
      rwa [← mul_assoc, Ring.inverse_mul_cancel α hα, one_mul]
    · intro hb
      exact ⟨Ring.inverse α * b, hb, by rw [← mul_assoc, Ring.mul_inverse_cancel α hα, one_mul]⟩
  have havg : ∀ {α : E}, IsUnit α →
      Vd α = m₀⁻¹ * ∫⁻ b, ((fun b => Ring.inverse α * b) ⁻¹' Uint (K := K) (L := L) (v := v)).indicator Vd b ∂mW := by
    intro α hα
    have h1 : ∫⁻ b, ((fun b => Ring.inverse α * b) ⁻¹' Uint (K := K) (L := L) (v := v)).indicator Vd b ∂mW = Vd α * m₀ := by
      rw [lintegral_indicator (hS_meas α)]
      have h2 : ∀ b ∈ (fun b => Ring.inverse α * b) ⁻¹' Uint (K := K) (L := L) (v := v), Vd b = Vd α := by
        intro b hb
        rw [← hS_eq hα] at hb
        obtain ⟨u, hu, rfl⟩ := hb
        exact hVdU hα hu
      rw [setLIntegral_congr_fun (hS_meas α) h2, setLIntegral_const, ← hS_eq hα, hm₀U α hα]
    rw [h1, mul_comm (Vd α), ← mul_assoc, ENNReal.inv_mul_cancel hm₀ hm₀', one_mul]

  set J : E × E → ℝ≥0∞ := fun z => Wu.indicator (fun _ => 1) z.1 *
      ((fun b => Ring.inverse (twE σ d0 z.1) * b) ⁻¹' Uint (K := K) (L := L) (v := v)).indicator Vd z.2 with hJ
  have hJm : Measurable J := by
    have hP : MeasurableSet {z : E × E | Ring.inverse (twE (K := K) (L := L) (v := v) σ d0 z.1) * z.2 ∈ Uint (K := K) (L := L) (v := v)} :=
      isCompact_Uint.isClosed.measurableSet.preimage
        (((measurable_ringInverse.comp (measurable_twE σ d0)).comp measurable_fst).mul measurable_snd)
    have h1 : (fun z : E × E => ((fun b => Ring.inverse (twE σ d0 z.1) * b) ⁻¹' Uint (K := K) (L := L) (v := v)).indicator Vd z.2) =
        fun z : E × E => {z : E × E | Ring.inverse (twE (K := K) (L := L) (v := v) σ d0 z.1) * z.2 ∈ Uint (K := K) (L := L) (v := v)}.indicator (fun z => Vd z.2) z := by
      funext z; simp only [Set.indicator, Set.mem_preimage, Set.mem_setOf_eq]
    refine ((measurable_const.indicator hWum).comp measurable_fst).mul ?_
    rw [h1]
    exact (hVdm.comp measurable_snd).indicator hP
  haveI : SFinite mW := by rw [hmW]; infer_instance
  have hstep2 : ∫⁻ p1, G1 p1 ∂ν ≤ m₀⁻¹ * (C_V * (C_H * X)) := by

    have hgm : Measurable (fun p1 : E => Wu.indicator (fun _ => (1 : ℝ≥0∞)) p1 * Vd (twE σ d0 p1)) :=
      (measurable_const.indicator hWum).mul (hVdm.comp (measurable_twE σ d0))
    have h1 : ∫⁻ p1, G1 p1 ∂ν = ∫⁻ p1, Wu.indicator (fun _ => 1) p1 * Vd (twE σ d0 p1) ∂mW := by
      rw [hmW, lintegral_withDensity_eq_lintegral_mul _ hDnm hgm]
      refine lintegral_congr fun p1 => ?_
      simp only [hG1, Pi.mul_apply]; ring
    have h2 : ∀ p1 : E, Wu.indicator (fun _ => (1 : ℝ≥0∞)) p1 * Vd (twE σ d0 p1) = m₀⁻¹ * ∫⁻ b, J (p1, b) ∂mW := by
      intro p1
      by_cases hp1 : p1 ∈ Wu
      · have hAu : IsUnit (twE (K := K) (L := L) (v := v) σ d0 p1) := isUnit_twE σ hd0u hp1.1
        simp only [hJ, Set.indicator_of_mem hp1, one_mul]
        exact havg hAu
      · simp only [hJ, Set.indicator_of_notMem hp1, zero_mul, lintegral_zero, mul_zero]
    rw [h1]
    simp_rw [h2]
    rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hm₀)]
    gcongr

    rw [lintegral_lintegral_swap (f := fun p1 b => J (p1, b))
      (by exact (hJm.comp (measurable_fst.prodMk measurable_snd)).aemeasurable)]

    set shell : Set E := {α : E | ‖Algebra.norm F α‖ = ‖Algebra.norm F d0‖} with hshell
    have hshellm : MeasurableSet shell := isClosed_eq (continuous_algebraNorm.norm) continuous_const |>.measurableSet
    have hin : ∀ α : E, ∫⁻ p1, J (p1, α) ∂mW ≤ C_V * shell.indicator Vd α := by
      intro α
      have hJ' : ∀ p1, J (p1, α) = {p1 : E | p1 ∈ Wu ∧ Ring.inverse (twE σ d0 p1) * α ∈ Uint (K := K) (L := L) (v := v)}.indicator (fun _ => Vd α) p1 := by
        intro p1
        simp only [hJ, Set.indicator, Set.mem_preimage, Set.mem_setOf_eq]
        by_cases h1 : p1 ∈ Wu <;> by_cases h2 : Ring.inverse (twE σ d0 p1) * α ∈ Uint (K := K) (L := L) (v := v) <;> simp [h1, h2]
      simp_rw [hJ']
      by_cases hne : ∃ p1 : E, p1 ∈ Wu ∧ Ring.inverse (twE σ d0 p1) * α ∈ Uint (K := K) (L := L) (v := v)
      ·
        obtain ⟨q, hq, hqU⟩ := hne
        have hAu : IsUnit (twE (K := K) (L := L) (v := v) σ d0 q) := isUnit_twE σ hd0u hq.1
        have hαeq : α = twE σ d0 q * (Ring.inverse (twE σ d0 q) * α) := by
          rw [← mul_assoc, Ring.mul_inverse_cancel _ hAu, one_mul]
        have hsh : α ∈ shell := by
          show ‖Algebra.norm F α‖ = ‖Algebra.norm F d0‖
          rw [hαeq, map_mul, norm_mul, norm_algebraNorm_eq_one_of_mem_Uint ν hqU, mul_one, algebraNorm_twE σ hq.1]
        rw [Set.indicator_of_mem hsh]
        calc ∫⁻ p1, {p1 : E | p1 ∈ Wu ∧ Ring.inverse (twE σ d0 p1) * α ∈ Uint (K := K) (L := L) (v := v)}.indicator (fun _ => Vd α) p1 ∂mW
            ≤ ∫⁻ p1 in {p1 : E | p1 ∈ Wu ∧ Ring.inverse (twE σ d0 p1) * α ∈ Uint (K := K) (L := L) (v := v)}, Vd α ∂mW :=
              lintegral_indicator_le _ _
          _ = Vd α * mW {p1 : E | p1 ∈ Wu ∧ Ring.inverse (twE σ d0 p1) * α ∈ Uint (K := K) (L := L) (v := v)} := setLIntegral_const _ _
          _ ≤ Vd α * C_V := by
              gcongr
              refine le_trans (measure_mono ?_) (hVOL hd0u.unit α)
              rintro p1 ⟨⟨hp1u, hp1W⟩, hU⟩
              obtain ⟨u', hu', huu'⟩ := inv_mem_Uint hU
              have hAu' : IsUnit (twE (K := K) (L := L) (v := v) σ d0 p1) := isUnit_twE σ hd0u hp1u
              refine ⟨hp1u, hp1W, u', hu', ?_⟩
              rw [IsUnit.unit_spec, ← mul_twE σ hp1u, mul_assoc]
              congr 1
              calc twE σ d0 p1 = twE σ d0 p1 * ((Ring.inverse (twE σ d0 p1) * α) * u') := by rw [huu', mul_one]
                _ = α * u' := by rw [← mul_assoc, ← mul_assoc, Ring.mul_inverse_cancel _ hAu', one_mul]
          _ = C_V * Vd α := mul_comm _ _
      · push Not at hne
        have : ∀ p1, {p1 : E | p1 ∈ Wu ∧ Ring.inverse (twE σ d0 p1) * α ∈ Uint (K := K) (L := L) (v := v)}.indicator (fun _ => Vd α) p1 = 0 := by
          intro p1; rw [Set.indicator_of_notMem]; exact fun h => hne p1 h.1 h.2
        simp_rw [this]
        rw [lintegral_zero]; exact zero_le
    calc ∫⁻ α, ∫⁻ p1, J (p1, α) ∂mW ∂mW ≤ ∫⁻ α, C_V * shell.indicator Vd α ∂mW := lintegral_mono hin
      _ = C_V * ∫⁻ α in shell, Vd α ∂mW := by
          rw [lintegral_const_mul'' _ ((hVdm.indicator hshellm).aemeasurable), lintegral_indicator hshellm]
      _ ≤ C_V * ∫⁻ α in shell, (⨆ β' : E, V ν g α β') ∂mW := by gcongr; exact hVd_le _
      _ ≤ C_V * (C_H * X) := by gcongr; exact hHT ‖Algebra.norm F d0‖
  calc Q0 ν σ g δ β ≤ C_V * ∫⁻ p1, G1 p1 ∂ν := hstep1
    _ ≤ C_V * (m₀⁻¹ * (C_V * (C_H * X))) := by gcongr

theorem norm_det_eq_of_Q0_ne_zero (g : G)
    (hδ₀₁ : (δ : Matrix (Fin 2) (Fin 2) E) 0 1 = 0) (hδ₁₀ : (δ : Matrix (Fin 2) (Fin 2) E) 1 0 = 0)
    {β : G → ℝ} (h : Q0 ν σ g δ β ≠ 0) :
    ‖Algebra.norm F ((Matrix.GeneralLinearGroup.det g : Eˣ) : E)‖ =
      ‖Algebra.norm F ((δ : Matrix (Fin 2) (Fin 2) E) 0 0) * Algebra.norm F ((δ : Matrix (Fin 2) (Fin 2) E) 1 1)‖ := by

  have hex : ∃ p : Q, D (K := K) (L := L) (v := v) p *
      (V ν g (twE σ ((δ : Matrix (Fin 2) (Fin 2) E) 0 0) p.1) (twE σ ((δ : Matrix (Fin 2) (Fin 2) E) 1 1) p.2) *
        ENNReal.ofReal (β (uGL p))) ≠ 0 := by
    by_contra hall
    push Not at hall
    apply h
    unfold Q0
    rw [lintegral_congr hall, lintegral_zero]
  obtain ⟨p, hp⟩ := hex
  have hgood : p ∈ goodT := by
    by_contra hng; exact hp (by rw [D_of_not hng, zero_mul])
  obtain ⟨hp1, hp2⟩ := (mem_goodT_iff p).1 hgood
  have hV : V ν g (twE σ ((δ : Matrix (Fin 2) (Fin 2) E) 0 0) p.1) (twE σ ((δ : Matrix (Fin 2) (Fin 2) E) 1 1) p.2) ≠ 0 := by
    intro h0; exact hp (by rw [h0, zero_mul, mul_zero])
  obtain ⟨ξ, h', hh', hcoe⟩ := nonempty_of_measure_ne_zero hV
  obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := (mem_Sset_iff g h').1 hh'

  have hdet : ((Matrix.GeneralLinearGroup.det k₁ : Eˣ) : E) * ((Matrix.GeneralLinearGroup.det g : Eˣ) : E) *
      ((Matrix.GeneralLinearGroup.det k₂ : Eˣ) : E) =
      twE σ ((δ : Matrix (Fin 2) (Fin 2) E) 0 0) p.1 * twE σ ((δ : Matrix (Fin 2) (Fin 2) E) 1 1) p.2 := by
    have : ((Matrix.GeneralLinearGroup.det (k₁ * g * k₂) : Eˣ) : E) =
        twE σ ((δ : Matrix (Fin 2) (Fin 2) E) 0 0) p.1 * twE σ ((δ : Matrix (Fin 2) (Fin 2) E) 1 1) p.2 := by
      show ((k₁ * g * k₂ : G) : Matrix (Fin 2) (Fin 2) E).det = _
      rw [hcoe, Matrix.det_fin_two_of]; ring
    rwa [map_mul, map_mul, Units.val_mul, Units.val_mul] at this
  have hk : ∀ k : G, k ∈ AutomorphicForm.semiLocalIntegralSet K L v →
      ‖Algebra.norm F ((Matrix.GeneralLinearGroup.det k : Eˣ) : E)‖ = 1 :=
    fun k hk => norm_algebraNorm_eq_one_of_mem_Uint ν (det_mem_Uint hk)
  have h1 := congrArg (fun x : E => ‖Algebra.norm F x‖) hdet
  simp only [map_mul, norm_mul, hk k₁ hk₁, hk k₂ hk₂, one_mul, mul_one] at h1
  rw [h1, algebraNorm_twE σ hp1, algebraNorm_twE σ hp2, norm_mul]

theorem main (g : G) [IsGalois K L] (hgen : ∀ τ₀ : L ≃ₐ[K] L, τ₀ ∈ Subgroup.zpowers σ) {cG : ℝ≥0∞} (hG : GHyp ν cG)
    (hab : a ≠ b) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b])
    (hδ₀₁ : (δ : Matrix (Fin 2) (Fin 2) E) 0 1 = 0) (hδ₁₀ : (δ : Matrix (Fin 2) (Fin 2) E) 1 0 = 0)
    (hN : Algebra.norm F ((δ : Matrix (Fin 2) (Fin 2) E) 0 0) ≠ Algebra.norm F ((δ : Matrix (Fin 2) (Fin 2) E) 1 1))
    (τ' : @Measure Tw (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hττ' : @Measure.map _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ)
        (AutomorphicForm.glBorelOf E) Subtype.val τ' =
      Measure.map (fun s : A => AutomorphicForm.toTensorGL K L F (s : GF)) τ)
    (W : Set F) (hWc : IsClosed W)
    (m₀ : ℝ≥0∞) (hm₀ : m₀ ≠ 0) (hm₀' : m₀ ≠ ⊤)
    (hm₀U : ∀ α : E, IsUnit α → (ν.withDensity fun b => ENNReal.ofReal ‖Algebra.norm F b‖⁻¹)
      {b : E | ∃ u ∈ Uint (K := K) (L := L) (v := v), b = α * u} = m₀)
    (C_V : ℝ≥0∞)
    (hVOL : ∀ (c : Eˣ) (p' : E),
      (ν.withDensity fun b => ENNReal.ofReal ‖Algebra.norm F b‖⁻¹)
        {b : E | IsUnit b ∧ Algebra.norm F b ∈ W ∧
          ∃ u ∈ Uint (K := K) (L := L) (v := v), (c : E) * AutomorphicForm.sigmaTensor K L F σ b = b * p' * u} ≤ C_V)
    (C_H : ℝ≥0∞) (Apow : ℕ)
    (hHT : ∀ r : ℝ, ∫⁻ α in {α : E | ‖Algebra.norm F α‖ = r},
        (⨆ β' : E, ν {ξ : E | ∃ h ∈ AutomorphicForm.semiLocalIntegralSet K L v * {g} * AutomorphicForm.semiLocalIntegralSet K L v,
            (h : Matrix (Fin 2) (Fin 2) E) = !![α, ξ; 0, β']})
          ∂(ν.withDensity fun b => ENNReal.ofReal ‖Algebra.norm F b‖⁻¹) ≤
        C_H * ENNReal.ofReal
          ((‖Algebra.norm F ((Matrix.GeneralLinearGroup.det g : Eˣ) : E)‖ *
              (AutomorphicForm.semiLocalHaar K L v (Sset (K := K) (L := L) (v := v) g)).toReal) ^ ((1 : ℝ) / 2) *
            (1 + Real.log (AutomorphicForm.semiLocalHaar K L v (Sset (K := K) (L := L) (v := v) g)).toReal) ^ Apow))
    {β : G → ℝ} (hβm : Measurable β) (hβ0 : ∀ x, 0 ≤ β x) (hβ1 : ∀ x, β x ≤ 1)
    (hβ : ∀ u : G, (u : Matrix (Fin 2) (Fin 2) E) 0 1 = 0 → (u : Matrix (Fin 2) (Fin 2) E) 1 0 = 0 →
      ∫ t : A, β (AutomorphicForm.toTensorGL K L F (t : GF) * u) ∂τ = 1)
    (hβW : ∀ p : Q, p ∈ goodT → β (uGL p) ≠ 0 → Algebra.norm F p.1 ∈ W ∧ Algebra.norm F p.2 ∈ W)
    {Yn : E → ℝ≥0∞} (hYm : Measurable Yn)
    (hY : ∀ y : E, ∃ η c : E, IsUnit η ∧ Yn y = (wt (K := K) (L := L) (v := v) (η ^ 2))⁻¹ ∧
        ∃ k : G, k ∈ 𝒦 ∧ ∀ (x : E) (p : Q), p ∈ goodT →
          uGL p * sGL (x, y) = uGL (p.1 * Ring.inverse η, p.2 * η) * sGL (η ^ 2 * x + c, 0) * k)
    {w : G → ℝ} (hw : AutomorphicForm.IsTwistedSectionFnOn K L F σ δ τ' (φS (K := K) (L := L) (v := v) g) w) :
    ENNReal.ofReal ‖Algebra.norm F ((δ : Matrix (Fin 2) (Fin 2) E) 0 0) - Algebra.norm F ((δ : Matrix (Fin 2) (Fin 2) E) 1 1)‖ *
      ∫⁻ x, ‖φS (K := K) (L := L) (v := v) g (x⁻¹ * δ * AutomorphicForm.sigmaGL K L F σ x)‖ₑ * ENNReal.ofReal (w x)
        ∂(AutomorphicForm.semiLocalHaar K L v) ≤
      cG * ((∫⁻ y, Yn y ∂ν) * (C_V * (m₀⁻¹ * (C_V * (C_H * ENNReal.ofReal
          ((‖Algebra.norm F ((Matrix.GeneralLinearGroup.det g : Eˣ) : E)‖ *
              (AutomorphicForm.semiLocalHaar K L v (Sset (K := K) (L := L) (v := v) g)).toReal) ^ ((1 : ℝ) / 2) *
            (1 + Real.log (AutomorphicForm.semiLocalHaar K L v (Sset (K := K) (L := L) (v := v) g)).toReal) ^ Apow)))))) := by
  set d : ℝ := ‖Algebra.norm F ((δ : Matrix (Fin 2) (Fin 2) E) 0 0) - Algebra.norm F ((δ : Matrix (Fin 2) (Fin 2) E) 1 1)‖ with hd
  have hd0 : ENNReal.ofReal d ≠ 0 := by
    rw [hd]; simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le, norm_pos_iff]; exact sub_ne_zero.2 hN
  have hdtop : ENNReal.ofReal d ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [lintegral_enorm_unfold ν σ τ hG hab hγ inferInstance hδ₀₁ hδ₁₀ τ' hττ' hβm hβ0 hβ (measurable_φS g) hw,
    total ν σ τ g hgen hab hγ hδ₀₁ hδ₁₀ hN hβm hβ0 hβ hYm hY]
  have hQ := Q0_le ν σ g (δ := δ) hδ₀₁ hδ₁₀ hN W hWc m₀ hm₀ hm₀' hm₀U C_V hVOL C_H Apow hHT hβm hβ0 hβ1 hβW
  calc ENNReal.ofReal d * (cG * ((∫⁻ y, Yn y ∂ν) * ((ENNReal.ofReal d)⁻¹ * Q0 ν σ g δ β)))
      = cG * ((∫⁻ y, Yn y ∂ν) * ((ENNReal.ofReal d * (ENNReal.ofReal d)⁻¹) * Q0 ν σ g δ β)) := by ring
    _ = cG * ((∫⁻ y, Yn y ∂ν) * Q0 ν σ g δ β) := by rw [ENNReal.mul_inv_cancel hd0 hdtop, one_mul]
    _ ≤ _ := by gcongr

theorem main' (g : G) [IsGalois K L] (hgen : ∀ τ₀ : L ≃ₐ[K] L, τ₀ ∈ Subgroup.zpowers σ) {cG : ℝ≥0∞} (hG : GHyp ν cG)
    (hab : a ≠ b) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b])
    (hδ₀₁ : (δ : Matrix (Fin 2) (Fin 2) E) 0 1 = 0) (hδ₁₀ : (δ : Matrix (Fin 2) (Fin 2) E) 1 0 = 0)
    (hN : Algebra.norm F ((δ : Matrix (Fin 2) (Fin 2) E) 0 0) ≠ Algebra.norm F ((δ : Matrix (Fin 2) (Fin 2) E) 1 1))
    (τ' : @Measure Tw (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hττ' : @Measure.map _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ)
        (AutomorphicForm.glBorelOf E) Subtype.val τ' =
      Measure.map (fun s : A => AutomorphicForm.toTensorGL K L F (s : GF)) τ)
    (W : Set F) (hWc : IsClosed W)
    (m₀ : ℝ≥0∞) (hm₀ : m₀ ≠ 0) (hm₀' : m₀ ≠ ⊤)
    (hm₀U : ∀ α : E, IsUnit α → (ν.withDensity fun b => ENNReal.ofReal ‖Algebra.norm F b‖⁻¹)
      {b : E | ∃ u ∈ Uint (K := K) (L := L) (v := v), b = α * u} = m₀)
    (C_V : ℝ≥0∞)
    (hVOL : ∀ (c : Eˣ) (p' : E),
      (ν.withDensity fun b => ENNReal.ofReal ‖Algebra.norm F b‖⁻¹)
        {b : E | IsUnit b ∧ Algebra.norm F b ∈ W ∧
          ∃ u ∈ Uint (K := K) (L := L) (v := v), (c : E) * AutomorphicForm.sigmaTensor K L F σ b = b * p' * u} ≤ C_V)
    (C_H : ℝ≥0∞) (Apow : ℕ)
    (hHT : ∀ r : ℝ, ∫⁻ α in {α : E | ‖Algebra.norm F α‖ = r},
        (⨆ β' : E, ν {ξ : E | ∃ h ∈ AutomorphicForm.semiLocalIntegralSet K L v * {g} * AutomorphicForm.semiLocalIntegralSet K L v,
            (h : Matrix (Fin 2) (Fin 2) E) = !![α, ξ; 0, β']})
          ∂(ν.withDensity fun b => ENNReal.ofReal ‖Algebra.norm F b‖⁻¹) ≤
        C_H * ENNReal.ofReal
          ((‖Algebra.norm F ((Matrix.GeneralLinearGroup.det g : Eˣ) : E)‖ *
              (AutomorphicForm.semiLocalHaar K L v (Sset (K := K) (L := L) (v := v) g)).toReal) ^ ((1 : ℝ) / 2) *
            (1 + Real.log (AutomorphicForm.semiLocalHaar K L v (Sset (K := K) (L := L) (v := v) g)).toReal) ^ Apow))
    {β : G → ℝ} (hβm : Measurable β) (hβ0 : ∀ x, 0 ≤ β x) (hβ1 : ∀ x, β x ≤ 1)
    (hβ : ∀ u : G, (u : Matrix (Fin 2) (Fin 2) E) 0 1 = 0 → (u : Matrix (Fin 2) (Fin 2) E) 1 0 = 0 →
      ∫ t : A, β (AutomorphicForm.toTensorGL K L F (t : GF) * u) ∂τ = 1)
    (hβW : ∀ p : Q, p ∈ goodT → β (uGL p) ≠ 0 → Algebra.norm F p.1 ∈ W ∧ Algebra.norm F p.2 ∈ W)
    {Yn : E → ℝ≥0∞} (hYm : Measurable Yn)
    (hY : ∀ y : E, ∃ η c : E, IsUnit η ∧ Yn y = (wt (K := K) (L := L) (v := v) (η ^ 2))⁻¹ ∧
        ∃ k : G, k ∈ 𝒦 ∧ ∀ (x : E) (p : Q), p ∈ goodT →
          uGL p * sGL (x, y) = uGL (p.1 * Ring.inverse η, p.2 * η) * sGL (η ^ 2 * x + c, 0) * k)
    {w : G → ℝ} (hw : AutomorphicForm.IsTwistedSectionFnOn K L F σ δ τ' (φS (K := K) (L := L) (v := v) g) w) :
    ENNReal.ofReal ‖Algebra.norm F ((δ : Matrix (Fin 2) (Fin 2) E) 0 0) - Algebra.norm F ((δ : Matrix (Fin 2) (Fin 2) E) 1 1)‖ *
      ∫⁻ x, ‖φS (K := K) (L := L) (v := v) g (x⁻¹ * δ * AutomorphicForm.sigmaGL K L F σ x)‖ₑ * ENNReal.ofReal (w x)
        ∂(AutomorphicForm.semiLocalHaar K L v) ≤
      cG * ((∫⁻ y, Yn y ∂ν) * (C_V * (m₀⁻¹ * (C_V * C_H)))) * ENNReal.ofReal
          ((‖Algebra.norm F ((δ : Matrix (Fin 2) (Fin 2) E) 0 0) * Algebra.norm F ((δ : Matrix (Fin 2) (Fin 2) E) 1 1)‖ *
              (AutomorphicForm.semiLocalHaar K L v (Sset (K := K) (L := L) (v := v) g)).toReal) ^ ((1 : ℝ) / 2) *
            (1 + Real.log (AutomorphicForm.semiLocalHaar K L v (Sset (K := K) (L := L) (v := v) g)).toReal) ^ Apow) := by
  by_cases hQ : Q0 ν σ g δ β = 0
  · rw [lintegral_enorm_unfold ν σ τ hG hab hγ inferInstance hδ₀₁ hδ₁₀ τ' hττ' hβm hβ0 hβ (measurable_φS g) hw,
      total ν σ τ g hgen hab hγ hδ₀₁ hδ₁₀ hN hβm hβ0 hβ hYm hY, hQ, mul_zero, mul_zero, mul_zero, mul_zero]
    exact zero_le
  · have hdet := norm_det_eq_of_Q0_ne_zero ν σ g hδ₀₁ hδ₁₀ hQ
    have h := main ν σ τ g hgen hG hab hγ hδ₀₁ hδ₁₀ hN τ' hττ' W hWc m₀ hm₀ hm₀' hm₀U C_V hVOL C_H Apow hHT
      hβm hβ0 hβ1 hβ hβW hYm hY hw
    rw [hdet] at h
    calc _ ≤ _ := h
      _ = _ := by ring

end Assembly

end K47C3
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_norm_sub_norm_mul_le_mul_rpow_mul_log_pow_of_isTwistedOrbitalIntegral_indicator_semiLocalIntegralSet_mul_mul.K47C3"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_norm_sub_norm_mul_le_mul_rpow_mul_log_pow_of_isTwistedOrbitalIntegral_indicator_semiLocalIntegralSet_mul_mul.K47C3"

set_option maxHeartbeats 20000000 in
open scoped Classical in
open K47C3 in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ A : ℕ,
    ∀ (a : GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
    ∀ (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
      (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 0 = 0 →
      (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 1 = 0 →
      Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0) ≠
        Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1) →
    ∀ (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
        (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ)),
      @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ' →
      τ' (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1 →
    ∀ I : ℂ, AutomorphicForm.IsTwistedOrbitalIntegral K L v σ δ τ'
        ((AutomorphicForm.semiLocalIntegralSet K L v * {a} * AutomorphicForm.semiLocalIntegralSet K L v).indicator
          (fun _ => (1 : ℂ))) I →
      ‖Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0) -
          Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1)‖ * ‖I‖ ≤
        C * (‖Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0) *
                Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1)‖ *
              (AutomorphicForm.semiLocalHaar K L v
                (AutomorphicForm.semiLocalIntegralSet K L v * {a} *
                  AutomorphicForm.semiLocalIntegralSet K L v)).toReal) ^ ((1 : ℝ) / 2) *
          (1 + Real.log (AutomorphicForm.semiLocalHaar K L v
                (AutomorphicForm.semiLocalIntegralSet K L v * {a} *
                  AutomorphicForm.semiLocalIntegralSet K L v)).toReal) ^ A := by
  classical

  letI mE : MeasurableSpace (L ⊗[K] v.adicCompletion K) := borel _
  haveI bE : BorelSpace (L ⊗[K] v.adicCompletion K) := ⟨rfl⟩
  haveI := isTopologicalRing_E (K := K) (L := L) (v := v)
  haveI := locallyCompactSpace_E (K := K) (L := L) (v := v)
  haveI := t2Space_E (K := K) (L := L) (v := v)
  haveI := secondCountableTopology_E (K := K) (L := L) (v := v)
  letI mG : MeasurableSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := AutomorphicForm.glBorelOf _
  haveI bG : BorelSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := AutomorphicForm.borelSpace_glBorelOf _
  set ν : Measure (L ⊗[K] v.adicCompletion K) := Measure.addHaar with hν

  obtain ⟨cG, hcG0, hcGtop, hG⟩ :=
    AutomorphicForm.exists_forall_lintegral_semiLocalHaar_eq_mul_lintegral_pi_norm_algebraNorm_det_inv_sq K L v ν
  obtain ⟨Yn, hYm, hYfin, hY⟩ := exists_absorb (K := K) (L := L) (v := v) ν
  obtain ⟨hWc, hW0⟩ := isCompact_window (K := K) (v := v) (Module.finrank K L)
  obtain ⟨m₀, hm₀, hm₀', hm₀U⟩ := exists_mass_Uint (K := K) (L := L) (v := v) ν
  obtain ⟨C_V, hCV, hVOL⟩ :=
    AutomorphicForm.exists_forall_withDensity_norm_inv_setOf_norm_mem_and_mul_sigmaTensor_eq_mul_mul_le K L σ hgen v ν
      _ hWc hW0 (Uint (K := K) (L := L) (v := v)) isCompact_Uint (fun u hu => isUnit_of_mem_Uint hu)
  obtain ⟨C_H, hCH, Apow, hHT⟩ :=
    AutomorphicForm.exists_forall_setLIntegral_withDensity_norm_inv_iSup_measure_setOf_upperTriangular_mem_doubleCoset_le
      K L v ν
  refine ⟨(cG * ((∫⁻ y, Yn y ∂ν) * (C_V * (m₀⁻¹ * (C_V * C_H))))).toReal, ENNReal.toReal_nonneg, Apow, ?_⟩
  intro g δ h10 h01 hN τ' hτ' hτ'1 I hI

  set a0 : v.adicCompletion K := Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0) with ha0
  set b0 : v.adicCompletion K := Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1) with hb0
  have hγdet : IsUnit (!![a0, 0; 0, b0] : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det := by
    have hd : IsUnit ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).det) := Matrix.isUnits_det_units δ
    rw [Matrix.det_fin_two, h01, zero_mul, sub_zero, IsUnit.mul_iff] at hd
    rw [Matrix.det_fin_two_of, mul_zero, sub_zero]
    exact (hd.1.map (Algebra.norm (v.adicCompletion K))).mul (hd.2.map (Algebra.norm (v.adicCompletion K)))
  set γ : GL (Fin 2) (v.adicCompletion K) := Matrix.GeneralLinearGroup.mk'' _ hγdet with hγdef
  have hγ : (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = !![a0, 0; 0, b0] := rfl
  obtain ⟨-, hT⟩ :=
    AutomorphicForm.twistedCentralizer_eq_map_toTensorGL_localCentralizer_and_exists_isHaarMeasure_map_eq_of_diagonal_of_norm_ne
      K L σ hgen v δ h10 h01 hN a0 b0 hN γ hγ
  obtain ⟨τ, hτ, hττ'⟩ := hT τ' hτ'
  letI mA : MeasurableSpace (AutomorphicForm.localCentralizer K v γ) := AutomorphicForm.localCentralizerBorel K v γ
  haveI : BorelSpace (AutomorphicForm.localCentralizer K v γ) := borelSpace_A (K := K) (v := v) γ
  haveI := hτ
  have hτ1 : τ {s : AutomorphicForm.localCentralizer K v γ |
      (s : GL (Fin 2) (v.adicCompletion K)) ∈ AutomorphicForm.localIntegralSet K v} = 1 := by
    letI := AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ
    haveI : BorelSpace (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ) := ⟨rfl⟩
    have hmeas : MeasurableSet (AutomorphicForm.semiLocalIntegralSet K L v) :=
      (AutomorphicForm.isOpen_semiLocalIntegralSet K L v).measurableSet
    have e1 : (Measure.map (Subtype.val : AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ →
        GL (Fin 2) (L ⊗[K] v.adicCompletion K)) τ') (AutomorphicForm.semiLocalIntegralSet K L v) = 1 := by
      rw [Measure.map_apply continuous_subtype_val.measurable hmeas]; exact hτ'1
    have e2 : (Measure.map (fun s : AutomorphicForm.localCentralizer K v γ =>
        AutomorphicForm.toTensorGL K L (v.adicCompletion K) (s : GL (Fin 2) (v.adicCompletion K))) τ)
          (AutomorphicForm.semiLocalIntegralSet K L v) =
        τ {s : AutomorphicForm.localCentralizer K v γ |
          (s : GL (Fin 2) (v.adicCompletion K)) ∈ AutomorphicForm.localIntegralSet K v} := by
      rw [Measure.map_apply measurable_toTensorGL_A hmeas]
      congr 1
      ext s
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      exact AutomorphicForm.toTensorGL_mem_semiLocalIntegralSet_iff_mem_localIntegralSet K L v _
    rw [hττ', e2] at e1
    exact e1
  obtain ⟨β, hβm, hβ0, hβ1, hβ, hβW⟩ :=
    AutomorphicForm.exists_windowed_section_localCentralizer_toTensorGL_of_diagonal K L v a0 b0 hN γ hγ τ hτ hτ1
  have hβW' : ∀ p : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K), p ∈ goodT → β (uGL p) ≠ 0 →
      Algebra.norm (v.adicCompletion K) p.1 ∈
          {y : v.adicCompletion K | ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ Module.finrank K L ≤ ‖y‖ ∧ ‖y‖ ≤ 1} ∧
        Algebra.norm (v.adicCompletion K) p.2 ∈
          {y : v.adicCompletion K | ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ Module.finrank K L ≤ ‖y‖ ∧ ‖y‖ ≤ 1} := by
    intro p hp hβp
    have h01' : ((uGL p : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 1 = 0 := by
      rw [coe_uGL_of_mem hp]; rfl
    have h10' : ((uGL p : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 0 = 0 := by
      rw [coe_uGL_of_mem hp]; rfl
    have h00 : ((uGL p : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0 = p.1 := by
      rw [coe_uGL_of_mem hp]; rfl
    have h11 : ((uGL p : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1 = p.2 := by
      rw [coe_uGL_of_mem hp]; rfl
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hβW (uGL p) h01' h10' hβp
    rw [h00] at h1 h2; rw [h11] at h3 h4
    exact ⟨⟨h1.le, h2⟩, ⟨h3.le, h4⟩⟩

  obtain ⟨w, hw, hIw⟩ := hI
  have key := main' ν σ τ g hgen hG hN hγ h01 h10 hN τ' hττ' _ hWc.isClosed
    m₀ hm₀ hm₀' hm₀U C_V hVOL C_H Apow (hHT g) hβm hβ0 hβ1 hβ hβW' hYm hY hw

  change ‖a0 - b0‖ * ‖I‖ ≤ _ * (‖a0 * b0‖ * (AutomorphicForm.semiLocalHaar K L v (Sset (K := K) (L := L) (v := v) g)).toReal) ^ ((1 : ℝ) / 2) *
    (1 + Real.log (AutomorphicForm.semiLocalHaar K L v (Sset (K := K) (L := L) (v := v) g)).toReal) ^ Apow
  obtain ⟨hS1, hStop⟩ := one_le_semiLocalHaar_Sset_and_ne_top (K := K) (L := L) (v := v) g
  set μS : ℝ≥0∞ := AutomorphicForm.semiLocalHaar K L v (Sset (K := K) (L := L) (v := v) g) with hμS
  have hμS1 : 1 ≤ μS.toReal := by
    have := ENNReal.toReal_mono hStop hS1
    rwa [ENNReal.toReal_one] at this
  have hlog : 0 ≤ 1 + Real.log μS.toReal := by
    have := Real.log_nonneg hμS1; linarith
  set X : ℝ := (‖a0 * b0‖ * μS.toReal) ^ ((1 : ℝ) / 2) * (1 + Real.log μS.toReal) ^ Apow with hX
  have hX0 : 0 ≤ X := mul_nonneg (Real.rpow_nonneg (mul_nonneg (norm_nonneg _) ENNReal.toReal_nonneg) _) (pow_nonneg hlog _)
  set Cc : ℝ≥0∞ := cG * ((∫⁻ y, Yn y ∂ν) * (C_V * (m₀⁻¹ * (C_V * C_H)))) with hCc
  have hCctop : Cc ≠ ⊤ :=
    ENNReal.mul_ne_top hcGtop (ENNReal.mul_ne_top hYfin (ENNReal.mul_ne_top hCV
      (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hm₀) (ENNReal.mul_ne_top hCV hCH))))
  have hw0 : ∀ x, 0 ≤ w x := hw.1
  set LI : ℝ≥0∞ := ∫⁻ x, ‖φS (K := K) (L := L) (v := v) g (x⁻¹ * δ * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x)‖ₑ *
      ENNReal.ofReal (w x) ∂(AutomorphicForm.semiLocalHaar K L v) with hLI
  have hI1 : ‖I‖ ≤ LI.toReal := by
    rw [hIw]
    refine (norm_integral_le_lintegral_norm _).trans (le_of_eq ?_)
    congr 1
    refine lintegral_congr fun x => ?_
    rw [ofReal_norm, enorm_mul]
    congr 1
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (hw0 _)]
  have h2 : ‖a0 - b0‖ * ‖I‖ ≤ (ENNReal.ofReal ‖a0 - b0‖ * LI).toReal := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _)]
    exact mul_le_mul_of_nonneg_left hI1 (norm_nonneg _)
  have h3 : (ENNReal.ofReal ‖a0 - b0‖ * LI).toReal ≤ (Cc * ENNReal.ofReal X).toReal :=
    ENNReal.toReal_mono (ENNReal.mul_ne_top hCctop ENNReal.ofReal_ne_top) key
  have h4 : (Cc * ENNReal.ofReal X).toReal = Cc.toReal * X := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hX0]
  calc ‖a0 - b0‖ * ‖I‖ ≤ (ENNReal.ofReal ‖a0 - b0‖ * LI).toReal := h2
    _ ≤ (Cc * ENNReal.ofReal X).toReal := h3
    _ = Cc.toReal * X := h4
    _ = _ := by rw [hX, mul_assoc]

end S_AutomorphicForm_exists_forall_norm_sub_norm_mul_le_mul_rpow_mul_log_pow_of_isTwistedOrbitalIntegral_indicator_semiLocalIntegralSet_mul_mul
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_norm_sub_norm_mul_le_mul_rpow_mul_log_pow_of_isTwistedOrbitalIntegral_indicator_semiLocalIntegralSet_mul_mul (solution)
