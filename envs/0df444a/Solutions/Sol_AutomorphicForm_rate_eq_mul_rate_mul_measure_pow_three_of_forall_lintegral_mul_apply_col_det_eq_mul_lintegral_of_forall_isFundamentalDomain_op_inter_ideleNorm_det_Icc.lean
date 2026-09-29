-- Prove2me | solution 1 for AutomorphicForm.rate_eq_mul_rate_mul_measure_pow_three_of_forall_lintegral_mul_apply_col_det_eq_mul_lintegral_of_forall_isFundamentalDomain_op_inter_ideleNorm_det_Icc
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/450095f5-47ee-53c1-b858-542b1940abf8

import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Theorems.Thm_AutomorphicForm_setLIntegral_mul_tsum_apply_mulVec_eq_mul_measure_mul_lintegral_mul_setLIntegral_of_isFundamentalDomain_op
import Theorems.Thm_NumberField_AdelicFourier_tsum_apply_smul_vecMul_add_eq_ideleNorm_cpow_neg_two_mul_tsum_reflectPair_of_mem_schwartzBruhat2
import Theorems.Thm_MeasureTheory_Measure_map_eq_self_of_involutive_of_isHaarMeasure
import Theorems.Thm_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar
import Theorems.Thm_NumberField_AdelicBox_exists_isAddHaarMeasure_adelicBox_eq_one
import Theorems.Thm_NumberField_AdelicFourier_fourierTransform2_mem_schwartzBruhat2_and_reflectPair_mem_schwartzBruhat2
import Theorems.Thm_NumberField_AdelicFourier_continuous_integrable_comp_vecMul_mem_and_bottomRowVec_mem_schwartzBruhat_of_mem_schwartzBruhat2
import Theorems.Thm_NumberField_AdelicFourier_exists_forall_tsum_norm_apply_smul_vecMul_le_and_continuous_tsum_of_mem_schwartzBruhat2
import Theorems.Thm_NumberField_AdelicFourier_exists_smul_eq_of_isAddHaarMeasure_adeleRing
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_rate_eq_mul_rate_mul_measure_pow_three_of_forall_lintegral_mul_apply_col_det_eq_mul_lintegral_of_forall_isFundamentalDomain_op_inter_ideleNorm_det_Icc
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply ContinuousAddEquiv.preimage_mulLeft_smul IsModuleTopology.continuousLinearEquiv_apply"
p2m_attr_erase "simp" "AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
open scoped ENNReal Pointwise

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "globalPoints unipotentGL2 setLIntegral_mul_tsum_apply_mulVec_eq_mul_measure_mul_lintegral_mul_setLIntegral_of_isFundamentalDomain_op"
namespace WeilCovolume
p2m_open "AutomorphicForm"

section Rate

variable {X : Type*} [MeasurableSpace X]

theorem setLIntegral_ofReal_inv_eq_of_forall_measure_inter_Icc (ρ : Measure X) (A : Set X)
    (f : X → ℝ) (hf : Measurable f) (hpos : ∀ x, 0 < f x) (R : ℝ≥0∞) (hR : R ≠ ⊤)
    (hrate : ∀ a b : ℝ, 0 < a → a ≤ b →
      ρ (A ∩ {x | f x ∈ Set.Icc a b}) = R * ENNReal.ofReal (Real.log (b / a)))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫⁻ x in A ∩ {x | f x ∈ Set.Icc a b}, ENNReal.ofReal (f x)⁻¹ ∂ρ = R * ENNReal.ofReal (a⁻¹ - b⁻¹) := by

  set φ : X → ℝ := fun x => Real.log (f x) with hφ_def
  have hφ : Measurable φ := Real.measurable_log.comp hf
  set m : Measure ℝ := Measure.map φ (ρ.restrict A) with hm_def
  have hpre : ∀ s t : ℝ, φ ⁻¹' Set.Icc s t = {x | f x ∈ Set.Icc (Real.exp s) (Real.exp t)} := by
    intro s t
    ext x
    simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_setOf_eq, hφ_def]
    rw [Real.le_log_iff_exp_le (hpos x), Real.log_le_iff_le_exp (hpos x)]
  have hIcc : ∀ s t : ℝ, s ≤ t → m (Set.Icc s t) = R * ENNReal.ofReal (t - s) := by
    intro s t hst
    rw [hm_def, Measure.map_apply hφ measurableSet_Icc, Measure.restrict_apply (hφ measurableSet_Icc), hpre,
      Set.inter_comm, hrate _ _ (Real.exp_pos s) (Real.exp_le_exp.2 hst), ← Real.exp_sub, Real.log_exp]
  have hpt : ∀ s : ℝ, m {s} = 0 := by
    intro s
    rw [← Set.Icc_self, hIcc s s le_rfl, sub_self, ENNReal.ofReal_zero, mul_zero]
  have hIco : ∀ s t : ℝ, s < t → m (Set.Ico s t) = R * ENNReal.ofReal (t - s) := by
    intro s t hst
    rw [← Set.Icc_sdiff_right, measure_diff_null (hpt t), hIcc s t hst.le]
  haveI : IsLocallyFiniteMeasure m := by
    refine ⟨fun x => ⟨Set.Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith), ?_⟩⟩
    rw [hIcc _ _ (by linarith)]
    exact ENNReal.mul_lt_top hR.lt_top ENNReal.ofReal_lt_top
  have hm : m = R • (volume : Measure ℝ) := by
    refine Measure.ext_of_Ico m (R • volume) fun s t hst => ?_
    rw [hIco s t hst, Measure.smul_apply, Real.volume_Ico, smul_eq_mul]

  set Gf : ℝ → ℝ≥0∞ := (Set.Icc (Real.log a) (Real.log b)).indicator fun u => ENNReal.ofReal (Real.exp (-u))
    with hGf_def
  have hGf : Measurable Gf := (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp measurable_neg)).indicator
    measurableSet_Icc
  have hcomp : ∀ x, ({x | f x ∈ Set.Icc a b} : Set X).indicator (fun x => ENNReal.ofReal (f x)⁻¹) x = Gf (φ x) := by
    intro x
    have hiff : f x ∈ Set.Icc a b ↔ φ x ∈ Set.Icc (Real.log a) (Real.log b) := by
      simp only [Set.mem_Icc, hφ_def]
      rw [Real.log_le_log_iff ha (hpos x), Real.log_le_log_iff (hpos x) (ha.trans_le hab)]
    by_cases hx : f x ∈ Set.Icc a b
    · rw [Set.indicator_of_mem (show x ∈ {x | f x ∈ Set.Icc a b} from hx), hGf_def,
        Set.indicator_of_mem (hiff.1 hx), hφ_def]
      simp only [Real.exp_neg, Real.exp_log (hpos x)]
    · rw [Set.indicator_of_notMem (show x ∉ {x | f x ∈ Set.Icc a b} from hx), hGf_def,
        Set.indicator_of_notMem (fun h' => hx (hiff.2 h'))]
  have hmeasS : MeasurableSet ({x | f x ∈ Set.Icc a b} : Set X) := hf measurableSet_Icc
  calc ∫⁻ x in A ∩ {x | f x ∈ Set.Icc a b}, ENNReal.ofReal (f x)⁻¹ ∂ρ
      = ∫⁻ x in A, ({x | f x ∈ Set.Icc a b} : Set X).indicator (fun x => ENNReal.ofReal (f x)⁻¹) x ∂ρ := by
        rw [Set.inter_comm, ← Measure.restrict_restrict hmeasS, lintegral_indicator hmeasS]
    _ = ∫⁻ x in A, Gf (φ x) ∂ρ := lintegral_congr fun x => hcomp x
    _ = ∫⁻ u, Gf u ∂m := (lintegral_map hGf hφ).symm
    _ = R * ∫⁻ u in Set.Icc (Real.log a) (Real.log b), ENNReal.ofReal (Real.exp (-u)) := by
        rw [hm, lintegral_smul_measure, hGf_def, lintegral_indicator measurableSet_Icc, smul_eq_mul]
    _ = R * ENNReal.ofReal (∫ u in Set.Icc (Real.log a) (Real.log b), Real.exp (-u)) := by
        have hcont : Continuous fun u : ℝ => Real.exp (-u) := Real.continuous_exp.comp continuous_neg
        rw [ofReal_integral_eq_lintegral_ofReal hcont.integrableOn_Icc
          (Filter.Eventually.of_forall fun u => (Real.exp_pos _).le)]
    _ = R * ENNReal.ofReal (a⁻¹ - b⁻¹) := by
        congr 2
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (Real.log_le_log ha hab),
          intervalIntegral.integral_comp_neg (fun u => Real.exp u), integral_exp, Real.exp_neg, Real.exp_neg,
          Real.exp_log ha, Real.exp_log (ha.trans_le hab)]

theorem setLIntegral_inter_setOf_mem_eq {ρ : Measure X} {A : Set X} {f : X → ℝ} (hf : Measurable f)
    (I : Set ℝ) (hI : MeasurableSet I) (F : X → ℝ≥0∞) :
    ∫⁻ x in A ∩ {x | f x ∈ I}, F x ∂ρ = ∫⁻ x in A, I.indicator (1 : ℝ → ℝ≥0∞) (f x) * F x ∂ρ := by
  have hmeasS : MeasurableSet ({x | f x ∈ I} : Set X) := hf hI
  rw [Set.inter_comm, ← Measure.restrict_restrict hmeasS, ← lintegral_indicator hmeasS]
  refine lintegral_congr fun x => ?_
  by_cases hx : f x ∈ I
  · rw [Set.indicator_of_mem (show x ∈ {x | f x ∈ I} from hx), Set.indicator_of_mem hx, Pi.one_apply, one_mul]
  · rw [Set.indicator_of_notMem (show x ∉ {x | f x ∈ I} from hx), Set.indicator_of_notMem hx, zero_mul]

end Rate

section Iota

variable {R : Type*} [CommRing R]

def iotaFun (g : GL (Fin 2) R) : GL (Fin 2) R :=
  Matrix.GeneralLinearGroup.scalar (Fin 2) (Matrix.GeneralLinearGroup.det g)⁻¹ * g

theorem coe_scalar (u : Rˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      Matrix.diagonal fun _ => (u : R) := by
  show ((Units.map (Matrix.scalar (Fin 2) : R →+* Matrix (Fin 2) (Fin 2) R).toMonoidHom) u : Matrix (Fin 2) (Fin 2) R)
    = _
  rw [Units.coe_map]
  exact Matrix.scalar_apply (u : R)

theorem scalar_mul_comm (u : Rˣ) (g : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) u * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_scalar, ← Matrix.scalar_apply]
  exact (Matrix.scalar_commute (u : R) (fun r' => Commute.all _ _) _).eq

theorem det_scalar_two (u : Rˣ) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) u) = u ^ 2 := by
  rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]

theorem det_iotaFun (g : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.det (iotaFun g) = (Matrix.GeneralLinearGroup.det g)⁻¹ := by
  rw [iotaFun, map_mul, det_scalar_two, sq, inv_mul_cancel_right]

theorem iotaFun_iotaFun (g : GL (Fin 2) R) : iotaFun (iotaFun g) = g := by
  rw [iotaFun, det_iotaFun, inv_inv, iotaFun, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]

theorem coe_iotaFun (g : GL (Fin 2) R) :
    ((iotaFun g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      (((Matrix.GeneralLinearGroup.det g)⁻¹ : Rˣ) : R) • (g : Matrix (Fin 2) (Fin 2) R) := by
  rw [iotaFun, Matrix.GeneralLinearGroup.coe_mul, coe_scalar, ← Matrix.smul_eq_diagonal_mul]

theorem iotaFun_mul (g h : GL (Fin 2) R) : iotaFun (g * h) = iotaFun g * iotaFun h := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.coe_mul, coe_iotaFun, coe_iotaFun, coe_iotaFun, Matrix.GeneralLinearGroup.coe_mul,
    map_mul, mul_inv, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Units.val_mul, mul_comm]

def iota : GL (Fin 2) R ≃* GL (Fin 2) R where
  toFun := iotaFun
  invFun := iotaFun
  left_inv := iotaFun_iotaFun
  right_inv := iotaFun_iotaFun
  map_mul' := iotaFun_mul

theorem iota_apply (g : GL (Fin 2) R) :
    iota g = Matrix.GeneralLinearGroup.scalar (Fin 2) (Matrix.GeneralLinearGroup.det g)⁻¹ * g := rfl

theorem iota_iota (g : GL (Fin 2) R) : iota (iota g) = g := iotaFun_iotaFun g

theorem det_iota (g : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.det (iota g) = (Matrix.GeneralLinearGroup.det g)⁻¹ := det_iotaFun g

theorem coe_iota (g : GL (Fin 2) R) :
    ((iota g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      (((Matrix.GeneralLinearGroup.det g)⁻¹ : Rˣ) : R) • (g : Matrix (Fin 2) (Fin 2) R) :=
  coe_iotaFun g

theorem iota_mulVec (g : GL (Fin 2) R) (v : Fin 2 → R) :
    ((iota g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R).mulVec v =
      (((Matrix.GeneralLinearGroup.det g)⁻¹ : Rˣ) : R) • (g : Matrix (Fin 2) (Fin 2) R).mulVec v := by
  rw [coe_iota, Matrix.smul_mulVec]

theorem det_map {S : Type*} [CommRing S] (f : R →+* S) (γ : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map f γ) =
      Units.map (f : R →* S) (Matrix.GeneralLinearGroup.det γ) := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.coe_map, MonoidHom.coe_coe, Matrix.GeneralLinearGroup.val_det_apply]
  have : ((Matrix.GeneralLinearGroup.map f γ : GL (Fin 2) S) : Matrix (Fin 2) (Fin 2) S) =
      (γ : Matrix (Fin 2) (Fin 2) R).map f := by
    ext i j; exact Matrix.GeneralLinearGroup.map_apply f i j γ
  rw [this, RingHom.map_det, RingHom.mapMatrix_apply]

theorem iota_map {S : Type*} [CommRing S] (f : R →+* S) (γ : GL (Fin 2) R) :
    iota (Matrix.GeneralLinearGroup.map f γ) = Matrix.GeneralLinearGroup.map f (iota γ) := by
  refine Units.ext ?_
  rw [coe_iota]
  ext i j
  rw [Matrix.smul_apply, Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.map_apply, coe_iota,
    Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, det_map, ← map_inv, Units.coe_map, MonoidHom.coe_coe]

end Iota

section Adelic

variable (K : Type) [Field K] [NumberField K]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]

local notation "𝔸" => AdeleRing (𝓞 K) K
local notation "G" => GL (Fin 2) (AdeleRing (𝓞 K) K)

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdeleRing.secondCountableTopology NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo

theorem continuous_det : Continuous fun g : G => Matrix.GeneralLinearGroup.det g := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have : (Units.val ∘ fun g : G => Matrix.GeneralLinearGroup.det g) =
        fun g : G => (g : Matrix (Fin 2) (Fin 2) 𝔸).det := by
      funext g; exact Matrix.GeneralLinearGroup.val_det_apply g
    rw [this]
    exact Units.continuous_val.matrix_det
  · have : (fun g : G => ((Matrix.GeneralLinearGroup.det g)⁻¹ : (𝔸)ˣ).1) =
        fun g : G => ((g⁻¹ : G) : Matrix (Fin 2) (Fin 2) 𝔸).det := by
      funext g
      rw [← map_inv]
      exact Matrix.GeneralLinearGroup.val_det_apply g⁻¹
    rw [this]
    exact (Units.continuous_val.comp continuous_inv).matrix_det

theorem measurable_det : Measurable fun g : G => Matrix.GeneralLinearGroup.det g :=
  (continuous_det K).measurable

theorem measurable_ideleNorm : Measurable (NumberField.TateGlobal.ideleNorm K) :=
  (NumberField.TateGlobal.continuous_ideleNorm K).measurable

abbrev Ndet (g : G) : ℝ := NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)

theorem measurable_Ndet : Measurable (Ndet K) := (measurable_ideleNorm K).comp (measurable_det K)

theorem Ndet_pos (g : G) : 0 < Ndet K g := NumberField.TateGlobal.ideleNorm_pos _

theorem measurable_mulVec (v : Fin 2 → 𝔸) : Measurable fun g : G => (g : Matrix (Fin 2) (Fin 2) 𝔸).mulVec v :=
  ((Units.continuous_val).matrix_mulVec continuous_const).measurable

theorem continuous_scalar : Continuous fun u : (𝔸)ˣ => (Matrix.GeneralLinearGroup.scalar (Fin 2) u : G) := by
  have h : Continuous (Matrix.scalar (Fin 2) : 𝔸 →+* Matrix (Fin 2) (Fin 2) 𝔸) := by
    have : (fun a : 𝔸 => Matrix.scalar (Fin 2) a) = fun a : 𝔸 => Matrix.diagonal fun _ : Fin 2 => a := by
      funext a; exact Matrix.scalar_apply a
    show Continuous fun a : 𝔸 => Matrix.scalar (Fin 2) a
    rw [this]
    exact (continuous_pi fun _ => continuous_id).matrix_diagonal
  exact Continuous.units_map ((Matrix.scalar (Fin 2) : 𝔸 →+* Matrix (Fin 2) (Fin 2) 𝔸).toMonoidHom) h

theorem continuous_iota : Continuous fun g : G => (iota g : G) := by
  show Continuous fun g : G => Matrix.GeneralLinearGroup.scalar (Fin 2) (Matrix.GeneralLinearGroup.det g)⁻¹ * g
  exact ((continuous_scalar K).comp ((continuous_det K).inv)).mul continuous_id

theorem measurable_iota : Measurable fun g : G => (iota g : G) := (continuous_iota K).measurable

theorem ideleNorm_inv (x : (𝔸)ˣ) : NumberField.TateGlobal.ideleNorm K x⁻¹ = (NumberField.TateGlobal.ideleNorm K x)⁻¹ := by
  unfold NumberField.TateGlobal.ideleNorm
  rw [map_inv, NNReal.coe_inv]

theorem Ndet_iota (g : G) : Ndet K (iota g) = (Ndet K g)⁻¹ := by
  show NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (iota g)) = _
  rw [det_iota, ideleNorm_inv]

theorem map_iota_eq (τ : Measure G) [τ.IsHaarMeasure] : Measure.map (fun g : G => (iota g : G)) τ = τ :=
  MeasureTheory.Measure.map_eq_self_of_involutive_of_isHaarMeasure τ iota (continuous_iota K) iota_iota

theorem measurePreserving_iota (τ : Measure G) [τ.IsHaarMeasure] :
    MeasurePreserving (fun g : G => (iota g : G)) τ τ :=
  ⟨measurable_iota K, map_iota_eq K τ⟩

theorem iota_globalPoints (γ : GL (Fin 2) K) : iota (globalPoints (𝓞 K) K γ) = globalPoints (𝓞 K) K (iota γ) :=
  iota_map (algebraMap K 𝔸) γ

theorem isFundamentalDomain_preimage_iota (τ : Measure G) [τ.IsHaarMeasure] {D : Set G}
    (hD : IsFundamentalDomain ((globalPoints (𝓞 K) K).range).op D τ) :
    IsFundamentalDomain ((globalPoints (𝓞 K) K).range).op ((fun g : G => (iota g : G)) ⁻¹' D) τ := by

  have hmem : ∀ x : ↥((globalPoints (𝓞 K) K).range).op,
      MulOpposite.op (iota (MulOpposite.unop x.1) : G) ∈ ((globalPoints (𝓞 K) K).range).op := fun x => by
    obtain ⟨γ, hγ⟩ := Subgroup.mem_op.1 x.2
    refine Subgroup.mem_op.2 ⟨iota γ, ?_⟩
    show globalPoints (𝓞 K) K (iota γ) = iota (MulOpposite.unop x.1)
    rw [← iota_globalPoints, hγ]
  let e : ↥((globalPoints (𝓞 K) K).range).op → ↥((globalPoints (𝓞 K) K).range).op := fun x =>
    ⟨MulOpposite.op (iota (MulOpposite.unop x.1) : G), hmem x⟩
  have he_inv : Function.Involutive e := fun x => Subtype.ext (by
    show MulOpposite.op (iota (MulOpposite.unop (MulOpposite.op (iota (MulOpposite.unop x.1) : G))) : G) = x.1
    rw [MulOpposite.unop_op, iota_iota, MulOpposite.op_unop])
  refine hD.preimage_of_equiv (measurePreserving_iota K τ).quasiMeasurePreserving he_inv.bijective fun x g => ?_
  show iota (g * MulOpposite.unop (e x).1 : G) = iota g * MulOpposite.unop x.1
  show iota (g * iota (MulOpposite.unop x.1) : G) = iota g * MulOpposite.unop x.1
  rw [map_mul, iota_iota]

theorem measurableSet_preimage_iota {D : Set G} (hDm : MeasurableSet D) :
    MeasurableSet ((fun g : G => (iota g : G)) ⁻¹' D) :=
  hDm.preimage (measurable_iota K)

def slab (a b : ℝ) : Set G := {g | Ndet K g ∈ Set.Icc a b}

theorem measurableSet_slab (a b : ℝ) : MeasurableSet (slab K a b) := (measurable_Ndet K) measurableSet_Icc

theorem iota_mem_slab_iff {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (g : G) :
    (iota g : G) ∈ slab K a b ↔ g ∈ slab K b⁻¹ a⁻¹ := by
  simp only [slab, Set.mem_setOf_eq, Set.mem_Icc, Ndet_iota]
  have hp := Ndet_pos K g
  rw [le_inv_comm₀ ha hp, inv_le_comm₀ hp hb, and_comm]

theorem setLIntegral_comp_iota (τ : Measure G) [τ.IsHaarMeasure] {D : Set G} (hDm : MeasurableSet D)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (F : G → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ g in D ∩ slab K a b, F (iota g) ∂τ =
      ∫⁻ g in ((fun g : G => (iota g : G)) ⁻¹' D) ∩ slab K b⁻¹ a⁻¹, F g ∂τ := by
  set T : Set G := ((fun g : G => (iota g : G)) ⁻¹' D) ∩ slab K b⁻¹ a⁻¹ with hT
  have hTm : MeasurableSet T := (measurableSet_preimage_iota K hDm).inter (measurableSet_slab K _ _)
  have hpre : (fun g : G => (iota g : G)) ⁻¹' T = D ∩ slab K a b := by
    ext g
    simp only [hT, Set.mem_preimage, Set.mem_inter_iff, iota_iota]
    rw [iota_mem_slab_iff K (inv_pos.2 hb) (inv_pos.2 ha), inv_inv, inv_inv]
  calc ∫⁻ g in D ∩ slab K a b, F (iota g) ∂τ
      = ∫⁻ g, (D ∩ slab K a b).indicator (fun g => F (iota g)) g ∂τ :=
        (lintegral_indicator (hDm.inter (measurableSet_slab K a b)) _).symm
    _ = ∫⁻ g, T.indicator F (iota g) ∂τ := by
        refine lintegral_congr fun g => ?_
        rw [← hpre]
        rfl
    _ = ∫⁻ g, T.indicator F g ∂(Measure.map (fun g : G => (iota g : G)) τ) :=
        (lintegral_map (hF.indicator hTm) (measurable_iota K)).symm
    _ = ∫⁻ g in T, F g ∂τ := by rw [map_iota_eq, lintegral_indicator hTm]

end Adelic

section TestFn

open scoped SchwartzMap Classical
open NumberField.AdelicFourier

variable (K : Type) [Field K] [NumberField K]

local notation "𝔸" => AdeleRing (𝓞 K) K

abbrev V2 : Type := Fin 2 → mixedEmbedding.mixedSpace K

def bump : ContDiffBump (0 : V2 K) := ⟨1, 2, one_pos, one_lt_two⟩

theorem hasCompactSupport_bumpC : HasCompactSupport (fun x : V2 K => ((bump K x : ℝ) : ℂ)) :=
  (bump K).hasCompactSupport.comp_left Complex.ofReal_zero

theorem contDiff_bumpC : ContDiff ℝ (⊤ : ℕ∞) (fun x : V2 K => ((bump K x : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (bump K).contDiff

def bumpS : 𝓢(V2 K, ℂ) := (hasCompactSupport_bumpC K).toSchwartzMap (contDiff_bumpC K)

theorem bumpS_apply (x : V2 K) : bumpS K x = ((bump K x : ℝ) : ℂ) := rfl

def intPairs : Set (Fin 2 → FiniteAdeleRing (𝓞 K) K) :=
  Set.univ.pi fun _ => NumberField.AdelicBox.integralFiniteAdeles (𝓞 K) K

theorem isOpen_intPairs : IsOpen (intPairs K) :=
  isOpen_set_pi Set.finite_univ fun _ _ => NumberField.AdelicBox.isOpen_integralFiniteAdeles K

theorem isCompact_intPairs : IsCompact (intPairs K) :=
  isCompact_univ_pi fun _ => NumberField.AdelicBox.isCompact_integralFiniteAdeles K

theorem zero_mem_intPairs : (0 : Fin 2 → FiniteAdeleRing (𝓞 K) K) ∈ intPairs K :=
  fun i _ v => (v.adicCompletionIntegers K).zero_mem

def finInd : (Fin 2 → FiniteAdeleRing (𝓞 K) K) → ℂ := (intPairs K).indicator 1

theorem isLocallyConstant_finInd : IsLocallyConstant (finInd K) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  by_cases hx : x ∈ intPairs K
  · refine ⟨intPairs K, isOpen_intPairs K, hx, fun y hy => ?_⟩
    simp only [finInd, Set.indicator_of_mem hx, Set.indicator_of_mem hy, Pi.one_apply]
  · refine ⟨(intPairs K)ᶜ, (isCompact_intPairs K).isClosed.isOpen_compl, hx, fun y hy => ?_⟩
    have hy' : y ∉ intPairs K := hy
    simp only [finInd, Set.indicator_of_notMem hx, Set.indicator_of_notMem hy']

theorem hasCompactSupport_finInd : HasCompactSupport (finInd K) :=
  HasCompactSupport.intro (isCompact_intPairs K) fun x hx => Set.indicator_of_notMem hx _

def Phi0 (x : Fin 2 → 𝔸) : ℂ :=
  bumpS K (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace K (x i).1) * finInd K (fun i => (x i).2)

theorem Phi0_mem : Phi0 K ∈ schwartzBruhat2 K :=
  mem_schwartzBruhat2_of_mem_pureTensorSet2
    (tensor_mem_pureTensorSet2 (bumpS K) (finInd K) (isLocallyConstant_finInd K) (hasCompactSupport_finInd K))

def u0 (x : Fin 2 → 𝔸) : ℝ := (Phi0 K x).re

theorem Phi0_eq_ofReal (x : Fin 2 → 𝔸) : Phi0 K x = ((u0 K x : ℝ) : ℂ) := by
  unfold u0 Phi0 finInd
  rw [bumpS_apply]
  by_cases hx : (fun i => (x i).2) ∈ intPairs K
  · rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one, Complex.ofReal_re]
  · rw [Set.indicator_of_notMem hx, mul_zero, Complex.zero_re, Complex.ofReal_zero]

theorem u0_nonneg (x : Fin 2 → 𝔸) : 0 ≤ u0 K x := by
  unfold u0 Phi0 finInd
  rw [bumpS_apply]
  by_cases hx : (fun i => (x i).2) ∈ intPairs K
  · rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one, Complex.ofReal_re]
    exact (bump K).nonneg
  · rw [Set.indicator_of_notMem hx, mul_zero, Complex.zero_re]

theorem norm_Phi0 (x : Fin 2 → 𝔸) : ‖Phi0 K x‖ = u0 K x := by
  rw [Phi0_eq_ofReal, Complex.norm_real, Real.norm_of_nonneg (u0_nonneg K x)]

theorem u0_zero : u0 K 0 = 1 := by
  unfold u0 Phi0 finInd
  rw [bumpS_apply]
  have h0 : (fun i : Fin 2 => ((0 : Fin 2 → 𝔸) i).2) = 0 := by funext i; rfl
  have h1 : (fun i : Fin 2 => InfiniteAdeleRing.ringEquiv_mixedSpace K ((0 : Fin 2 → 𝔸) i).1) = 0 := by
    funext i; exact map_zero _
  rw [h0, h1, Set.indicator_of_mem (zero_mem_intPairs K), Pi.one_apply, mul_one, Complex.ofReal_re]
  exact (bump K).one_of_mem_closedBall (by simp [(bump K).rIn_pos.le])

end TestFn

section Theta

open scoped Classical
open NumberField.AdelicFourier NumberField.StandardAddChar

variable (K : Type) [Field K] [NumberField K]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]

local notation "𝔸" => AdeleRing (𝓞 K) K
local notation "G" => GL (Fin 2) (AdeleRing (𝓞 K) K)

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdeleRing.secondCountableTopology NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo

abbrev NZ : Type := {ξ : Fin 2 → K // ξ ≠ 0}

scoped instance countable_NZ : Countable (NZ K) := by
  haveI : Countable K := (Module.finBasis ℚ K).equivFun.toEquiv.injective.countable
  exact Subtype.countable

def avec (ξ : NZ K) : Fin 2 → 𝔸 := fun i => algebraMap K 𝔸 (ξ.1 i)

def thetaE (f : (Fin 2 → 𝔸) → ℝ) (g : G) : ℝ≥0∞ :=
  ∑' ξ : NZ K, ENNReal.ofReal (f ((g : Matrix (Fin 2) (Fin 2) 𝔸).mulVec (avec K ξ)))

theorem measurable_thetaE {f : (Fin 2 → 𝔸) → ℝ} (hf : Measurable f) : Measurable (thetaE K f) := by
  unfold thetaE
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  exact Measurable.iSup fun s => s.measurable_fun_sum fun ξ _ =>
    ENNReal.measurable_ofReal.comp (hf.comp (measurable_mulVec K _))

def trGL (g : G) : G where
  val := (g : Matrix (Fin 2) (Fin 2) 𝔸).transpose
  inv := ((g⁻¹ : G) : Matrix (Fin 2) (Fin 2) 𝔸).transpose
  val_inv := by
    rw [← Matrix.transpose_mul, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel]
    simp
  inv_val := by
    rw [← Matrix.transpose_mul, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel]
    simp

theorem coe_trGL (g : G) : ((trGL K g : G) : Matrix (Fin 2) (Fin 2) 𝔸) = (g : Matrix (Fin 2) (Fin 2) 𝔸).transpose :=
  rfl

theorem det_trGL (g : G) : Matrix.GeneralLinearGroup.det (trGL K g) = Matrix.GeneralLinearGroup.det g := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, coe_trGL,
    Matrix.det_transpose]

theorem vecMul_trGL (g : G) (v : Fin 2 → 𝔸) :
    Matrix.vecMul v ((trGL K g : G) : Matrix (Fin 2) (Fin 2) 𝔸) = (g : Matrix (Fin 2) (Fin 2) 𝔸).mulVec v := by
  rw [coe_trGL, Matrix.vecMul_transpose]

theorem ideleNorm_one : NumberField.TateGlobal.ideleNorm K (1 : (𝔸)ˣ) = 1 := by
  unfold NumberField.TateGlobal.ideleNorm
  rw [map_one, NNReal.coe_one]

theorem summable_norm_mulVec {Φ : (Fin 2 → 𝔸) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 K) (g : G) :
    Summable fun ξ : NZ K => ‖Φ ((g : Matrix (Fin 2) (Fin 2) 𝔸).mulVec (avec K ξ))‖ := by
  obtain ⟨C, -, hC⟩ :=
    (NumberField.AdelicFourier.exists_forall_tsum_norm_apply_smul_vecMul_le_and_continuous_tsum_of_mem_schwartzBruhat2
      K hΦ).1 {trGL K g} isCompact_singleton 0
  have h := (hC (trGL K g) (Set.mem_singleton _) 1).1
  have h' : Summable fun ξ : Fin 2 → K => ‖Φ ((g : Matrix (Fin 2) (Fin 2) 𝔸).mulVec fun i => algebraMap K 𝔸 (ξ i))‖ := by
    refine h.congr fun ξ => ?_
    rw [Units.val_one, one_smul, vecMul_trGL]
  exact h'.subtype _

variable (μ₁ : Measure (AdeleRing (𝓞 K) K)) [μ₁.IsAddHaarMeasure]

def Pref : (Fin 2 → 𝔸) → ℂ := reflectPair (stdAddChar K) μ₁ (Phi0 K)

def pp (x : Fin 2 → 𝔸) : ℝ := max (Pref K μ₁ x).re 0
def pm (x : Fin 2 → 𝔸) : ℝ := max (-(Pref K μ₁ x).re) 0

theorem pp_nonneg (x : Fin 2 → 𝔸) : 0 ≤ pp K μ₁ x := le_max_right _ _
theorem pm_nonneg (x : Fin 2 → 𝔸) : 0 ≤ pm K μ₁ x := le_max_right _ _
theorem pp_sub_pm (x : Fin 2 → 𝔸) : pp K μ₁ x - pm K μ₁ x = (Pref K μ₁ x).re := by
  unfold pp pm
  rcases le_total 0 (Pref K μ₁ x).re with h | h
  · rw [max_eq_left h, max_eq_right (neg_nonpos.2 h), sub_zero]
  · rw [max_eq_right h, max_eq_left (neg_nonneg.2 h), zero_sub, neg_neg]
theorem pp_le_norm (x : Fin 2 → 𝔸) : pp K μ₁ x ≤ ‖Pref K μ₁ x‖ :=
  max_le ((le_abs_self _).trans (Complex.abs_re_le_norm _)) (norm_nonneg _)
theorem pm_le_norm (x : Fin 2 → 𝔸) : pm K μ₁ x ≤ ‖Pref K μ₁ x‖ :=
  max_le ((neg_le_abs _).trans (Complex.abs_re_le_norm _)) (norm_nonneg _)

theorem Pref_mem : Pref K μ₁ ∈ schwartzBruhat2 K :=
  (NumberField.AdelicFourier.fourierTransform2_mem_schwartzBruhat2_and_reflectPair_mem_schwartzBruhat2 K μ₁
    (isGlobalAddChar_stdAddChar K) (Phi0_mem K)).2

theorem continuous_Phi0 : Continuous (Phi0 K) :=
  (NumberField.AdelicFourier.continuous_integrable_comp_vecMul_mem_and_bottomRowVec_mem_schwartzBruhat_of_mem_schwartzBruhat2
    K _ (Phi0_mem K)).1

theorem continuous_Pref : Continuous (Pref K μ₁) :=
  (NumberField.AdelicFourier.continuous_integrable_comp_vecMul_mem_and_bottomRowVec_mem_schwartzBruhat_of_mem_schwartzBruhat2
    K _ (Pref_mem K μ₁)).1

theorem measurable_u0 : Measurable (u0 K) := (Complex.continuous_re.comp (continuous_Phi0 K)).measurable

theorem measurable_pp : Measurable (pp K μ₁) :=
  ((Complex.continuous_re.comp (continuous_Pref K μ₁)).max continuous_const).measurable

theorem measurable_pm : Measurable (pm K μ₁) :=
  ((Complex.continuous_re.comp (continuous_Pref K μ₁)).neg.max continuous_const).measurable

theorem integrable_Phi0 (μ : Measure 𝔸) [μ.IsAddHaarMeasure] : Integrable (Phi0 K) (Measure.pi fun _ : Fin 2 => μ) :=
  (NumberField.AdelicFourier.continuous_integrable_comp_vecMul_mem_and_bottomRowVec_mem_schwartzBruhat_of_mem_schwartzBruhat2
    K _ (Phi0_mem K)).2.2.2.1 μ

theorem integrable_Pref (μ : Measure 𝔸) [μ.IsAddHaarMeasure] : Integrable (Pref K μ₁) (Measure.pi fun _ : Fin 2 => μ) :=
  (NumberField.AdelicFourier.continuous_integrable_comp_vecMul_mem_and_bottomRowVec_mem_schwartzBruhat_of_mem_schwartzBruhat2
    K _ (Pref_mem K μ₁)).2.2.2.1 μ

theorem lintegral_u0_ne_top (μ : Measure 𝔸) [μ.IsAddHaarMeasure] :
    ∫⁻ x, ENNReal.ofReal (u0 K x) ∂(Measure.pi fun _ : Fin 2 => μ) ≠ ⊤ := by
  have h := (integrable_Phi0 K μ).hasFiniteIntegral
  refine ne_of_lt (lt_of_le_of_lt (le_of_eq (lintegral_congr fun x => ?_)) h)
  rw [← norm_Phi0, ofReal_norm]

theorem lintegral_le_norm_ne_top (μ : Measure 𝔸) [μ.IsAddHaarMeasure] {f : (Fin 2 → 𝔸) → ℝ}
    (hle : ∀ x, f x ≤ ‖Pref K μ₁ x‖) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂(Measure.pi fun _ : Fin 2 => μ) ≠ ⊤ := by
  have h := (integrable_Pref K μ₁ μ).hasFiniteIntegral
  refine ne_of_lt (lt_of_le_of_lt (lintegral_mono fun x => ?_) h)
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (hle x)

def I1 : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (u0 K x) ∂(Measure.pi fun _ : Fin 2 => μ₁)

theorem I1_ne_top : I1 K μ₁ ≠ ⊤ := lintegral_u0_ne_top K μ₁

theorem I1_ne_zero : I1 K μ₁ ≠ 0 := by

  have hc : Continuous (u0 K) := Complex.continuous_re.comp (continuous_Phi0 K)
  have hU : IsOpen {x : Fin 2 → 𝔸 | (1 / 2 : ℝ) < u0 K x} := isOpen_lt continuous_const hc
  have h0 : (0 : Fin 2 → 𝔸) ∈ {x : Fin 2 → 𝔸 | (1 / 2 : ℝ) < u0 K x} := by
    show (1 / 2 : ℝ) < u0 K 0
    rw [u0_zero]; norm_num
  have hpos : 0 < (Measure.pi fun _ : Fin 2 => μ₁) {x : Fin 2 → 𝔸 | (1 / 2 : ℝ) < u0 K x} :=
    hU.measure_pos _ ⟨0, h0⟩
  intro hzero
  have hle : ∫⁻ x in {x : Fin 2 → 𝔸 | (1 / 2 : ℝ) < u0 K x}, ENNReal.ofReal (1 / 2) ∂(Measure.pi fun _ : Fin 2 => μ₁) ≤
      I1 K μ₁ := by
    refine (setLIntegral_mono (ENNReal.measurable_ofReal.comp (measurable_u0 K)) fun x hx =>
      ENNReal.ofReal_le_ofReal (le_of_lt hx)).trans (setLIntegral_le_lintegral _ _)
  rw [hzero, setLIntegral_const, nonpos_iff_eq_zero, mul_eq_zero] at hle
  rcases hle with h | h
  · exact absurd h (by simp)
  · exact hpos.ne' h

theorem re_Pref_zero : (Pref K μ₁ 0).re = (I1 K μ₁).toReal := by
  have h0 : (![(0 : Fin 2 → 𝔸) 1, -(0 : Fin 2 → 𝔸) 0] : Fin 2 → 𝔸) = 0 := by
    funext i; fin_cases i <;> simp
  have h1 : Pref K μ₁ 0 = ∫ v, Phi0 K v ∂(Measure.pi fun _ : Fin 2 => μ₁) := by
    show fourierTransform2 (stdAddChar K) μ₁ (Phi0 K) ![(0 : Fin 2 → 𝔸) 1, -(0 : Fin 2 → 𝔸) 0] = _
    rw [h0, fourierTransform2, fourierIntegral_def]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    show pairChar (stdAddChar K) (-(v * 0)) * Phi0 K v = Phi0 K v
    rw [mul_zero, neg_zero, AddChar.map_zero_eq_one, one_mul]
  have h2 : ∫ v, Phi0 K v ∂(Measure.pi fun _ : Fin 2 => μ₁) = ((∫ v, u0 K v ∂(Measure.pi fun _ : Fin 2 => μ₁) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    exact integral_congr_ae (Filter.Eventually.of_forall fun v => Phi0_eq_ofReal K v)
  rw [h1, h2, Complex.ofReal_re, I1,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun v => u0_nonneg K v)
      (measurable_u0 K).aestronglyMeasurable]

theorem theta_identity (hμ₁ : μ₁ (NumberField.AdelicBox.adelicBox K) = 1) (g : G) :
    thetaE K (u0 K) g + 1 + ENNReal.ofReal (Ndet K g)⁻¹ * thetaE K (pm K μ₁) (iota g) =
      ENNReal.ofReal (Ndet K g)⁻¹ * thetaE K (pp K μ₁) (iota g) + ENNReal.ofReal (Ndet K g)⁻¹ * I1 K μ₁ := by
  have hcard := NumberField.AdelicFourier.tsum_apply_smul_vecMul_add_eq_ideleNorm_cpow_neg_two_mul_tsum_reflectPair_of_mem_schwartzBruhat2
    K μ₁ hμ₁ (isGlobalAddChar_stdAddChar K) (Phi0_mem K) (trGL K g) 1

  have eL : (∑' ξ : NZ K, Phi0 K (((1 : (𝔸)ˣ) : 𝔸) •
      Matrix.vecMul (fun i => algebraMap K 𝔸 (ξ.1 i)) ((trGL K g : G) : Matrix (Fin 2) (Fin 2) 𝔸))) =
      ∑' ξ : NZ K, Phi0 K ((g : Matrix (Fin 2) (Fin 2) 𝔸).mulVec (avec K ξ)) :=
    tsum_congr fun ξ => by rw [Units.val_one, one_smul, vecMul_trGL]; rfl
  have eR : (∑' ξ : NZ K, reflectPair (stdAddChar K) μ₁ (Phi0 K)
      ((((1 : (𝔸)ˣ)⁻¹ * (Matrix.GeneralLinearGroup.det (trGL K g))⁻¹ : (𝔸)ˣ) : 𝔸) •
        Matrix.vecMul (fun i => algebraMap K 𝔸 (ξ.1 i)) ((trGL K g : G) : Matrix (Fin 2) (Fin 2) 𝔸))) =
      ∑' ξ : NZ K, Pref K μ₁ (((iota g : G) : Matrix (Fin 2) (Fin 2) 𝔸).mulVec (avec K ξ)) :=
    tsum_congr fun ξ => by rw [inv_one, one_mul, det_trGL, vecMul_trGL, ← iota_mulVec]; rfl
  have eN : NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (trGL K g)) = Ndet K g := by
    rw [det_trGL]
  have e1 : (((NumberField.TateGlobal.ideleNorm K (1 : (𝔸)ˣ) : ℝ) : ℂ)) ^ (-(2 : ℂ)) = 1 := by
    rw [ideleNorm_one, Complex.ofReal_one, Complex.one_cpow]
  rw [eL, eR, eN, e1, one_mul] at hcard

  have hsΦ : Summable fun ξ : NZ K => Phi0 K ((g : Matrix (Fin 2) (Fin 2) 𝔸).mulVec (avec K ξ)) :=
    (summable_norm_mulVec K (Phi0_mem K) g).of_norm
  have hsPn := summable_norm_mulVec K (Pref_mem K μ₁) (iota g)
  have hsP : Summable fun ξ : NZ K => Pref K μ₁ (((iota g : G) : Matrix (Fin 2) (Fin 2) 𝔸).mulVec (avec K ξ)) :=
    hsPn.of_norm
  have hspp : Summable fun ξ : NZ K => pp K μ₁ (((iota g : G) : Matrix (Fin 2) (Fin 2) 𝔸).mulVec (avec K ξ)) :=
    Summable.of_nonneg_of_le (fun ξ => pp_nonneg K μ₁ _) (fun ξ => pp_le_norm K μ₁ _) hsPn
  have hspm : Summable fun ξ : NZ K => pm K μ₁ (((iota g : G) : Matrix (Fin 2) (Fin 2) 𝔸).mulVec (avec K ξ)) :=
    Summable.of_nonneg_of_le (fun ξ => pm_nonneg K μ₁ _) (fun ξ => pm_le_norm K μ₁ _) hsPn
  have hsu : Summable fun ξ : NZ K => u0 K ((g : Matrix (Fin 2) (Fin 2) 𝔸).mulVec (avec K ξ)) := by
    refine (summable_norm_mulVec K (Phi0_mem K) g).congr fun ξ => ?_
    exact norm_Phi0 K _

  have hre := congrArg Complex.re hcard
  rw [Complex.add_re, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.re_tsum hsΦ,
    Complex.re_tsum hsP, show reflectPair (stdAddChar K) μ₁ (Phi0 K) 0 = Pref K μ₁ 0 from rfl, re_Pref_zero] at hre
  have hu : (fun ξ : NZ K => (Phi0 K ((g : Matrix (Fin 2) (Fin 2) 𝔸).mulVec (avec K ξ))).re) =
      fun ξ : NZ K => u0 K ((g : Matrix (Fin 2) (Fin 2) 𝔸).mulVec (avec K ξ)) := rfl
  have hP : (fun ξ : NZ K => (Pref K μ₁ (((iota g : G) : Matrix (Fin 2) (Fin 2) 𝔸).mulVec (avec K ξ))).re) =
      fun ξ : NZ K => pp K μ₁ (((iota g : G) : Matrix (Fin 2) (Fin 2) 𝔸).mulVec (avec K ξ)) -
        pm K μ₁ (((iota g : G) : Matrix (Fin 2) (Fin 2) 𝔸).mulVec (avec K ξ)) := by
    funext ξ; rw [pp_sub_pm]
  have h00 : (Phi0 K 0).re = 1 := u0_zero K
  rw [hu, hP, hspp.tsum_sub hspm, h00] at hre

  set A := ∑' ξ : NZ K, u0 K ((g : Matrix (Fin 2) (Fin 2) 𝔸).mulVec (avec K ξ)) with hA
  set Up := ∑' ξ : NZ K, pp K μ₁ (((iota g : G) : Matrix (Fin 2) (Fin 2) 𝔸).mulVec (avec K ξ)) with hUp
  set Um := ∑' ξ : NZ K, pm K μ₁ (((iota g : G) : Matrix (Fin 2) (Fin 2) 𝔸).mulVec (avec K ξ)) with hUm
  set N := Ndet K g with hN
  have key : A + 1 + N⁻¹ * Um = N⁻¹ * Up + N⁻¹ * (I1 K μ₁).toReal := by linear_combination hre
  have hA0 : 0 ≤ A := tsum_nonneg fun ξ => u0_nonneg K _
  have hUp0 : 0 ≤ Up := tsum_nonneg fun ξ => pp_nonneg K μ₁ _
  have hUm0 : 0 ≤ Um := tsum_nonneg fun ξ => pm_nonneg K μ₁ _
  have hN0 : 0 ≤ N⁻¹ := inv_nonneg.2 (Ndet_pos K g).le

  have tA : thetaE K (u0 K) g = ENNReal.ofReal A := by
    rw [hA, ENNReal.ofReal_tsum_of_nonneg (fun ξ => u0_nonneg K _) hsu]; rfl
  have tp : thetaE K (pp K μ₁) (iota g) = ENNReal.ofReal Up := by
    rw [hUp, ENNReal.ofReal_tsum_of_nonneg (fun ξ => pp_nonneg K μ₁ _) hspp]; rfl
  have tm : thetaE K (pm K μ₁) (iota g) = ENNReal.ofReal Um := by
    rw [hUm, ENNReal.ofReal_tsum_of_nonneg (fun ξ => pm_nonneg K μ₁ _) hspm]; rfl
  calc thetaE K (u0 K) g + 1 + ENNReal.ofReal N⁻¹ * thetaE K (pm K μ₁) (iota g)
      = ENNReal.ofReal (A + 1 + N⁻¹ * Um) := by
        rw [tA, tm, ← ENNReal.ofReal_one, ← ENNReal.ofReal_mul hN0, ← ENNReal.ofReal_add hA0 zero_le_one,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ = ENNReal.ofReal (N⁻¹ * Up + N⁻¹ * (I1 K μ₁).toReal) := by rw [key]
    _ = ENNReal.ofReal N⁻¹ * thetaE K (pp K μ₁) (iota g) + ENNReal.ofReal N⁻¹ * I1 K μ₁ := by
        rw [tp, ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hN0, ENNReal.ofReal_mul hN0,
          ENNReal.ofReal_toReal (I1_ne_top K μ₁)]

end Theta

section Assembly

open scoped Classical
open NumberField.AdelicFourier NumberField.StandardAddChar

variable (K : Type) [Field K] [NumberField K]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]

local notation "𝔸" => AdeleRing (𝓞 K) K
local notation "G" => GL (Fin 2) (AdeleRing (𝓞 K) K)

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdeleRing.secondCountableTopology NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo

def IE (μ : Measure 𝔸) (f : (Fin 2 → 𝔸) → ℝ) : ℝ≥0∞ := ∫⁻ c, ENNReal.ofReal (f c) ∂(Measure.pi fun _ : Fin 2 => μ)

def FibreHyp (τ : Measure G) (μ : Measure 𝔸) (ν : Measure (𝔸)ˣ) (κ : ℝ≥0∞) : Prop :=
  ∀ (w : G → ℝ≥0∞) (Ψ : (Fin 2 → 𝔸) × (𝔸)ˣ → ℝ≥0∞),
    Measurable w → Measurable Ψ →
    (∀ᵐ g ∂τ, ∫⁻ x, w (g * unipotentGL2 x) ∂μ = 1) →
    ∫⁻ g, w g * Ψ (fun i => (g : Matrix (Fin 2) (Fin 2) 𝔸) i 0, Matrix.GeneralLinearGroup.det g) ∂τ =
      κ * ∫⁻ c, ∫⁻ δ, Ψ (c, δ) * ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K δ)⁻¹ ∂ν
        ∂(Measure.pi fun _ : Fin 2 => μ)

def RateHyp (τ : Measure G) (C : ℝ≥0∞) : Prop :=
  ∀ D : Set G, IsFundamentalDomain ((globalPoints (𝓞 K) K).range).op D τ →
    ∀ a b : ℝ, 0 < a → a ≤ b →
      τ (D ∩ {t | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det t) ∈ Set.Icc a b}) =
        C * ENNReal.ofReal (Real.log (b / a))

def RateHypI (ν : Measure (𝔸)ˣ) (CI : ℝ≥0∞) : Prop :=
  ∀ Ω : Set (𝔸)ˣ, IsFundamentalDomain (Units.map (algebraMap K 𝔸 : K →* 𝔸)).range Ω ν →
    ∀ a b : ℝ, 0 < a → a ≤ b →
      ν (Ω ∩ {x | NumberField.TateGlobal.ideleNorm K x ∈ Set.Icc a b}) = CI * ENNReal.ofReal (Real.log (b / a))

variable {K}

theorem idelic_indicator (ν : Measure (𝔸)ˣ) (CI : ℝ≥0∞) (hCI : CI ≠ ⊤) (hrateI : RateHypI K ν CI)
    {Ω : Set (𝔸)ˣ} (hΩ : IsFundamentalDomain (Units.map (algebraMap K 𝔸 : K →* 𝔸)).range Ω ν)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫⁻ δ in Ω, (Set.Icc a b).indicator (1 : ℝ → ℝ≥0∞) (NumberField.TateGlobal.ideleNorm K δ) *
        ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K δ)⁻¹ ∂ν = CI * ENNReal.ofReal (a⁻¹ - b⁻¹) := by
  rw [← setLIntegral_inter_setOf_mem_eq (measurable_ideleNorm K) (Set.Icc a b) measurableSet_Icc]
  exact setLIntegral_ofReal_inv_eq_of_forall_measure_inter_Icc ν Ω _ (measurable_ideleNorm K)
    NumberField.TateGlobal.ideleNorm_pos CI hCI (hrateI Ω hΩ) ha hab

theorem idelic_indicator_mul (ν : Measure (𝔸)ˣ) (CI : ℝ≥0∞) (hrateI : RateHypI K ν CI)
    {Ω : Set (𝔸)ˣ} (hΩ : IsFundamentalDomain (Units.map (algebraMap K 𝔸 : K →* 𝔸)).range Ω ν)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫⁻ δ in Ω, ((Set.Icc b⁻¹ a⁻¹).indicator (1 : ℝ → ℝ≥0∞) (NumberField.TateGlobal.ideleNorm K δ) *
        ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K δ)) *
        ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K δ)⁻¹ ∂ν = CI * ENNReal.ofReal (Real.log (b / a)) := by
  have hb : 0 < b := ha.trans_le hab
  have h1 : ∀ δ : (𝔸)ˣ, ((Set.Icc b⁻¹ a⁻¹).indicator (1 : ℝ → ℝ≥0∞) (NumberField.TateGlobal.ideleNorm K δ) *
      ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K δ)) *
      ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K δ)⁻¹ =
      (Set.Icc b⁻¹ a⁻¹).indicator (1 : ℝ → ℝ≥0∞) (NumberField.TateGlobal.ideleNorm K δ) * 1 := fun δ => by
    have hp := NumberField.TateGlobal.ideleNorm_pos δ
    rw [mul_assoc, ← ENNReal.ofReal_mul hp.le, mul_inv_cancel₀ hp.ne', ENNReal.ofReal_one]
  simp_rw [h1]
  rw [← setLIntegral_inter_setOf_mem_eq (measurable_ideleNorm K) (Set.Icc b⁻¹ a⁻¹) measurableSet_Icc (fun _ => 1),
    setLIntegral_one, hrateI Ω hΩ b⁻¹ a⁻¹ (inv_pos.2 hb) (inv_anti₀ ha hab), inv_div_inv]

theorem main
    (τ : Measure G) [τ.IsHaarMeasure] [τ.IsMulRightInvariant]
    (μ : Measure 𝔸) [μ.IsAddHaarMeasure] (ν : Measure (𝔸)ˣ)
    (κ : ℝ≥0∞) (hκ : κ ≠ ⊤) (hfib : FibreHyp K τ μ ν κ)
    (C : ℝ≥0∞) (hC : C ≠ ⊤) (hrate : RateHyp K τ C)
    {D₀ : Set G} (hD₀m : MeasurableSet D₀) (hD₀ : IsFundamentalDomain ((globalPoints (𝓞 K) K).range).op D₀ τ)
    (CI : ℝ≥0∞) (hCI : CI ≠ ⊤) (hrateI : RateHypI K ν CI)
    {Ω₀ : Set (𝔸)ˣ} (hΩ₀m : MeasurableSet Ω₀)
    (hΩ₀ : IsFundamentalDomain (Units.map (algebraMap K 𝔸 : K →* 𝔸)).range Ω₀ ν)
    {B : Set 𝔸} (hB : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 K) K) B μ)
    (hB0 : μ B ≠ 0) (hBt : μ B ≠ ⊤)
    (μ₁ : Measure 𝔸) [μ₁.IsAddHaarMeasure] (hμ₁ : μ₁ (NumberField.AdelicBox.adelicBox K) = 1)
    (c : ℝ≥0∞) (hμμ₁ : μ = c • μ₁) (hcB : μ B = c) :
    C = κ * CI * μ B ^ 3 := by

  have hUf : ∀ (D : Set G), MeasurableSet D → IsFundamentalDomain ((globalPoints (𝓞 K) K).range).op D τ →
      ∀ (f : (Fin 2 → 𝔸) → ℝ), Measurable f → ∀ (h : ℝ → ℝ≥0∞), Measurable h →
      ∫⁻ g in D, h (Ndet K g) * thetaE K f g ∂τ =
        κ * μ B * IE K μ f * ∫⁻ δ in Ω₀, h (NumberField.TateGlobal.ideleNorm K δ) *
          ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K δ)⁻¹ ∂ν :=
    fun D hDm hD f hf h hh =>
      AutomorphicForm.setLIntegral_mul_tsum_apply_mulVec_eq_mul_measure_mul_lintegral_mul_setLIntegral_of_isFundamentalDomain_op
        K τ inferInstance inferInstance μ inferInstance ν κ hfib D hDm hD Ω₀ hΩ₀m hΩ₀ B hB
        (fun x => ENNReal.ofReal (f x)) (ENNReal.measurable_ofReal.comp hf) h hh

  set Dι : Set G := (fun g : G => (iota g : G)) ⁻¹' D₀ with hDι_def
  have hDιm : MeasurableSet Dι := measurableSet_preimage_iota K hD₀m
  have hDι : IsFundamentalDomain ((globalPoints (𝓞 K) K).range).op Dι τ := isFundamentalDomain_preimage_iota K τ hD₀

  have hIu : IE K μ (u0 K) ≠ ⊤ := lintegral_u0_ne_top K μ
  have hIp : IE K μ (pp K μ₁) ≠ ⊤ := lintegral_le_norm_ne_top K μ₁ μ (pp_le_norm K μ₁)
  have hIm : IE K μ (pm K μ₁) ≠ ⊤ := lintegral_le_norm_ne_top K μ₁ μ (pm_le_norm K μ₁)

  set P1 : ℝ≥0∞ := κ * μ B * IE K μ (u0 K) * CI with hP1
  set P3 : ℝ≥0∞ := κ * μ B * IE K μ (pm K μ₁) * CI with hP3
  set P4 : ℝ≥0∞ := κ * μ B * IE K μ (pp K μ₁) * CI with hP4
  set P5 : ℝ≥0∞ := I1 K μ₁ * C with hP5
  have hP1t : P1 ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top hκ hBt) hIu) hCI
  have hP3t : P3 ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top hκ hBt) hIm) hCI
  have hP4t : P4 ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top hκ hBt) hIp) hCI
  have hP5t : P5 ≠ ⊤ := ENNReal.mul_ne_top (I1_ne_top K μ₁) hC
  clear_value P1 P3 P4 P5

  have hInt : ∀ a b : ℝ, 0 < a → a ≤ b →
      P1 * ENNReal.ofReal (a⁻¹ - b⁻¹) + C * ENNReal.ofReal (Real.log (b / a)) + P3 * ENNReal.ofReal (Real.log (b / a)) =
        P4 * ENNReal.ofReal (Real.log (b / a)) + P5 * ENNReal.ofReal (a⁻¹ - b⁻¹) := by
    intro a b ha hab
    have hb : 0 < b := ha.trans_le hab
    set S : Set G := D₀ ∩ slab K a b with hS

    have mθu : Measurable (thetaE K (u0 K)) := measurable_thetaE K (measurable_u0 K)
    have mθp : Measurable fun g : G => thetaE K (pp K μ₁) (iota g) :=
      (measurable_thetaE K (measurable_pp K μ₁)).comp (measurable_iota K)
    have mθm : Measurable fun g : G => thetaE K (pm K μ₁) (iota g) :=
      (measurable_thetaE K (measurable_pm K μ₁)).comp (measurable_iota K)
    have mNi : Measurable fun g : G => ENNReal.ofReal (Ndet K g)⁻¹ :=
      ENNReal.measurable_ofReal.comp (measurable_Ndet K).inv

    have hI : ∫⁻ g in S, (thetaE K (u0 K) g + 1 + ENNReal.ofReal (Ndet K g)⁻¹ * thetaE K (pm K μ₁) (iota g)) ∂τ =
        ∫⁻ g in S, (ENNReal.ofReal (Ndet K g)⁻¹ * thetaE K (pp K μ₁) (iota g) +
          ENNReal.ofReal (Ndet K g)⁻¹ * I1 K μ₁) ∂τ :=
      lintegral_congr fun g => theta_identity K μ₁ hμ₁ g
    rw [lintegral_add_left (f := fun g => thetaE K (u0 K) g + 1) (mθu.add measurable_const),
      lintegral_add_left mθu] at hI
    erw [lintegral_add_left (mNi.mul mθp)] at hI

    have hT1 : ∫⁻ g in S, thetaE K (u0 K) g ∂τ = P1 * ENNReal.ofReal (a⁻¹ - b⁻¹) := by
      rw [hS, slab, setLIntegral_inter_setOf_mem_eq (measurable_Ndet K) (Set.Icc a b) measurableSet_Icc,
        hUf D₀ hD₀m hD₀ (u0 K) (measurable_u0 K) _ (measurable_one.indicator measurableSet_Icc),
        idelic_indicator ν CI hCI hrateI hΩ₀ ha hab, hP1]
      ring

    have hT2 : ∫⁻ g in S, (1 : ℝ≥0∞) ∂τ = C * ENNReal.ofReal (Real.log (b / a)) := by
      rw [setLIntegral_one, hS]
      exact hrate D₀ hD₀ a b ha hab

    have hT34 : ∀ (f : (Fin 2 → 𝔸) → ℝ) (hf : Measurable f),
        ∫⁻ g in S, ENNReal.ofReal (Ndet K g)⁻¹ * thetaE K f (iota g) ∂τ =
          κ * μ B * IE K μ f * CI * ENNReal.ofReal (Real.log (b / a)) := by
      intro f hf
      have mF : Measurable fun g : G => ENNReal.ofReal (Ndet K g) * thetaE K f g :=
        (ENNReal.measurable_ofReal.comp (measurable_Ndet K)).mul (measurable_thetaE K hf)
      calc ∫⁻ g in S, ENNReal.ofReal (Ndet K g)⁻¹ * thetaE K f (iota g) ∂τ
          = ∫⁻ g in S, (fun g' : G => ENNReal.ofReal (Ndet K g') * thetaE K f g') (iota g) ∂τ := by
            refine lintegral_congr fun g => ?_
            show _ = ENNReal.ofReal (Ndet K (iota g)) * thetaE K f (iota g)
            rw [Ndet_iota]
        _ = ∫⁻ g in Dι ∩ slab K b⁻¹ a⁻¹, ENNReal.ofReal (Ndet K g) * thetaE K f g ∂τ :=
            setLIntegral_comp_iota K τ hD₀m ha hb _ mF
        _ = ∫⁻ g in Dι, ((Set.Icc b⁻¹ a⁻¹).indicator (1 : ℝ → ℝ≥0∞) (Ndet K g) * ENNReal.ofReal (Ndet K g)) *
              thetaE K f g ∂τ := by
            rw [slab, setLIntegral_inter_setOf_mem_eq (measurable_Ndet K) (Set.Icc b⁻¹ a⁻¹) measurableSet_Icc]
            simp only [mul_assoc]
        _ = κ * μ B * IE K μ f * ∫⁻ δ in Ω₀, ((Set.Icc b⁻¹ a⁻¹).indicator (1 : ℝ → ℝ≥0∞)
              (NumberField.TateGlobal.ideleNorm K δ) * ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K δ)) *
              ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K δ)⁻¹ ∂ν :=
            hUf Dι hDιm hDι f hf (fun r => (Set.Icc b⁻¹ a⁻¹).indicator (1 : ℝ → ℝ≥0∞) r * ENNReal.ofReal r)
              ((measurable_one.indicator measurableSet_Icc).mul ENNReal.measurable_ofReal)
        _ = κ * μ B * IE K μ f * CI * ENNReal.ofReal (Real.log (b / a)) := by
            rw [idelic_indicator_mul ν CI hrateI hΩ₀ ha hab]
            ring
    have hT3 := hT34 (pm K μ₁) (measurable_pm K μ₁)
    have hT4 := hT34 (pp K μ₁) (measurable_pp K μ₁)

    have hT5 : ∫⁻ g in S, ENNReal.ofReal (Ndet K g)⁻¹ * I1 K μ₁ ∂τ = P5 * ENNReal.ofReal (a⁻¹ - b⁻¹) := by
      rw [lintegral_mul_const _ mNi, hS, slab,
        setLIntegral_ofReal_inv_eq_of_forall_measure_inter_Icc τ D₀ (Ndet K) (measurable_Ndet K) (Ndet_pos K) C hC
          (hrate D₀ hD₀) ha hab, hP5]
      ring
    simp only [Pi.mul_apply] at hI
    rw [hT1, hT2, hT3, hT4, hT5] at hI
    rw [hP3, hP4]
    exact hI

  have hR : ∀ b : ℝ, 1 ≤ b →
      P1.toReal * (1 - b⁻¹) + C.toReal * Real.log b + P3.toReal * Real.log b =
        P4.toReal * Real.log b + P5.toReal * (1 - b⁻¹) := by
    intro b hb
    have h := congrArg ENNReal.toReal (hInt 1 b one_pos hb)
    have hu : 0 ≤ (1 : ℝ)⁻¹ - b⁻¹ := by
      rw [inv_one, sub_nonneg]; exact inv_le_one_of_one_le₀ hb
    have hL : 0 ≤ Real.log (b / 1) := by rw [div_one]; exact Real.log_nonneg hb
    rw [ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hP1t ENNReal.ofReal_ne_top,
        ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top⟩) (ENNReal.mul_ne_top hP3t ENNReal.ofReal_ne_top),
      ENNReal.toReal_add (ENNReal.mul_ne_top hP1t ENNReal.ofReal_ne_top) (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top),
      ENNReal.toReal_add (ENNReal.mul_ne_top hP4t ENNReal.ofReal_ne_top) (ENNReal.mul_ne_top hP5t ENNReal.ofReal_ne_top),
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hu, ENNReal.toReal_ofReal hL, div_one, inv_one] at h
    exact h
  have h2 := hR 2 (by norm_num)
  have h4 := hR 4 (by norm_num)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [hlog4] at h4
  have hP15 : P1.toReal = P5.toReal := by linear_combination 8 * h2 - 4 * h4
  have hE : P1 = P5 := (ENNReal.toReal_eq_toReal_iff' hP1t hP5t).1 hP15

  have hpi : (Measure.pi fun _ : Fin 2 => μ) = (c ^ 2) • Measure.pi fun _ : Fin 2 => μ₁ := by
    refine Measure.pi_eq fun s hs => ?_
    have e : ∀ t : Set 𝔸, μ t = c * μ₁ t := fun t => by rw [hμμ₁, Measure.smul_apply, smul_eq_mul]
    rw [Measure.smul_apply, smul_eq_mul, Measure.pi_pi, Fin.prod_univ_two, Fin.prod_univ_two, e, e]
    ring
  have hIE : IE K μ (u0 K) = μ B ^ 2 * I1 K μ₁ := by
    show ∫⁻ x, ENNReal.ofReal (u0 K x) ∂(Measure.pi fun _ : Fin 2 => μ) = μ B ^ 2 * I1 K μ₁
    rw [hpi, lintegral_smul_measure, smul_eq_mul, hcB]
    rfl
  rw [hP1, hP5, hIE] at hE
  have hE' : I1 K μ₁ * C = I1 K μ₁ * (κ * CI * μ B ^ 3) := by
    rw [← hE]; ring
  exact (ENNReal.mul_right_inj (I1_ne_zero K μ₁) (I1_ne_top K μ₁)).1 hE'

end Assembly

end AutomorphicForm.WeilCovolume
p2m_reactivate "P2MW.S_AutomorphicForm_rate_eq_mul_rate_mul_measure_pow_three_of_forall_lintegral_mul_apply_col_det_eq_mul_lintegral_of_forall_isFundamentalDomain_op_inter_ideleNorm_det_Icc.AutomorphicForm P2MW.S_AutomorphicForm_rate_eq_mul_rate_mul_measure_pow_three_of_forall_lintegral_mul_apply_col_det_eq_mul_lintegral_of_forall_isFundamentalDomain_op_inter_ideleNorm_det_Icc.AutomorphicForm.WeilCovolume"
p2m_reactivate "P2MW.S_AutomorphicForm_rate_eq_mul_rate_mul_measure_pow_three_of_forall_lintegral_mul_apply_col_det_eq_mul_lintegral_of_forall_isFundamentalDomain_op_inter_ideleNorm_det_Icc.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_rate_eq_mul_rate_mul_measure_pow_three_of_forall_lintegral_mul_apply_col_det_eq_mul_lintegral_of_forall_isFundamentalDomain_op_inter_ideleNorm_det_Icc.AutomorphicForm P2MW.S_AutomorphicForm_rate_eq_mul_rate_mul_measure_pow_three_of_forall_lintegral_mul_apply_col_det_eq_mul_lintegral_of_forall_isFundamentalDomain_op_inter_ideleNorm_det_Icc.AutomorphicForm.WeilCovolume"

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm.WeilCovolume in
theorem solution
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (τ : Measure (GL (Fin 2) (AdeleRing (𝓞 K) K))) (hτ : τ.IsHaarMeasure) (hτr : τ.IsMulRightInvariant)
    (μ : Measure (AdeleRing (𝓞 K) K)) (hμ : μ.IsAddHaarMeasure)
    (ν : Measure (AdeleRing (𝓞 K) K)ˣ) (hν : ν.IsHaarMeasure)

    (κ : ENNReal) (hκ : κ ≠ ⊤)
    (hfib : ∀ (w : GL (Fin 2) (AdeleRing (𝓞 K) K) → ENNReal)
        (Ψ : (Fin 2 → AdeleRing (𝓞 K) K) × (AdeleRing (𝓞 K) K)ˣ → ENNReal),
        Measurable w → Measurable Ψ →
        (∀ᵐ g ∂τ, ∫⁻ x, w (g * AutomorphicForm.unipotentGL2 x) ∂μ = 1) →
        ∫⁻ g, w g * Ψ (fun i => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i 0,
            Matrix.GeneralLinearGroup.det g) ∂τ =
          κ * ∫⁻ c, ∫⁻ δ, Ψ (c, δ) * ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K δ)⁻¹ ∂ν
            ∂(Measure.pi fun _ : Fin 2 => μ))

    (C : ENNReal) (hC : C ≠ ⊤)
    (hrate : ∀ D : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)),
      IsFundamentalDomain ((AutomorphicForm.globalPoints (𝓞 K) K).range).op D τ →
      ∀ a b : ℝ, 0 < a → a ≤ b →
        τ (D ∩ {t | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det t) ∈ Set.Icc a b}) =
          C * ENNReal.ofReal (Real.log (b / a)))
    (D₀ : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))) (hD₀m : MeasurableSet D₀)
    (hD₀ : IsFundamentalDomain ((AutomorphicForm.globalPoints (𝓞 K) K).range).op D₀ τ)

    (CI : ENNReal) (hCI : CI ≠ ⊤)
    (hrateI : ∀ Ω : Set (AdeleRing (𝓞 K) K)ˣ,
      IsFundamentalDomain
        (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range Ω ν →
      ∀ a b : ℝ, 0 < a → a ≤ b →
        ν (Ω ∩ {x | NumberField.TateGlobal.ideleNorm K x ∈ Set.Icc a b}) =
          CI * ENNReal.ofReal (Real.log (b / a)))
    (Ω₀ : Set (AdeleRing (𝓞 K) K)ˣ) (hΩ₀m : MeasurableSet Ω₀)
    (hΩ₀ : IsFundamentalDomain
        (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range Ω₀ ν)

    (B : Set (AdeleRing (𝓞 K) K)) (hBm : MeasurableSet B)
    (hB : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 K) K) B μ) :
    C = κ * CI * μ B ^ 3 := by

  obtain rfl : ‹MeasurableSpace (AdeleRing (𝓞 K) K)› = borel _ := BorelSpace.measurable_eq
  letI : MeasurableSpace (AdeleRing (𝓞 K) K) := borel _
  haveI : BorelSpace (AdeleRing (𝓞 K) K) := ⟨rfl⟩
  haveI := hτ
  haveI := hτr
  haveI := hμ
  haveI : Countable K := (Module.finBasis ℚ K).equivFun.toEquiv.injective.countable
  let e : K → ↥(AdeleRing.principalSubgroup (𝓞 K) K) := fun k => ⟨algebraMap K _ k, ⟨k, rfl⟩⟩
  have he : Function.Surjective e := fun x => by
    obtain ⟨k, hk⟩ := x.2
    exact ⟨k, Subtype.ext hk⟩
  haveI : Countable ↥(AdeleRing.principalSubgroup (𝓞 K) K) := he.countable
  have hbox : μ B = μ (NumberField.AdelicBox.adelicBox K) :=
    hB.measure_eq (NumberField.AdelicBox.isAddFundamentalDomain_adelicBox K μ)
  have hB0 : μ B ≠ 0 := by
    rw [hbox]; exact (NumberField.AdelicBox.measure_adelicBox_pos K μ).ne'
  have hBt : μ B ≠ ⊤ := by
    rw [hbox]; exact (NumberField.AdelicBox.measure_adelicBox_lt_top K μ).ne

  obtain ⟨μ₁, hμ₁H, hμ₁⟩ := NumberField.AdelicBox.exists_isAddHaarMeasure_adelicBox_eq_one K
  haveI := hμ₁H
  obtain ⟨c, -, hμμ₁⟩ := NumberField.AdelicFourier.exists_smul_eq_of_isAddHaarMeasure_adeleRing K μ μ₁
  have hμμ₁' : μ = (c : ENNReal) • μ₁ := by
    rw [hμμ₁]
    exact Measure.ext fun s _ => by rw [Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  have hcB : μ B = (c : ENNReal) := by
    rw [hbox, hμμ₁', Measure.smul_apply, smul_eq_mul, hμ₁, mul_one]
  exact main τ μ ν κ hκ hfib C hC hrate hD₀m hD₀ CI hCI hrateI hΩ₀m hΩ₀ hB hB0 hBt μ₁ hμ₁ c hμμ₁' hcB

end S_AutomorphicForm_rate_eq_mul_rate_mul_measure_pow_three_of_forall_lintegral_mul_apply_col_det_eq_mul_lintegral_of_forall_isFundamentalDomain_op_inter_ideleNorm_det_Icc
end P2MW
export P2MW.S_AutomorphicForm_rate_eq_mul_rate_mul_measure_pow_three_of_forall_lintegral_mul_apply_col_det_eq_mul_lintegral_of_forall_isFundamentalDomain_op_inter_ideleNorm_det_Icc (solution)
