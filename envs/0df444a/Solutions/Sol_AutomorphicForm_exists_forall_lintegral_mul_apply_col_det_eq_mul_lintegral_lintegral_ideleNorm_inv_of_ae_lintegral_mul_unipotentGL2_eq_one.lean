-- Prove2me | solution 1 for AutomorphicForm.exists_forall_lintegral_mul_apply_col_det_eq_mul_lintegral_lintegral_ideleNorm_inv_of_ae_lintegral_mul_unipotentGL2_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/0470a73e-8ff9-5799-b00c-456d54c8d66f

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_AutomorphicForm_exists_forall_lintegral_eq_mul_lintegral_mul_apply_col_det_of_forall_map_mulVec_eq_self
import Theorems.Thm_AutomorphicForm_exists_measurable_forall_lintegral_mul_unipotentGL2_eq_one
import Theorems.Thm_MeasureTheory_lintegral_mul_eq_lintegral_mul_of_forall_mul_eq_of_ae_lintegral_comp_mul_eq_one
import Theorems.Thm_NumberField_AdeleRing_map_mulVec_det_mul_pi_prod_withDensity_ideleNorm_inv_eq_self
import Theorems.Thm_NumberField_AdeleRing_pi_measure_setOf_not_exists_apply_col_eq_eq_zero
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_lintegral_mul_apply_col_det_eq_mul_lintegral_lintegral_ideleNorm_inv_of_ae_lintegral_mul_unipotentGL2_eq_one
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.cpowChar_apply_val ContinuousAddEquiv.preimage_mulLeft_smul"
p2m_attr_erase "simp" "IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
open scoped ENNReal

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "unipotentGL2 unipotentGL2_coe unipotentGL2_add exists_forall_lintegral_eq_mul_lintegral_mul_apply_col_det_of_forall_map_mulVec_eq_self exists_measurable_forall_lintegral_mul_unipotentGL2_eq_one"
namespace WeilQualitative
p2m_open "AutomorphicForm"

variable (K : Type) [Field K] [NumberField K]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]

local notation "𝔸" => AdeleRing (𝓞 K) K
local notation "Gp" => Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 K) K)
local notation "Xp" => (Fin 2 → AdeleRing (𝓞 K) K) × (AdeleRing (𝓞 K) K)ˣ

attribute [local instance 2000] NumberField.AdelicHaar.glBorel

theorem borelSpace_G : BorelSpace (GL (Fin 2) (AdeleRing (𝓞 K) K)) := borelSpace_glBorel _ _ _

theorem secondCountable_A : SecondCountableTopology (AdeleRing (𝓞 K) K) :=
  NumberField.AdeleRing.secondCountableTopology K

theorem secondCountable_G : SecondCountableTopology (GL (Fin 2) (AdeleRing (𝓞 K) K)) :=
  NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K

theorem secondCountable_units : SecondCountableTopology (AdeleRing (𝓞 K) K)ˣ := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K) := secondCountable_A K
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

attribute [local instance] borelSpace_G secondCountable_A secondCountable_G secondCountable_units

scoped instance borelSpace_pi : BorelSpace (Fin 2 → AdeleRing (𝓞 K) K) := Pi.borelSpace

theorem isMulRightInvariant_of_isHaarMeasure (τ : Measure Gp) [τ.IsHaarMeasure] :
    τ.IsMulRightInvariant := by
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  haveI := NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar K
  obtain ⟨c, hc⟩ : ∃ c : NNReal, τ = c • adelicGLHaar (Fin 2) (𝓞 K) K :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul τ (adelicGLHaar (Fin 2) (𝓞 K) K)⟩
  rw [hc]
  infer_instance

def proj (g : GL (Fin 2) (AdeleRing (𝓞 K) K)) : (Fin 2 → AdeleRing (𝓞 K) K) × (AdeleRing (𝓞 K) K)ˣ :=
  (fun i => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i 0, Matrix.GeneralLinearGroup.det g)

variable {K}

theorem continuous_GLdet : Continuous (Matrix.GeneralLinearGroup.det : Gp → (AdeleRing (𝓞 K) K)ˣ) := by
  rw [Units.continuous_iff]
  constructor
  · have : (Units.val ∘ (Matrix.GeneralLinearGroup.det : Gp → (AdeleRing (𝓞 K) K)ˣ)) =
        fun g : Gp => ((g : Gp) : Matrix (Fin 2) (Fin 2) 𝔸).det := by
      funext g; exact Matrix.GeneralLinearGroup.val_det_apply g
    rw [this]
    exact Units.continuous_val.matrix_det
  · have : (fun g : Gp => (((Matrix.GeneralLinearGroup.det g)⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : 𝔸)) =
        fun g : Gp => (((g⁻¹ : Gp) : Gp) : Matrix (Fin 2) (Fin 2) 𝔸).det := by
      funext g
      rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply]
    rw [this]
    exact (Units.continuous_val.comp continuous_inv).matrix_det

theorem measurable_proj : Measurable (proj K) := by
  refine Measurable.prodMk ?_ continuous_GLdet.measurable
  exact measurable_pi_iff.mpr fun i => (Units.continuous_val.matrix_elem i 0).measurable

theorem proj_mul_unipotentGL2 (g : Gp) (x : 𝔸) : proj K (g * unipotentGL2 x) = proj K g := by
  refine Prod.ext ?_ ?_
  · funext i
    fin_cases i <;> simp [proj, unipotentGL2_coe, Matrix.mul_apply, Fin.sum_univ_two]
  · have : Matrix.GeneralLinearGroup.det (unipotentGL2 x : Gp) = 1 := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, unipotentGL2_coe, Matrix.det_fin_two_of]
      simp
    simp [proj, this]

theorem continuous_unipotentGL2 : Continuous fun y : 𝔸 => (unipotentGL2 y : Gp) := by
  rw [Units.continuous_iff]
  constructor
  · have h : (Units.val ∘ fun y : 𝔸 => (unipotentGL2 y : Gp)) = fun y => !![1, y; 0, 1] :=
      funext fun y => rfl
    rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> first | exact continuous_const | exact continuous_id
  · have h : (fun y : 𝔸 => (((unipotentGL2 y : Gp)⁻¹ : Gp) : Matrix (Fin 2) (Fin 2) 𝔸)) =
        fun y => !![1, -y; 0, 1] := funext fun y => rfl
    show Continuous fun y : 𝔸 => (((unipotentGL2 y : Gp)⁻¹ : Gp) : Matrix (Fin 2) (Fin 2) 𝔸)
    rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> first | exact continuous_const | exact continuous_neg

theorem exists_proj_eq_of_exists_col_eq {p : Xp}
    (h : ∃ g : Gp, (fun i => ((g : Gp) : Matrix (Fin 2) (Fin 2) 𝔸) i 0) = p.1) :
    ∃ g : Gp, proj K g = p := by
  obtain ⟨g, hg⟩ := h
  set u : (AdeleRing (𝓞 K) K)ˣ := (Matrix.GeneralLinearGroup.det g)⁻¹ * p.2 with hu

  let d : Gp :=
    ⟨!![(1 : 𝔸), 0; 0, (u : 𝔸)], !![(1 : 𝔸), 0; 0, ((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : 𝔸)],
      by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
      by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩
  have hdval : ((d : Gp) : Matrix (Fin 2) (Fin 2) 𝔸) = !![(1 : 𝔸), 0; 0, (u : 𝔸)] := rfl
  refine ⟨g * d, Prod.ext ?_ ?_⟩
  · funext i
    have hgi := congr_fun hg i
    simp only [proj, Units.val_mul, hdval, Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> simp <;> simpa using congr_fun hg _
  · have hdet : Matrix.GeneralLinearGroup.det d = u := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, hdval, Matrix.det_fin_two_of]
      simp
    simp only [proj, map_mul, hdet, hu, mul_inv_cancel_left]

def dens (δ : (AdeleRing (𝓞 K) K)ˣ) : ℝ≥0∞ := ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K δ)⁻¹

theorem measurable_dens : Measurable (dens (K := K)) := by
  unfold dens
  exact ENNReal.measurable_ofReal.comp
    (NumberField.TateGlobal.continuous_ideleNorm K).measurable.inv

theorem dens_ne_zero (δ : (AdeleRing (𝓞 K) K)ˣ) : dens (K := K) δ ≠ 0 := by
  unfold dens
  rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
  exact inv_pos.mpr (NumberField.TateGlobal.ideleNorm_pos δ)

variable (K)

theorem main
    (τ : Measure (GL (Fin 2) (AdeleRing (𝓞 K) K))) (hτ : τ.IsHaarMeasure)
    (μ : Measure (AdeleRing (𝓞 K) K)) (hμ : μ.IsAddHaarMeasure)
    (ν : Measure (AdeleRing (𝓞 K) K)ˣ) (hν : ν.IsHaarMeasure) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      ∀ (w : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℝ≥0∞)
        (Ψ : (Fin 2 → AdeleRing (𝓞 K) K) × (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞),
        Measurable w → Measurable Ψ →
        (∀ᵐ g ∂τ, ∫⁻ x, w (g * AutomorphicForm.unipotentGL2 x) ∂μ = 1) →
        ∫⁻ g, w g * Ψ (fun i => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i 0,
            Matrix.GeneralLinearGroup.det g) ∂τ =
          c * ∫⁻ p, ∫⁻ δ, Ψ (p, δ) * ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K δ)⁻¹ ∂ν
            ∂(Measure.pi fun _ : Fin 2 => μ) := by
  haveI := hτ; haveI := hμ; haveI := hν
  haveI : τ.IsMulRightInvariant := isMulRightInvariant_of_isHaarMeasure K τ
  haveI : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μ
  haveI : μ.IsNegInvariant := inferInstance

  obtain ⟨w₀, hw₀m, hw₀⟩ :=
    AutomorphicForm.exists_measurable_forall_lintegral_mul_unipotentGL2_eq_one K μ hμ

  set ν' : Measure (AdeleRing (𝓞 K) K)ˣ :=
    ν.withDensity fun δ => ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K δ)⁻¹ with hν'
  set ρ : Measure Xp := (Measure.pi fun _ : Fin 2 => μ).prod ν' with hρ
  have hdm : Measurable fun δ : (AdeleRing (𝓞 K) K)ˣ =>
      ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K δ)⁻¹ := measurable_dens
  haveI : T1Space (AdeleRing (𝓞 K) K) := T2Space.t1Space
  haveI : LocallyCompactSpace (AdeleRing (𝓞 K) K)ˣ := inferInstance
  haveI : SigmaCompactSpace (AdeleRing (𝓞 K) K)ˣ := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaFinite ν := inferInstance
  haveI : SigmaFinite ν' := by rw [hν']; infer_instance
  have hρσ : SigmaFinite ρ := by rw [hρ]; infer_instance
  have hρinv : ∀ h : Gp, Measure.map (fun p : Xp =>
      (((h : Gp) : Matrix (Fin 2) (Fin 2) 𝔸).mulVec p.1, Matrix.GeneralLinearGroup.det h * p.2)) ρ = ρ :=
    fun h => NumberField.AdeleRing.map_mulVec_det_mul_pi_prod_withDensity_ideleNorm_inv_eq_self K μ hμ ν hν h
  have hρ0 : ρ {p : Xp | ¬ ∃ g : Gp,
      ((fun i => ((g : Gp) : Matrix (Fin 2) (Fin 2) 𝔸) i 0), Matrix.GeneralLinearGroup.det g) = p} = 0 := by
    have hcol := NumberField.AdeleRing.pi_measure_setOf_not_exists_apply_col_eq_eq_zero K μ hμ
    have hsub : {p : Xp | ¬ ∃ g : Gp,
        ((fun i => ((g : Gp) : Matrix (Fin 2) (Fin 2) 𝔸) i 0), Matrix.GeneralLinearGroup.det g) = p} ⊆
        {c : Fin 2 → 𝔸 | ¬ ∃ g : Gp, (fun i => ((g : Gp) : Matrix (Fin 2) (Fin 2) 𝔸) i 0) = c} ×ˢ
          (Set.univ : Set (AdeleRing (𝓞 K) K)ˣ) := by
      intro p hp
      simp only [Set.mem_prod, Set.mem_setOf_eq, Set.mem_univ, and_true]
      intro hc
      exact hp (exists_proj_eq_of_exists_col_eq hc)
    refine measure_mono_null hsub ?_
    rw [hρ, Measure.prod_prod, hcol, zero_mul]

  obtain ⟨c₁, hc₁top, hc₁⟩ :=
    AutomorphicForm.exists_forall_lintegral_eq_mul_lintegral_mul_apply_col_det_of_forall_map_mulVec_eq_self
      K τ hτ μ hμ w₀ hw₀m hw₀ ρ hρσ hρinv hρ0

  have hc₁0 : c₁ ≠ 0 := by
    intro h0
    have h1 := hc₁ (fun _ => 1) measurable_const
    rw [h0, zero_mul, lintegral_const, one_mul] at h1

    have hpi : (Measure.pi fun _ : Fin 2 => μ) Set.univ ≠ 0 := by
      haveI : (Measure.pi fun _ : Fin 2 => μ).IsAddHaarMeasure := inferInstance
      exact (isOpen_univ.measure_pos (Measure.pi fun _ : Fin 2 => μ) Set.univ_nonempty).ne'
    have hν'0 : ν' Set.univ ≠ 0 := by
      rw [hν', withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      intro hz
      rw [lintegral_eq_zero_iff hdm] at hz
      have : ν Set.univ = 0 := by
        have hall : ∀ᵐ δ ∂ν, False := by
          filter_upwards [hz] with δ hδ
          exact dens_ne_zero δ hδ
        simpa [ae_iff] using hall
      exact (isOpen_univ.measure_pos ν Set.univ_nonempty).ne' this
    rw [hρ, ← Set.univ_prod_univ, Measure.prod_prod] at h1
    exact (mul_ne_zero hpi hν'0) h1
  refine ⟨c₁⁻¹, ENNReal.inv_ne_zero.mpr hc₁top, ENNReal.inv_ne_top.mpr hc₁0, ?_⟩
  intro w Ψ hw hΨ hw1

  have hΦ : Measurable fun g : Gp => Ψ (proj K g) := hΨ.comp measurable_proj
  have havg := MeasureTheory.lintegral_mul_eq_lintegral_mul_of_forall_mul_eq_of_ae_lintegral_comp_mul_eq_one
    τ μ (fun x : 𝔸 => (unipotentGL2 x : Gp)) continuous_unipotentGL2.measurable
    (fun x y => unipotentGL2_add x y) (fun g : Gp => Ψ (proj K g)) hΦ
    (fun g x => by simp only [proj_mul_unipotentGL2]) w w₀ hw hw₀m hw1 (ae_of_all _ hw₀)

  have htonelli : ∫⁻ p, Ψ p ∂ρ =
      ∫⁻ p, ∫⁻ δ, Ψ (p, δ) * ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K δ)⁻¹ ∂ν
        ∂(Measure.pi fun _ : Fin 2 => μ) := by
    rw [hρ, lintegral_prod _ hΨ.aemeasurable]
    refine lintegral_congr fun p => ?_
    have hg : Measurable fun δ : (AdeleRing (𝓞 K) K)ˣ => Ψ (p, δ) :=
      hΨ.comp (measurable_const.prodMk measurable_id)
    rw [hν', lintegral_withDensity_eq_lintegral_mul ν hdm hg]
    refine lintegral_congr fun δ => ?_
    simp only [Pi.mul_apply]
    rw [mul_comm]

  have hmain := hc₁ Ψ hΨ
  change ∫⁻ g, w g * Ψ (proj K g) ∂τ = c₁⁻¹ * _
  rw [havg, ← htonelli, hmain, ← mul_assoc, ENNReal.inv_mul_cancel hc₁0 hc₁top, one_mul]
  rfl

end AutomorphicForm.WeilQualitative
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_lintegral_mul_apply_col_det_eq_mul_lintegral_lintegral_ideleNorm_inv_of_ae_lintegral_mul_unipotentGL2_eq_one.AutomorphicForm P2MW.S_AutomorphicForm_exists_forall_lintegral_mul_apply_col_det_eq_mul_lintegral_lintegral_ideleNorm_inv_of_ae_lintegral_mul_unipotentGL2_eq_one.AutomorphicForm.WeilQualitative"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_lintegral_mul_apply_col_det_eq_mul_lintegral_lintegral_ideleNorm_inv_of_ae_lintegral_mul_unipotentGL2_eq_one.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_lintegral_mul_apply_col_det_eq_mul_lintegral_lintegral_ideleNorm_inv_of_ae_lintegral_mul_unipotentGL2_eq_one.AutomorphicForm P2MW.S_AutomorphicForm_exists_forall_lintegral_mul_apply_col_det_eq_mul_lintegral_lintegral_ideleNorm_inv_of_ae_lintegral_mul_unipotentGL2_eq_one.AutomorphicForm.WeilQualitative"

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem solution
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (τ : Measure (GL (Fin 2) (AdeleRing (𝓞 K) K))) (hτ : τ.IsHaarMeasure)
    (μ : Measure (AdeleRing (𝓞 K) K)) (hμ : μ.IsAddHaarMeasure)
    (ν : Measure (AdeleRing (𝓞 K) K)ˣ) (hν : ν.IsHaarMeasure) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      ∀ (w : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℝ≥0∞)
        (Ψ : (Fin 2 → AdeleRing (𝓞 K) K) × (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞),
        Measurable w → Measurable Ψ →
        (∀ᵐ g ∂τ, ∫⁻ x, w (g * AutomorphicForm.unipotentGL2 x) ∂μ = 1) →
        ∫⁻ g, w g * Ψ (fun i => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i 0,
            Matrix.GeneralLinearGroup.det g) ∂τ =
          c * ∫⁻ p, ∫⁻ δ, Ψ (p, δ) * ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K δ)⁻¹ ∂ν
            ∂(Measure.pi fun _ : Fin 2 => μ) :=
  AutomorphicForm.WeilQualitative.main K τ hτ μ hμ ν hν

end S_AutomorphicForm_exists_forall_lintegral_mul_apply_col_det_eq_mul_lintegral_lintegral_ideleNorm_inv_of_ae_lintegral_mul_unipotentGL2_eq_one
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_lintegral_mul_apply_col_det_eq_mul_lintegral_lintegral_ideleNorm_inv_of_ae_lintegral_mul_unipotentGL2_eq_one (solution)
