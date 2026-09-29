-- Prove2me | solution 1 for AutomorphicForm.convOp_pseudoEisenstein_eq_pseudoEisenstein_convOp_of_isSlabProfile
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/ee88eb12-72ed-5310-9591-69a3cc9036fa

import Theorems.Thm_AutomorphicForm_finite_support_pseudoEisenstein_summand
import Theorems.Thm_NumberField_AdelicHeight_exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_convOp_pseudoEisenstein_eq_pseudoEisenstein_convOp_of_isSlabProfile
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.cpowChar_apply_val ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar AutomorphicForm
open scoped NNReal ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

open NumberField.AdelicHeight

theorem solution
    (F : Type) [Field F] [NumberField F]
    (Z : Subgroup (AdeleRing (𝓞 F) F)ˣ) (ξ : Z →* ℂˣ) (hξu : ∀ z : Z, ‖((ξ z : ℂˣ) : ℂ)‖ = 1)
    (ψ : AdelicGL2 (𝓞 F) F → ℂ) (_hψ : AutomorphicForm.IsSlabProfile F Z ξ ψ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f)
    (g : AdelicGL2 (𝓞 F) F) :
    convOp F f (AutomorphicForm.pseudoEisenstein F ψ) g =
      AutomorphicForm.pseudoEisenstein F (convOp F f ψ) g := by
  classical
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 F) F) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F

  set μH := adelicGLHaar (Fin 2) (𝓞 F) F with hμH

  set S := tsupport f with hS
  have hSc : IsCompact S := _hfc
  have hf0 : ∀ x, x ∉ S → f x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx

  have hdetc : Continuous fun x : AdelicGL2 (𝓞 F) F =>
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) :=
    NumberField.TateGlobal.continuous_ideleNorm_det F
  have hwindow : ∃ m M : ℝ, 0 < m ∧ ∀ x ∈ S,
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc m M := by
    by_cases hne : S.Nonempty
    · obtain ⟨x₀, hx₀, hmin⟩ := hSc.exists_isMinOn hne hdetc.continuousOn
      obtain ⟨x₁, hx₁, hmax⟩ := hSc.exists_isMaxOn hne hdetc.continuousOn
      exact ⟨_, _, NumberField.TateGlobal.ideleNorm_pos _, fun x hx => ⟨hmin hx, hmax hx⟩⟩
    · exact ⟨1, 1, one_pos, fun x hx => (hne ⟨x, hx⟩).elim⟩
  obtain ⟨m, M, hm, hmM⟩ := hwindow
  have hbdd : ∀ h : AdelicGL2 (𝓞 F) F, ∃ C : ℝ, ∀ x ∈ S, ‖ψ (h * x)‖ ≤ C := by
    intro h
    have hd : 0 < NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det h) :=
      NumberField.TateGlobal.ideleNorm_pos _
    obtain ⟨C, hC⟩ := _hψ.bounded_on_slab
      (NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det h) * m)
      (NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det h) * M) (mul_pos hd hm)
    refine ⟨C, fun x hx => hC _ ?_⟩
    rw [map_mul, NumberField.TateGlobal.ideleNorm_mul]
    exact ⟨mul_le_mul_of_nonneg_left (hmM x hx).1 hd.le, mul_le_mul_of_nonneg_left (hmM x hx).2 hd.le⟩

  have hψm : Measurable ψ := _hψ.measurable
  have hint : ∀ h : AdelicGL2 (𝓞 F) F, Integrable (fun x => ψ (h * x) * f x) μH := by
    intro h
    obtain ⟨C, hC⟩ := hbdd h
    have hmeas : AEStronglyMeasurable (fun x => ψ (h * x) * f x) μH :=
      ((hψm.comp (continuous_mul_left h).measurable).aestronglyMeasurable).mul _hf.aestronglyMeasurable
    refine Integrable.mono' ((_hf.norm.integrable_of_hasCompactSupport _hfc.norm).const_mul (max C 0)) hmeas
      (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ S
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right ((hC x hx).trans (le_max_left _ _)) (norm_nonneg _)
    · rw [hf0 x hx]; simp
  have hfn_int : Integrable (fun x => ‖f x‖) μH := _hf.norm.integrable_of_hasCompactSupport _hfc.norm

  have hΨr_int : ∀ h : AdelicGL2 (𝓞 F) F, Integrable (fun x => ‖ψ (h * x)‖ * ‖f x‖) μH := fun h => by
    have := (hint h).norm; simpa only [norm_mul] using this
  have hΨr_nn : ∀ h : AdelicGL2 (𝓞 F) F, 0 ≤ ∫ x, ‖ψ (h * x)‖ * ‖f x‖ ∂μH := fun h =>
    integral_nonneg fun x => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  set Ψ : AdelicGL2 (𝓞 F) F → ℂ := fun h => (((∫ x, ‖ψ (h * x)‖ * ‖f x‖ ∂μH) : ℝ) : ℂ) with hΨ
  have hΨprof : IsSlabProfile F Z (1 : Z →* ℂˣ) Ψ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hsm : StronglyMeasurable (Function.uncurry fun (h x : AdelicGL2 (𝓞 F) F) => ‖ψ (h * x)‖ * ‖f x‖) :=
        (((hψm.comp measurable_mul).norm).mul ((_hf.measurable.comp measurable_snd).norm)).stronglyMeasurable
      exact Complex.measurable_ofReal.comp hsm.integral_prod_right.measurable
    · intro x h
      simp only [hΨ, mul_assoc, _hψ.unipotent_mul]
    · intro γ hγ h
      simp only [hΨ, mul_assoc, _hψ.borel_mul γ hγ]
    · intro z h
      simp only [hΨ, mul_assoc, _hψ.central_transform, norm_mul, hξu, one_mul, MonoidHom.one_apply,
        Units.val_one]
    · intro d₁ d₂ hd₁
      obtain ⟨C, hC⟩ := _hψ.bounded_on_slab (d₁ * m) (d₂ * M) (mul_pos hd₁ hm)
      refine ⟨max C 0 * ∫ x, ‖f x‖ ∂μH, fun h hh => ?_⟩
      simp only [hΨ, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hΨr_nn h)]
      calc (∫ x, ‖ψ (h * x)‖ * ‖f x‖ ∂μH) ≤ ∫ x, max C 0 * ‖f x‖ ∂μH := by
            refine integral_mono (hΨr_int h) (hfn_int.const_mul _) fun x => ?_
            by_cases hx : x ∈ S
            · refine mul_le_mul_of_nonneg_right ((hC _ ?_).trans (le_max_left _ _)) (norm_nonneg _)
              rw [map_mul, NumberField.TateGlobal.ideleNorm_mul]
              exact ⟨mul_le_mul hh.1 (hmM x hx).1 hm.le (hd₁.le.trans hh.1),
                mul_le_mul hh.2 (hmM x hx).2 (NumberField.TateGlobal.ideleNorm_pos _).le
                  (hd₁.le.trans (hh.1.trans hh.2))⟩
            · show ‖ψ (h * x)‖ * ‖f x‖ ≤ max C 0 * ‖f x‖
              rw [hf0 x hx]; simp
        _ = max C 0 * ∫ x, ‖f x‖ ∂μH := integral_const_mul _ _
    · obtain ⟨a, b, ha, hband⟩ := _hψ.height_band
      obtain ⟨κ, Kc, hκ, hcmp⟩ :=
        NumberField.AdelicHeight.exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact F S hSc
      refine ⟨a / max Kc 1, b / κ, div_pos ha (lt_max_of_lt_right one_pos), fun h hh => ?_⟩
      have hex : ∃ x ∈ S, ψ (h * x) ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        apply hh
        simp only [hΨ]
        rw [integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x => ?_), Complex.ofReal_zero]
        show ‖ψ (h * x)‖ * ‖f x‖ = (0 : AdelicGL2 (𝓞 F) F → ℝ) x
        by_cases hx : x ∈ S
        · rw [hcon x hx, norm_zero, zero_mul, Pi.zero_apply]
        · rw [hf0 x hx, norm_zero, mul_zero, Pi.zero_apply]
      obtain ⟨x, hx, hψx⟩ := hex
      have hhx := hband _ hψx
      obtain ⟨h1, h2⟩ := hcmp h x hx
      have hHpos := adelicHeight_pos h
      constructor
      · rw [div_le_iff₀ (lt_max_of_lt_right one_pos)]
        calc a ≤ adelicHeight F (h * x) := hhx.1
          _ ≤ Kc * adelicHeight F h := h2
          _ ≤ max Kc 1 * adelicHeight F h := mul_le_mul_of_nonneg_right (le_max_left _ _) hHpos.le
          _ = adelicHeight F h * max Kc 1 := mul_comm _ _
      · rw [le_div_iff₀ hκ]
        calc adelicHeight F h * κ = κ * adelicHeight F h := mul_comm _ _
          _ ≤ adelicHeight F (h * x) := h1
          _ ≤ b := hhx.2

  have hfinB := AutomorphicForm.finite_support_pseudoEisenstein_summand F Z 1 Ψ hΨprof g
  set B : Finset F := hfinB.toFinset with hB
  have hBout : ∀ β : F, β ∉ B → Ψ ((adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β)) * g) = 0 := fun β hβ => by
    by_contra hne
    exact hβ (hfinB.mem_toFinset.2 hne)

  have hzero : ∀ β : F, β ∉ B → ∀ᵐ x ∂μH, ψ ((adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β)) * g * x) * f x = 0 := by
    intro β hβ
    have h0 : (∫ x, ‖ψ ((adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β)) * g * x)‖ * ‖f x‖ ∂μH) = 0 := by
      have := hBout β hβ
      simp only [hΨ, Complex.ofReal_eq_zero] at this
      exact this
    have hae := (integral_eq_zero_iff_of_nonneg (fun x => mul_nonneg (norm_nonneg _) (norm_nonneg _)) (hΨr_int _)).1 h0
    filter_upwards [hae] with x hx
    have : ‖ψ ((adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β)) * g * x) * f x‖ = 0 := by rw [norm_mul]; exact hx
    exact norm_eq_zero.1 this
  haveI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := F)
  have hzero' : ∀ᵐ x ∂μH, ∀ β : F, β ∉ B → ψ ((adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β)) * g * x) * f x = 0 := by
    rw [ae_all_iff]
    intro β
    by_cases hβ : β ∈ B
    · exact Filter.Eventually.of_forall fun x h => (h hβ).elim
    · exact (hzero β hβ).mono fun x hx _ => hx

  have hRout : ∀ β : F, β ∉ B → convOp F f ψ ((adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β)) * g) = 0 := by
    intro β hβ
    rw [convOp_apply, rightConv_apply]
    exact integral_eq_zero_of_ae (hzero β hβ)

  have hLHS : convOp F f (AutomorphicForm.pseudoEisenstein F ψ) g =
      ∫ x, (ψ (g * x) + ∑' β : F, ψ ((adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β)) * (g * x))) * f x ∂μH := by
    rw [convOp_apply, rightConv_apply]
    rfl
  have hsplit : ∀ᵐ x ∂μH, (ψ (g * x) + ∑' β : F, ψ ((adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β)) * (g * x))) * f x =
      ψ (g * x) * f x + ∑ β ∈ B, ψ ((adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β)) * g * x) * f x := by
    filter_upwards [hzero'] with x hx
    rw [add_mul]
    congr 1
    by_cases hfx : f x = 0
    · simp [hfx]
    · rw [tsum_eq_sum (s := B) (fun β hβ => ?_), Finset.sum_mul]
      · exact Finset.sum_congr rfl fun β _ => by simp only [mul_assoc]
      · have h := hx β hβ
        rw [mul_assoc] at h
        exact (mul_eq_zero.1 h).resolve_right hfx
  have hintβ : ∀ β : F, Integrable (fun x => ψ ((adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β)) * g * x) * f x) μH :=
    fun β => hint _
  rw [hLHS, integral_congr_ae hsplit, integral_add (hint g) (integrable_finsetSum _ fun β _ => hintβ β),
    integral_finsetSum _ fun β _ => hintβ β, pseudoEisenstein_apply]
  congr 1
  rw [tsum_eq_sum (s := B) (fun β hβ => hRout β hβ)]
  exact Finset.sum_congr rfl fun β _ => by rw [convOp_apply, rightConv_apply]

end S_AutomorphicForm_convOp_pseudoEisenstein_eq_pseudoEisenstein_convOp_of_isSlabProfile
end P2MW
export P2MW.S_AutomorphicForm_convOp_pseudoEisenstein_eq_pseudoEisenstein_convOp_of_isSlabProfile (solution)
