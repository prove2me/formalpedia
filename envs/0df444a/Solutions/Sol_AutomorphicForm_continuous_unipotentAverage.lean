-- Prove2me | solution 1 for AutomorphicForm.continuous_unipotentAverage
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/156b02d6-2493-5fea-a83c-9387b7b1d818

import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicBox
import Theorems.Thm_NumberField_AdelicFourier_integrable_of_mem_schwartzBruhat
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_continuous_unipotentAverage
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_continuous_unipotentAverage.AutomorphicForm IsDedekindDomain NumberField.TateGlobal"

section Core
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_continuous_unipotentAverage.AutomorphicForm"
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_continuous_unipotentAverage.AutomorphicForm"
namespace AutomorphicForm p2m_export "AutomorphicForm" "AdelicGL2 unipotentGL2 continuous_unipotentGL2" namespace T0Aux end AutomorphicForm.T0Aux
p2m_open_scoped "AutomorphicForm" in
theorem AutomorphicForm.T0Aux.det_unipotentGL2 {R : Type*} [CommRing R] (x : R) :
    Matrix.GeneralLinearGroup.det (unipotentGL2 x) = 1 := by
  ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two_of]
end Core

theorem solution
    (F : Type) [Field F] [NumberField F]
    (G : AdelicGL2 (𝓞 F) F → ℂ) (hcont : Continuous G)
    (hMG : ∃ C : ℝ, ∃ M : ℕ, ∀ g : AdelicGL2 (𝓞 F) F,
      ‖G g‖ ≤ C * max (ideleNorm F (Matrix.GeneralLinearGroup.det g))
        (ideleNorm F (Matrix.GeneralLinearGroup.det g))⁻¹ ^ M)
    (B : AdeleRing (𝓞 F) F → ℂ) (hB : B ∈ NumberField.AdelicFourier.schwartzBruhat F)
    (Φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hΦ : ∀ h : AdelicGL2 (𝓞 F) F, Φ h = (letI := adeleBorel (𝓞 F) F
        ∫ x, B x * G (h * unipotentGL2 x) ∂(adelicAddHaar (𝓞 F) F))) :
    Continuous Φ := by
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := borelSpace_adeleBorel (𝓞 F) F
  haveI : (adelicAddHaar (𝓞 F) F).IsAddHaarMeasure := isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 F) F) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  obtain ⟨C, M, hG⟩ := hMG
  have hBint : Integrable B (adelicAddHaar (𝓞 F) F) :=
    NumberField.AdelicFourier.integrable_of_mem_schwartzBruhat F (adelicAddHaar (𝓞 F) F) hB
  have hΦ' : Φ = fun h => ∫ x, B x * G (h * unipotentGL2 x) ∂(adelicAddHaar (𝓞 F) F) := funext hΦ
  rw [hΦ']

  set m : AdelicGL2 (𝓞 F) F → ℝ := fun h => max (ideleNorm F (Matrix.GeneralLinearGroup.det h))
      (ideleNorm F (Matrix.GeneralLinearGroup.det h))⁻¹ ^ M with hm
  have hmcont : Continuous m := by
    have h1 := NumberField.TateGlobal.continuous_ideleNorm_det F
    have h2 : Continuous fun h : AdelicGL2 (𝓞 F) F =>
        (ideleNorm F (Matrix.GeneralLinearGroup.det h))⁻¹ :=
      h1.inv₀ fun h => (ideleNorm_pos _).ne'
    exact (h1.max h2).pow M
  have hmn : ∀ h x, m (h * unipotentGL2 x) = m h := by
    intro h x; simp [hm, map_mul, AutomorphicForm.T0Aux.det_unipotentGL2]
  refine continuous_iff_continuousAt.2 fun h₀ => ?_

  have hnhds : ∀ᶠ h in nhds h₀, m h ≤ m h₀ + 1 := by
    have : ∀ᶠ h in nhds h₀, m h ∈ Set.Iio (m h₀ + 1) :=
      hmcont.continuousAt.eventually_mem (Iio_mem_nhds (by linarith))
    exact this.mono fun h hh => le_of_lt hh
  refine MeasureTheory.continuousAt_of_dominated (bound := fun x => ‖B x‖ * (|C| * (m h₀ + 1))) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun h =>
      hBint.aestronglyMeasurable.mul
        (hcont.comp (continuous_const.mul continuous_unipotentGL2)).aestronglyMeasurable
  · refine hnhds.mono fun h hh => ae_of_all _ fun x => ?_
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hmx : 0 ≤ m (h * unipotentGL2 x) := by
      simp only [hm]
      exact pow_nonneg (le_max_of_le_left (ideleNorm_pos _).le) M
    calc ‖G (h * unipotentGL2 x)‖ ≤ C * m (h * unipotentGL2 x) := hG _
      _ ≤ |C| * m (h * unipotentGL2 x) := mul_le_mul_of_nonneg_right (le_abs_self C) hmx
      _ = |C| * m h := by rw [hmn]
      _ ≤ |C| * (m h₀ + 1) := mul_le_mul_of_nonneg_left hh (abs_nonneg C)
  · exact hBint.norm.mul_const _
  · exact ae_of_all _ fun x =>
      (continuous_const.mul (hcont.comp (continuous_id.mul continuous_const))).continuousAt

end S_AutomorphicForm_continuous_unipotentAverage
end P2MW
export P2MW.S_AutomorphicForm_continuous_unipotentAverage (solution)
