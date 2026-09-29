-- Prove2me | solution 1 for AutomorphicForm.one_le_of_archOccursInClassOf_isArchLoweringAnnihilatedAt_of_coversModCentre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/c8bf1abc-595e-5e44-bb37-9e8aa0624c25

import Mathlib
import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchLoweringAnnihilated
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_NumberField_AdelicBox
import Theorems.Thm_AutomorphicForm_isArchLoweringAnnihilatedAt_iff_isArchSmoothAt_and_lower_eq_zero_of_hasArchCharacterAt
import Theorems.Thm_AutomorphicForm_archCasimirAt_eq_smul_of_lower_eq_zero_of_hasArchCharacterAt
import Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_exists_cpow_centralExponent_of_isReal
import Theorems.Thm_AutomorphicForm_archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt
import Theorems.Thm_AutomorphicForm_apply_mul_archRealGLAt_eq_of_archDerivAt_E_eq_zero_of_archDerivAt_Fm_eq_zero
import Theorems.Thm_AutomorphicForm_archOccursInClassOf_continuous_foldr_archDerivAt_of_archOccursInClassOf_archCasimirAt_eq_smul_of_coversModCentre
import Theorems.Thm_AutomorphicForm_im_eq_zero_and_le_re_of_archOccursInClassOf_archCasimirAt_eq_smul_of_coversModCentre
import Theorems.Thm_AutomorphicForm_archOccursInClassOf_lower_eq_zero_of_archCasimirAt_eq_smul_of_coversModCentre
import Theorems.Thm_AutomorphicForm_archOccursInClassOf_raise_eq_zero_of_archCasimirAt_eq_smul_of_coversModCentre
import Theorems.Thm_AutomorphicForm_eq_zero_of_isCuspidalFn_of_forall_apply_mul_archRealGLAt_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_one_le_of_archOccursInClassOf_isArchLoweringAnnihilatedAt_of_coversModCentre
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero LanglandsTunnell.LDatum.mk.sizeOf_spec LanglandsTunnell.LDatum.badFactor_zero LanglandsTunnell.LDatum.mk.injEq AutomorphicForm.rightTranslationEmbed_smul_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

p2m_open "NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm P2MW.S_AutomorphicForm_one_le_of_archOccursInClassOf_isArchLoweringAnnihilatedAt_of_coversModCentre.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion"

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "ArchOccursInClassOf SmoothCuspRealizationAt finiteAdelicGL2Subgroup productionPinsOf AdelicGL2 globalPoints centralScalar HeckeEigensystem rowIsometrySubgroup₀Map norm_ringEquivRealOfIsReal archWeightCharAt rowIsometrySubgroup₀ archWeightCharℝ HasArchCharacterAt₀ IsArchLoweringAnnihilatedAt archRealGLAt IsArchSmoothAt ArchDir archDerivAt archCasimirAt isArchLoweringAnnihilatedAt_iff_isArchSmoothAt_and_lower_eq_zero_of_hasArchCharacterAt archCasimirAt_eq_smul_of_lower_eq_zero_of_hasArchCharacterAt SmoothCuspRealizationAt.exists_cpow_centralExponent_of_isReal archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt apply_mul_archRealGLAt_eq_of_archDerivAt_E_eq_zero_of_archDerivAt_Fm_eq_zero archOccursInClassOf_continuous_foldr_archDerivAt_of_archOccursInClassOf_archCasimirAt_eq_smul_of_coversModCentre im_eq_zero_and_le_re_of_archOccursInClassOf_archCasimirAt_eq_smul_of_coversModCentre archOccursInClassOf_lower_eq_zero_of_archCasimirAt_eq_smul_of_coversModCentre archOccursInClassOf_raise_eq_zero_of_archCasimirAt_eq_smul_of_coversModCentre eq_zero_of_isCuspidalFn_of_forall_apply_mul_archRealGLAt_eq"
namespace LowestWeightPositivityAssembly
p2m_open "AutomorphicForm"

variable {F : Type} [Field F] [NumberField F]

abbrev wchar {w : InfinitePlace F} (hw : w.IsReal) (n : ℤ) : rowIsometrySubgroup₀ w.Completion →* ℂˣ :=
  (archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))

omit [NumberField F] in
theorem archWeightCharAt_eq_wchar {w : InfinitePlace F} (hw : w.IsReal) (n : ℤ) :
    archWeightCharAt hw n = wchar hw n := rfl

theorem central_transform_of_realization {D : Set (AdelicGL2 (𝓞 F) F)} {Θ : HeckeEigensystem F ℂ}
    (R : SmoothCuspRealizationAt F
      (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) Θ) :
    ∀ (z : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ)) (g : AdelicGL2 (𝓞 F) F),
      R.toFun (centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ) * g) = ((R.centralChar z : ℂˣ) : ℂ) * R.toFun g := by
  intro z g
  letI := (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
    (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).mS
  letI : MeasureTheory.MeasureSpace (AdelicGL2 (𝓞 F) F) :=
    ⟨(productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).μ⟩
  exact R.smoothCusp.1.1.central_transform z g

theorem left_invariant_of_realization {D : Set (AdelicGL2 (𝓞 F) F)} {Θ : HeckeEigensystem F ℂ}
    (R : SmoothCuspRealizationAt F
      (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) Θ) :
    ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), R.toFun (globalPoints (𝓞 F) F γ * g) = R.toFun g := by
  intro γ g
  letI := (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
    (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).mS
  letI : MeasureTheory.MeasureSpace (AdelicGL2 (𝓞 F) F) :=
    ⟨(productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).μ⟩
  exact R.smoothCusp.1.1.left_invariant γ g

theorem archDerivAt_H_eq_zero_and_add_eq_zero {w : InfinitePlace F} (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hL : archDerivAt hw .H φ - Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ) = 0)
    (hR : archDerivAt hw .H φ + Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ) = 0) :
    archDerivAt hw .H φ = 0 ∧ archDerivAt hw .E φ + archDerivAt hw .Fm φ = 0 := by
  have h1 : (2 : ℂ) • archDerivAt hw .H φ = 0 := by
    have := congrArg₂ (· + ·) hL hR
    simp only [add_zero] at this
    rw [← this, two_smul]; abel
  have hH : archDerivAt hw .H φ = 0 := by
    have := congrArg ((2 : ℂ)⁻¹ • ·) h1
    simpa [smul_smul] using this
  refine ⟨hH, ?_⟩
  have h2 : Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ) = 0 := by
    rw [hH, zero_add] at hR; exact hR
  have := congrArg (Complex.I⁻¹ • ·) h2
  simpa [smul_smul, Complex.I_ne_zero] using this

end AutomorphicForm.LowestWeightPositivityAssembly

end

open AutomorphicForm.LowestWeightPositivityAssembly in
theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Θ : HeckeEigensystem F ℂ)
    (w : InfinitePlace F) (hw : w.IsReal) (k : ℤ)
    (hk :
      ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
        (fun φ => HasArchCharacterAt₀ F w
            ((archWeightCharℝ k).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
              (norm_ringEquivRealOfIsReal hw))) φ ∧
          IsArchLoweringAnnihilatedAt w hw φ)) :
    1 ≤ k := by

  have occ1 : ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
      (fun φ => HasArchCharacterAt₀ F w (wchar hw k) φ ∧ IsArchSmoothAt hw φ ∧
        archCasimirAt hw φ = (((k : ℂ) / 2) * (1 - (k : ℂ) / 2)) • φ) := by
    obtain ⟨Θ', hΘ', R', hR', hty, hLA⟩ := hk
    obtain ⟨c₀, hc₀⟩ :=
      AutomorphicForm.SmoothCuspRealizationAt.exists_cpow_centralExponent_of_isReal F _ Θ'.toRawCentral R' hR' w hw
    have hdict := (AutomorphicForm.isArchLoweringAnnihilatedAt_iff_isArchSmoothAt_and_lower_eq_zero_of_hasArchCharacterAt
      F w hw k R'.toFun hR' hty R'.centralChar (central_transform_of_realization R') c₀ hc₀).mp hLA
    refine ⟨Θ', hΘ', R', hR', hty, hdict.1, ?_⟩
    exact AutomorphicForm.archCasimirAt_eq_smul_of_lower_eq_zero_of_hasArchCharacterAt F hw R'.toFun hdict.1 k
      (by rw [archWeightCharAt_eq_wchar]; exact hty) hdict.2

  have occ2 :=
    AutomorphicForm.archOccursInClassOf_continuous_foldr_archDerivAt_of_archOccursInClassOf_archCasimirAt_eq_smul_of_coversModCentre
      F c u d₁ d₂ T hd hcov Θ w hw k _ occ1

  have hk0 : 0 ≤ k := by
    obtain ⟨-, -, h2⟩ :=
      AutomorphicForm.im_eq_zero_and_le_re_of_archOccursInClassOf_archCasimirAt_eq_smul_of_coversModCentre
        F c u d₁ d₂ T hd hcov Θ w hw k _ occ2
    have hre : ((((k : ℂ) / 2) * (1 - (k : ℂ) / 2))).re = ((k : ℝ) / 2) * (1 - (k : ℝ) / 2) := by
      have e : (((k : ℂ) / 2) * (1 - (k : ℂ) / 2)) = ((((k : ℝ) / 2) * (1 - (k : ℝ) / 2) : ℝ) : ℂ) := by
        push_cast; ring
      rw [e, Complex.ofReal_re]
    rw [hre] at h2
    have hk' : (0 : ℝ) ≤ (k : ℝ) := by nlinarith [h2]
    exact_mod_cast hk'

  by_contra hcon
  have hk00 : k = 0 := by omega
  subst hk00

  have occ3 :=
    AutomorphicForm.archOccursInClassOf_lower_eq_zero_of_archCasimirAt_eq_smul_of_coversModCentre
      F c u d₁ d₂ T hd hcov Θ w hw 0
      (fun φ => HasArchCharacterAt₀ F w (wchar hw 0) φ ∧ IsArchSmoothAt hw φ ∧
        (∀ l : List ArchDir, Continuous (l.foldr (archDerivAt hw) φ) ∧
          ∀ e₁ e₂ : ℝ, 0 < e₁ → e₁ < e₂ → ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 F) F,
            NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
              ‖l.foldr (archDerivAt hw) φ g‖ ≤ B) ∧
        archCasimirAt hw φ = ((((0 : ℤ) : ℂ) / 2) * (1 - ((0 : ℤ) : ℂ) / 2)) • φ)
      (occ2.mono fun φ h => ⟨h, h⟩)

  have occ4 :=
    AutomorphicForm.archOccursInClassOf_raise_eq_zero_of_archCasimirAt_eq_smul_of_coversModCentre
      F c u d₁ d₂ T hd hcov Θ w hw 0
      (fun φ => HasArchCharacterAt₀ F w (wchar hw 0) φ ∧ IsArchSmoothAt hw φ ∧
        archDerivAt hw .H φ - Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ) = 0)
      (occ3.mono fun φ h => by
        obtain ⟨⟨hty, hsm, hreg, hΩ⟩, hL⟩ := h
        refine ⟨⟨hty, hsm, hL⟩, hty, hsm, hreg, ?_⟩
        have e : ((-((0 : ℤ) : ℂ) / 2) * (1 + ((0 : ℤ) : ℂ) / 2)) = ((((0 : ℤ) : ℂ) / 2) * (1 - ((0 : ℤ) : ℂ) / 2)) := by
          push_cast; ring
        rw [e]; exact hΩ)
  obtain ⟨Θ'', -, R'', hR'', ⟨hty0, hsm0, hL0⟩, hR0⟩ := occ4
  obtain ⟨hH, hS⟩ := archDerivAt_H_eq_zero_and_add_eq_zero hw R''.toFun hL0 hR0
  have hW : archDerivAt hw .E R''.toFun - archDerivAt hw .Fm R''.toFun = 0 := by
    have := AutomorphicForm.archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt F w hw 0 R''.toFun hsm0
      (by rw [archWeightCharAt_eq_wchar]; exact hty0)
    simpa using this
  have hE : archDerivAt hw .E R''.toFun = 0 := by
    have := congrArg₂ (· + ·) hS hW
    simp only [add_zero, add_add_sub_cancel] at this
    have h2 : (2 : ℂ) • archDerivAt hw .E R''.toFun = 0 := by rw [two_smul]; exact this
    have := congrArg ((2 : ℂ)⁻¹ • ·) h2
    simpa [smul_smul] using this
  have hF : archDerivAt hw .Fm R''.toFun = 0 := by
    rw [hE, zero_add] at hS; exact hS
  have hinv : ∀ (g : AdelicGL2 (𝓞 F) F) (h : GL (Fin 2) ℝ), Matrix.GeneralLinearGroup.det h = 1 →
      R''.toFun (g * archRealGLAt hw h) = R''.toFun g := fun g h hh =>
    AutomorphicForm.apply_mul_archRealGLAt_eq_of_archDerivAt_E_eq_zero_of_archDerivAt_Fm_eq_zero
      F w hw R''.toFun hsm0 hE hF g h hh
  have hzeroFun :=
    AutomorphicForm.eq_zero_of_isCuspidalFn_of_forall_apply_mul_archRealGLAt_eq F _ _ _ R''.toFun hR''
      (left_invariant_of_realization R'') R''.smoothCusp.1.2 w hw hinv
  obtain ⟨g, hg⟩ := R''.exists_ne_zero
  exact hg (by rw [hzeroFun]; rfl)

end S_AutomorphicForm_one_le_of_archOccursInClassOf_isArchLoweringAnnihilatedAt_of_coversModCentre
end P2MW
export P2MW.S_AutomorphicForm_one_le_of_archOccursInClassOf_isArchLoweringAnnihilatedAt_of_coversModCentre (solution)
