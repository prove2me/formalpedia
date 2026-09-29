-- Prove2me | solution 1 for AutomorphicForm.continuous_archDerivAt_and_exists_bound_slab_of_isIsotypicCuspFormAt_of_rightConv_eq_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/81237a02-220c-5207-8233-694c8912c192

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.MellinTransform
import Definitions.Def_LanglandsTunnell_ArchParam
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport

import Theorems.Thm_AutomorphicForm_archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_continuous_rightConv_and_contDiff_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_exists_forall_norm_rightConv_le_of_ideleNorm_det_mem_Icc
import Theorems.Thm_AutomorphicForm_SiegelCovering_coversModCentre_productionPinsGeneral_D_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_continuous_archDerivAt_and_exists_bound_slab_of_isIsotypicCuspFormAt_of_rightConv_eq_rat
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicFourier IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SiegelCoordinates
open LanglandsTunnell LanglandsTunnell.RankinSelberg RSCarrier UnramifiedWhittaker AutomorphicForm.CuspidalConstituent

open _root_.LanglandsTunnell.RealArchParam in

theorem solution
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (N : Ideal (𝓞 ℚ)) (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (Θ : HeckeEigensystem ℚ ℂ)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hφ : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S Θ φ)
    (hconv : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ)
    (e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ < e₂) :
    IsArchSmoothAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) φ ∧
    (∀ d : ArchDir, Continuous (archDerivAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) d φ)) ∧
    (∀ d d' : ArchDir, Continuous (archDerivAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) d (archDerivAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) d' φ))) ∧
    ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
      ‖φ g‖ ≤ B ∧ (∀ d : ArchDir, ‖archDerivAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) d φ g‖ ≤ B) ∧
        (∀ d d' : ArchDir, ‖archDerivAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) d (archDerivAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) d' φ) g‖ ≤ B) := by
  classical
  have hw : (default : InfinitePlace ℚ).IsReal := IsTotallyReal.isReal _
  obtain ⟨α, hα, hφα⟩ := hconv

  have gen : ∀ (d : ArchDir) (β : AdelicGL2 (𝓞 ℚ) ℚ → ℂ), IsFactorizableTestFn ℚ β →
      IsArchSmoothAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (rightConv ℚ φ β) ∧
        ∃ β' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ β' ∧
          archDerivAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) d (rightConv ℚ φ β) = rightConv ℚ φ β' := by
    intro d β hβ
    have H := AutomorphicForm.archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn ℚ hw d
    obtain ⟨hsm, hD⟩ := H.1 φ β hφ.continuous hβ
    obtain ⟨fa, ff, hfa, hff, hβeq⟩ := hβ
    obtain ⟨fa', hfa', hfeq⟩ := H.2.1 fa ff hfa
    refine ⟨hsm, fun y => fa' (AdelicLevel.glArch (𝓞 ℚ) ℚ y) * ff (AdelicLevel.glFin (𝓞 ℚ) ℚ y),
      ⟨fa', ff, hfa', hff, fun g => rfl⟩, ?_⟩
    rw [hD, ← hfeq]
    congr 1
    funext y
    simp only [hβeq]

  have h1 : ∀ d : ArchDir, ∃ β' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ β' ∧
      archDerivAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) d φ = rightConv ℚ φ β' := by
    intro d
    obtain ⟨-, β', hβ', hD⟩ := gen d α hα
    rw [hφα] at hD
    exact ⟨β', hβ', hD⟩
  choose β₁ hβ₁ hD₁ using h1

  have h2 : ∀ d d' : ArchDir, ∃ β'' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ β'' ∧
      archDerivAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) d
        (archDerivAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) d' φ) = rightConv ℚ φ β'' := by
    intro d d'
    obtain ⟨-, β'', hβ'', hD⟩ := gen d (β₁ d') (hβ₁ d')
    exact ⟨β'', hβ'', by rw [hD₁ d']; exact hD⟩
  choose β₂ hβ₂ hD₂ using h2

  have hsm : IsArchSmoothAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) φ := by
    have h := (gen ArchDir.H α hα).1
    rwa [hφα] at h
  have hc1 : ∀ d : ArchDir, Continuous (archDerivAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) d φ) := by
    intro d; rw [hD₁ d]
    exact (AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn ℚ φ hφ.continuous _ (hβ₁ d)).1
  have hc2 : ∀ d d' : ArchDir, Continuous (archDerivAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) d
      (archDerivAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) d' φ)) := by
    intro d d'; rw [hD₂ d d']
    exact (AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn ℚ φ hφ.continuous _ (hβ₂ d d')).1

  have bnd : ∀ β : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ β → ∃ M : ℝ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ → ‖rightConv ℚ φ β g‖ ≤ M := by
    intro β hβ
    exact AutomorphicForm.exists_forall_norm_rightConv_le_of_ideleNorm_det_mem_Icc ℚ (1/2 : ℝ) 1 (1/2) 2
      (classRepTranslates ℚ) (by norm_num) AutomorphicForm.SiegelCovering.coversModCentre_productionPinsGeneral_D_rat
      ξ φ hφ.smoothCusp.1 hφ.continuous β hβ e₁ e₂ he₁
  obtain ⟨M₀, hM₀⟩ := bnd α hα
  have b1 : ∀ d : ArchDir, ∃ M : ℝ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
        ‖archDerivAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) d φ g‖ ≤ M := by
    intro d
    obtain ⟨M, hM⟩ := bnd _ (hβ₁ d)
    exact ⟨M, fun g hg => by rw [hD₁ d]; exact hM g hg⟩
  choose M₁ hM₁ using b1
  have b2 : ∀ d d' : ArchDir, ∃ M : ℝ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
        ‖archDerivAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) d
          (archDerivAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) d' φ) g‖ ≤ M := by
    intro d d'
    obtain ⟨M, hM⟩ := bnd _ (hβ₂ d d')
    exact ⟨M, fun g hg => by rw [hD₂ d d']; exact hM g hg⟩
  choose M₂ hM₂ using b2

  let B₁ : ℝ := max (M₁ .H) (max (M₁ .E) (M₁ .Fm))
  let B₂ : ℝ := max (max (M₂ .H .H) (max (M₂ .H .E) (M₂ .H .Fm)))
    (max (max (M₂ .E .H) (max (M₂ .E .E) (M₂ .E .Fm))) (max (M₂ .Fm .H) (max (M₂ .Fm .E) (M₂ .Fm .Fm))))
  have hB₁ : ∀ d : ArchDir, M₁ d ≤ B₁ := by
    intro d; cases d <;> simp only [B₁, le_max_iff, le_refl, true_or, or_true]
  have hB₂ : ∀ d d' : ArchDir, M₂ d d' ≤ B₂ := by
    intro d d'; cases d <;> cases d' <;> simp only [B₂, le_max_iff, le_refl, true_or, or_true]
  refine ⟨hsm, hc1, hc2, max M₀ (max B₁ B₂), fun g hg => ⟨?_, fun d => ?_, fun d d' => ?_⟩⟩
  · calc ‖φ g‖ = ‖rightConv ℚ φ α g‖ := by rw [hφα]
      _ ≤ M₀ := hM₀ g hg
      _ ≤ max M₀ (max B₁ B₂) := le_max_left _ _
  · exact ((hM₁ d g hg).trans (hB₁ d)).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact ((hM₂ d d' g hg).trans (hB₂ d d')).trans ((le_max_right _ _).trans (le_max_right _ _))

end S_AutomorphicForm_continuous_archDerivAt_and_exists_bound_slab_of_isIsotypicCuspFormAt_of_rightConv_eq_rat
end P2MW
export P2MW.S_AutomorphicForm_continuous_archDerivAt_and_exists_bound_slab_of_isIsotypicCuspFormAt_of_rightConv_eq_rat (solution)
