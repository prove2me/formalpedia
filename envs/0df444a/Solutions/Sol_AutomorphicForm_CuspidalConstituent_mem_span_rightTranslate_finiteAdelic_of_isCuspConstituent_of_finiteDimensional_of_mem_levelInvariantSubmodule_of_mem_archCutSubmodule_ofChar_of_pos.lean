-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.mem_span_rightTranslate_finiteAdelic_of_isCuspConstituent_of_finiteDimensional_of_mem_levelInvariantSubmodule_of_mem_archCutSubmodule_ofChar_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/31578e7b-ea6c-57c6-88ca-d6908ac8afae

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_isCuspSubrep_span_cyclic_and_mem_and_le
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_mem_span_rightTranslate_sup_span_rightConv_spherical_of_mem_span_cyclic_of_mem_archCutSubmodule_ofChar
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_isFactorizableTestFn_indicator_and_rightConv_mem_span_rightTranslate_rightConv_indicator_of_mem_levelInvariantSubmodule
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_forall_rightConv_eq_smul_of_isCuspConstituent_of_finiteDimensional_ofChar_of_pos
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_mem_span_rightTranslate_finiteAdelic_of_isCuspConstituent_of_finiteDimensional_of_mem_levelInvariantSubmodule_of_mem_archCutSubmodule_ofChar_of_pos
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent

theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hV : IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ V)
    (hadm : ∀ (N : Ideal (𝓞 F)) (tys : ArchTypeFamily F), N ≠ ⊥ →
      FiniteDimensional ℂ
        ↥(V ⊓ levelInvariantSubmodule F
              (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F))
              N ⊓
            archCutSubmodule F tys))
    (hreal : ∀ w : InfinitePlace F, w.IsReal)
    (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (Ψ₁ Ψ₂ : AdelicGL2 (𝓞 F) F → ℂ) (h₁ : Ψ₁ ∈ V) (h₂ : Ψ₂ ∈ V)
    (hχ₁ : Ψ₁ ∈ archCutSubmodule F (ArchTypeFamily.ofChar F χ))
    (hχ₂ : Ψ₂ ∈ archCutSubmodule F (ArchTypeFamily.ofChar F χ))
    (N₁ : Ideal (𝓞 F)) (hN₁ : N₁ ≠ ⊥)
    (h₁N : Ψ₁ ∈ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N₁)
    (hne : Ψ₁ ≠ 0) :
    Ψ₂ ∈ Submodule.span ℂ
      ((fun g => rightTranslate F g Ψ₁) '' (finiteAdelicGL2Subgroup F : Set (AdelicGL2 (𝓞 F) F))) := by
  classical

  have hR5a := AutomorphicForm.CuspidalConstituent.isCuspSubrep_span_cyclic_and_mem_and_le F
    (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
    (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)
    ξ V hV.1 Ψ₁ h₁
  have hCV := hR5a.2.2.2 hV hne
  have h₂C : Ψ₂ ∈ Submodule.span ℂ
      {ψ | ∃ g ∈ finiteAdelicGL2Subgroup F, ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range),
        ψ = rightTranslate F (g * k) Ψ₁ ∨
        ∃ (f : AdelicGL2 (𝓞 F) F → ℂ) (tys : ArchTypeFamily F), IsFactorizableTestFn F f ∧ IsArchBiFinite F tys f ∧
          ψ = rightTranslate F (g * k) (rightConv F Ψ₁ f)} := by
    rw [hCV]; exact h₂

  have hΨ₁c : Continuous Ψ₁ := by
    have hmem := hV.1.le h₁
    refine Submodule.span_induction (p := fun φ _ => Continuous φ) ?_ ?_ ?_ ?_ hmem
    · rintro φ ⟨-, hcont, -⟩; exact hcont
    · exact continuous_const
    · intro a b _ _ ha hb; exact ha.add hb
    · intro a b _ hb; exact hb.const_smul a

  have hb := AutomorphicForm.CuspidalConstituent.mem_span_rightTranslate_sup_span_rightConv_spherical_of_mem_span_cyclic_of_mem_archCutSubmodule_ofChar F χ Ψ₁ Ψ₂ hΨ₁c hχ₁ hχ₂ h₂C

  set Tspan : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
    Submodule.span ℂ ((fun g => rightTranslate F g Ψ₁) '' (finiteAdelicGL2Subgroup F : Set (AdelicGL2 (𝓞 F) F)))
    with hTspan
  have hTstab : ∀ g ∈ finiteAdelicGL2Subgroup F, ∀ φ ∈ Tspan, rightTranslate F g φ ∈ Tspan := by
    intro g hg φ hφ
    refine Submodule.span_induction (p := fun φ _ => rightTranslate F g φ ∈ Tspan) ?_ ?_ ?_ ?_ hφ
    · rintro _ ⟨g', hg', rfl⟩
      rw [rightTranslate_rightTranslate]
      exact Submodule.subset_span ⟨g * g', mul_mem hg hg', rfl⟩
    · show rightTranslate F g 0 ∈ Tspan
      rw [rightTranslate_zero]; exact Tspan.zero_mem
    · intro a b _ _ ha hb
      show rightTranslate F g (a + b) ∈ Tspan
      rw [rightTranslate_add]; exact Tspan.add_mem ha hb
    · intro r a _ ha
      show rightTranslate F g (r • a) ∈ Tspan
      rw [rightTranslate_smul]; exact Tspan.smul_mem r ha
  have hΨ₁T : Ψ₁ ∈ Tspan := by
    refine Submodule.subset_span ⟨1, one_mem _, ?_⟩
    funext x; simp [rightTranslate]

  have hB : Submodule.span ℂ
        {ψ | ∃ g ∈ finiteAdelicGL2Subgroup F,
          ∃ (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ),
            IsArchTestFactor F fa ∧ IsArchFactorBiFinite F (ArchTypeFamily.ofChar F χ) fa ∧
            (∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (InfiniteAdeleRing F)),
              fa (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) = fa x) ∧
            IsFinTestFactor F ff ∧
            ψ = rightTranslate F g (rightConv F Ψ₁
              (fun y => fa (AdelicLevel.glArch (𝓞 F) F y) * ff (AdelicLevel.glFin (𝓞 F) F y)))} ≤ Tspan := by
    rw [Submodule.span_le]
    rintro ψ ⟨g, hg, fa, ff, hfa, hbf, hconj, hff, rfl⟩

    obtain ⟨hf₀, hmem⟩ := AutomorphicForm.CuspidalConstituent.isFactorizableTestFn_indicator_and_rightConv_mem_span_rightTranslate_rightConv_indicator_of_mem_levelInvariantSubmodule F
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)
      N₁ hN₁ Ψ₁ hΨ₁c h₁N fa ff hfa hff

    obtain ⟨lam, hlam⟩ :=
      AutomorphicForm.CuspidalConstituent.exists_forall_rightConv_eq_smul_of_isCuspConstituent_of_finiteDimensional_ofChar_of_pos F
        c u d₁ d₂ T hc hd₁ hd hcov ξ N₁ hN₁ V hV hreal χ (hadm N₁ _ hN₁) _ hf₀ ⟨fa, hfa, hbf, hconj, fun _ => rfl⟩
    have hscal := hlam Ψ₁ ⟨⟨h₁, h₁N⟩, hχ₁⟩

    have hin : rightConv F Ψ₁ (fun y => fa (AdelicLevel.glArch (𝓞 F) F y) * ff (AdelicLevel.glFin (𝓞 F) F y)) ∈ Tspan := by
      refine (Submodule.span_le.mpr ?_) hmem
      rintro _ ⟨g', hg', rfl⟩
      show rightTranslate F g' (rightConv F Ψ₁ _) ∈ Tspan
      rw [hscal, rightTranslate_smul]
      exact Tspan.smul_mem lam (hTstab g' hg' Ψ₁ hΨ₁T)
    exact hTstab g hg _ hin

  exact (sup_le le_rfl hB) hb

end S_AutomorphicForm_CuspidalConstituent_mem_span_rightTranslate_finiteAdelic_of_isCuspConstituent_of_finiteDimensional_of_mem_levelInvariantSubmodule_of_mem_archCutSubmodule_ofChar_of_pos
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_mem_span_rightTranslate_finiteAdelic_of_isCuspConstituent_of_finiteDimensional_of_mem_levelInvariantSubmodule_of_mem_archCutSubmodule_ofChar_of_pos (solution)
