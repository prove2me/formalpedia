-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.mem_iSup_isCuspConstituent_of_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_rightConv_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/e1822585-a2fa-5a57-84fd-77c9cea064f3

import Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep
import Theorems.Thm_AutomorphicForm_exists_isFactorizableTestFn_isArchBiFinite_rightConv_eq_smul_of_rightConv_eq_smul
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_orthogonal_isIrreducibleCuspSubrep_sum_eq_of_apply_eq_smul
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isCuspConstituent_forall_mem_iff_toCuspSubcarrier_mem_of_isIrreducibleCuspSubrep
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isCuspLift_rightConv_isCompactOperator
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_mem_cuspKFiniteSubmodule_of_mem_cuspMemberSubmodule_of_rightConv_eq_smul
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_isIsotypicCuspFormAt_of_mem_of_sub_mem_orthogonal
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_mem_cuspMemberSubmodule_toCuspSubcarrier_eq_rightConv_eq_smul
import Theorems.Thm_AutomorphicForm_mem_cuspKFiniteSubmodule_of_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_rightConv_eq_smul
import Theorems.Thm_AutomorphicForm_isotypicCuspSubmodule_eq_bot_of_nonpos
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_cuspKFiniteSubmodule_le_cuspKFiniteSubmodule_of_le_of_exists_ne_zero
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_hasModulus_of_isAutomorphicFnAt_of_continuous
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isSlabFundamentalDomain
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_cuspKFiniteSubmodule_le_cuspMemberSubmodule
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_eq_zero_of_toCarrier_eq_zero
import Theorems.Thm_AutomorphicForm_coversModCentre_of_le_of_lt_of_coversModCentre
import Theorems.Thm_AutomorphicForm_isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule
import Theorems.Thm_AutomorphicForm_rightConv_mem_archCutSubmodule_of_isArchBiFinite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_mem_iSup_isCuspConstituent_of_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_rightConv_eq_smul
p2m_attr_erase "instance" "AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv"
p2m_attr_erase "simp" "RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val"

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open NumberField.SiegelVolume
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ENNReal InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace SDGlue

variable (F : Type) [Field F] [NumberField F]

theorem isSmoothCuspAutomorphicFnAt_mono {D D' : Set (AdelicGL2 (𝓞 F) F)} (hsub : D' ⊆ D)
    (ξ : (⊤ : Subgroup (NumberField.AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (h : IsSmoothCuspAutomorphicFnAt F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ φ) : IsSmoothCuspAutomorphicFnAt F (productionPinsOf F D' (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ φ := by
  refine ⟨⟨?_, h.1.2⟩, h.2⟩
  have h1 := (lsXiMemberAt_iff (𝓞 F) F (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) ⊤ ξ D φ).mp h.1.1
  exact (lsXiMemberAt_iff (𝓞 F) F (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) ⊤ ξ D' φ).mpr
    ⟨h1.1, h1.2.mono_measure (Measure.restrict_mono hsub le_rfl)⟩

theorem cuspKFiniteSubmodule_mono {D D' : Set (AdelicGL2 (𝓞 F) F)} (hsub : D' ⊆ D)
    (ξ : (⊤ : Subgroup (NumberField.AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) :
    cuspKFiniteSubmodule F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ ≤ cuspKFiniteSubmodule F (productionPinsOf F D' (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ := by
  unfold cuspKFiniteSubmodule
  refine Submodule.span_mono fun φ hφ => ?_
  exact ⟨fun g => isSmoothCuspAutomorphicFnAt_mono F hsub ξ (hφ.1 g), hφ.2.1, hφ.2.2⟩

theorem isIsotypicCuspFormAt_mono {D D' : Set (AdelicGL2 (𝓞 F) F)} (hsub : D' ⊆ D)
    (ξ : (⊤ : Subgroup (NumberField.AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (N : Ideal (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (Ψ : HeckeEigensystem F ℂ) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (h : IsIsotypicCuspFormAt F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ N S Ψ φ) : IsIsotypicCuspFormAt F (productionPinsOf F D' (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ N S Ψ φ :=
  ⟨isSmoothCuspAutomorphicFnAt_mono F hsub ξ h.smoothCusp, h.continuous, h.level_invariant, h.hecke_eigen, h.central_eigen⟩

theorem isCuspSubrep_of_eq {D D' : Set (AdelicGL2 (𝓞 F) F)} (ξ : (⊤ : Subgroup (NumberField.AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (heq : cuspKFiniteSubmodule F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ = cuspKFiniteSubmodule F (productionPinsOf F D' (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ)
    {V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)} (h : IsCuspSubrep F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ V) : IsCuspSubrep F (productionPinsOf F D' (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ V :=
  ⟨heq ▸ h.le, h.rightTranslate_fin_mem, h.rightTranslate_arch_mem, h.rightConv_mem⟩

theorem isCuspConstituent_of_eq {D D' : Set (AdelicGL2 (𝓞 F) F)} (ξ : (⊤ : Subgroup (NumberField.AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (heq : cuspKFiniteSubmodule F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ = cuspKFiniteSubmodule F (productionPinsOf F D' (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ)
    {V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)} (h : IsCuspConstituent F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ V) : IsCuspConstituent F (productionPinsOf F D' (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ V :=
  ⟨isCuspSubrep_of_eq F ξ heq h.1, h.2.1, fun W hW hWV => h.2.2 W (isCuspSubrep_of_eq F ξ heq.symm hW) hWV⟩

theorem window_mono (c u d₁ d₂ d₁' : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)) (hle : d₁ ≤ d₁') :
    (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁' d₂) ⊆ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) := by
  refine Set.iUnion₂_mono fun x _ => Set.image_mono fun g hg => ?_
  obtain ⟨h1, h2, h3, h4⟩ := mem_centreCutSiegelSet_iff.mp hg
  exact mem_centreCutSiegelSet_iff.mpr ⟨h1, h2, h3, fun w => ⟨hle.trans (h4 w).1, (h4 w).2⟩⟩

theorem isotypicCuspSubmodule_mono {D D' : Set (AdelicGL2 (𝓞 F) F)} (hsub : D' ⊆ D)
    (ξ : (⊤ : Subgroup (NumberField.AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (N : Ideal (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (Ψ : HeckeEigensystem F ℂ) :
    isotypicCuspSubmodule F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ N S Ψ ≤ isotypicCuspSubmodule F (productionPinsOf F D' (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ N S Ψ := by
  unfold isotypicCuspSubmodule
  exact Submodule.span_mono fun φ hφ => isIsotypicCuspFormAt_mono F hsub ξ N S Ψ hφ

theorem cuspConstituentMeets_of_le {D D' : Set (AdelicGL2 (𝓞 F) F)}
    (ξ : (⊤ : Subgroup (NumberField.AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (N : Ideal (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (Ψ : HeckeEigensystem F ℂ) {V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)}
    (hle : V ≤ cuspKFiniteSubmodule F (productionPinsOf F D' (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ)
    (h : CuspConstituentMeets F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ N S Ψ V) :
    CuspConstituentMeets F (productionPinsOf F D' (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ N S Ψ V := by
  obtain ⟨ψ, hψV, hψ0, hI⟩ := h
  have hsc := (AutomorphicForm.CuspidalConstituent.continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule F D' _ _ ξ ψ (hle hψV)).2 1
  have e1 : rightTranslate F 1 ψ = ψ := by funext x; rw [rightTranslate_apply, mul_one]
  rw [e1] at hsc
  exact ⟨ψ, hψV, hψ0, ⟨hsc, hI.continuous, hI.level_invariant, hI.hecke_eigen, hI.central_eigen⟩⟩

theorem false_of_coversModCentre_of_nonpos (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)) (hd₂ : d₂ ≤ 0)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) : False := by
  obtain ⟨γ, z, hmem⟩ := hcov 1
  simp only [Set.mem_iUnion, Set.mem_image] at hmem
  obtain ⟨x, -, g, hg, -⟩ := hmem
  obtain ⟨v₀⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace F))
  have h := ((mem_centreCutSiegelSet_iff.mp hg).2.2.2 v₀).2
  exact absurd (h.trans hd₂) (not_le.mpr (NumberField.AdelicVolume.archDetNorm_pos v₀ g))

end SDGlue

theorem core
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁)
    (hd : d₁ < d₂) (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (tys : AutomorphicForm.ArchTypeFamily F) (Ψ : HeckeEigensystem F ℂ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) (lam : ℂ) (hlam : lam ≠ 0)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : φ ∈ isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ N S Ψ ⊓ archCutSubmodule F tys)
    (heig : rightConv F φ f = lam • φ) :
    φ ∈ ⨆ (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
        (_ : IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ V ∧ CuspConstituentMeets F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ N S Ψ V ∧
              V ⊓ archCutSubmodule F tys ≠ ⊥), V := by
  classical
  by_cases hφ0 : φ = 0
  · rw [hφ0]; exact Submodule.zero_mem _

  have hφI : IsIsotypicCuspFormAt F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ N S Ψ φ := AutomorphicForm.isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule F _ _ _ ξ N S Ψ φ hφ.1 hφ0
  have hφc : Continuous φ := hφI.continuous

  obtain ⟨f', hf', hft', heig'⟩ := AutomorphicForm.exists_isFactorizableTestFn_isArchBiFinite_rightConv_eq_smul_of_rightConv_eq_smul F tys φ hφc hφ.2 f hf lam heig

  have hφK := AutomorphicForm.mem_cuspKFiniteSubmodule_of_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_rightConv_eq_smul F c u d₁ d₂ T hc hd₁ hd hcov ξ N S Ψ tys f' hf' lam hlam φ hφ heig'
  obtain ⟨α, β, Φ₀, hΦ₀⟩ := AutomorphicForm.CuspidalSpectrum.exists_isSlabFundamentalDomain F
  have hKle := AutomorphicForm.CuspidalSpectrum.cuspKFiniteSubmodule_le_cuspMemberSubmodule F c u d₁ d₂ T hc hd₁ hd hcov ξ hΦ₀
  have hφm : φ ∈ cuspMemberSubmodule F Φ₀ ξ := hKle hφK

  obtain ⟨σ, hσ⟩ := AutomorphicForm.CuspidalSpectrum.exists_hasModulus_of_isAutomorphicFnAt_of_continuous F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) ξ φ hφI.smoothCusp.1.1 hφc hφ0

  obtain ⟨Tc, hTc, hcpt⟩ := AutomorphicForm.CuspidalSpectrum.exists_isCuspLift_rightConv_isCompactOperator F hΦ₀ σ ξ hσ f' hf'
  have hconvm : rightConv F φ f' ∈ cuspMemberSubmodule F Φ₀ ξ := by
    rw [heig']; exact Submodule.smul_mem _ _ hφm
  have hv : Tc (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφm⟩) = lam • toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφm⟩ := by
    rw [hTc ⟨φ, hφm⟩ hconvm]
    have e : (⟨rightConv F φ f', hconvm⟩ : ↥(cuspMemberSubmodule F Φ₀ ξ)) = lam • ⟨φ, hφm⟩ := Subtype.ext heig'
    rw [e, map_smul]

  obtain ⟨n, Mi, vs, hirr, horth, heigen, hsum⟩ :=
    AutomorphicForm.CuspidalSpectrum.exists_orthogonal_isIrreducibleCuspSubrep_sum_eq_of_apply_eq_smul F hΦ₀ σ ξ hσ f' hf' tys hft' Tc hTc hcpt lam hlam _ hv

  have hrep : ∀ i : Fin n, ∃ (ψ : AdelicGL2 (𝓞 F) F → ℂ) (hψ : ψ ∈ cuspMemberSubmodule F Φ₀ ξ),
      toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψ⟩ = vs i ∧ rightConv F ψ f' = lam • ψ := fun i =>
    AutomorphicForm.CuspidalSpectrum.exists_mem_cuspMemberSubmodule_toCuspSubcarrier_eq_rightConv_eq_smul F hΦ₀ σ ξ hσ f' hf' Tc hTc lam hlam (vs i) (heigen i).2
  choose ψs hψm hψcl hψeig using hrep
  have hψK : ∀ i, ψs i ∈ cuspKFiniteSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ := fun i =>
    AutomorphicForm.CuspidalSpectrum.mem_cuspKFiniteSubmodule_of_mem_cuspMemberSubmodule_of_rightConv_eq_smul F c u d₁ d₂ T hc hd₁ hd hcov ξ hΦ₀ tys f' hf' hft' lam hlam (ψs i) (hψm i) (hψeig i)
  have hV : ∀ i, ∃ V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ V ∧
      ∀ ψ, ψ ∈ V ↔ ψ ∈ cuspKFiniteSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ ∧
        ∃ h : ψ ∈ cuspMemberSubmodule F Φ₀ ξ, toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, h⟩ ∈ Mi i := fun i =>
    AutomorphicForm.CuspidalSpectrum.exists_isCuspConstituent_forall_mem_iff_toCuspSubcarrier_mem_of_isIrreducibleCuspSubrep F c u d₁ d₂ T hc hd₁ hd hcov ξ σ hσ hΦ₀ (Mi i) (hirr i)
  choose Vs hVc hVmem using hV
  have hψMi : ∀ i, toCuspSubcarrier F hΦ₀ σ ξ ⟨ψs i, hψm i⟩ ∈ Mi i := fun i => by rw [hψcl i]; exact (heigen i).1
  have hψV : ∀ i, ψs i ∈ Vs i := fun i => (hVmem i (ψs i)).mpr ⟨hψK i, hψm i, hψMi i⟩

  have hperp : ∀ i, toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφm⟩ - toCuspSubcarrier F hΦ₀ σ ξ ⟨ψs i, hψm i⟩ ∈ (Mi i)ᗮ := by
    intro i
    have e : toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφm⟩ - toCuspSubcarrier F hΦ₀ σ ξ ⟨ψs i, hψm i⟩ = ∑ j ∈ Finset.univ.erase i, vs j := by
      rw [hψcl i, hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), add_sub_cancel_left]
    rw [e]
    refine Submodule.sum_mem _ (fun j hj => ?_)
    have hne : i ≠ j := fun h => (Finset.ne_of_mem_erase hj) h.symm
    exact (horth hne).symm.le (heigen j).1

  have hmeets : ∀ i, IsIsotypicCuspFormAt F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ N S Ψ (ψs i) := fun i =>
    AutomorphicForm.CuspidalSpectrum.isIsotypicCuspFormAt_of_mem_of_sub_mem_orthogonal F c u d₁ d₂ T hc hd₁ hd hcov ξ σ hσ hΦ₀ N S Ψ (Mi i) (hirr i).isClosedCuspSubrep
      φ hφI hφm (ψs i) (hψK i) (hψm i) (hψMi i) (hperp i)

  have hφsum : φ = ∑ i, ψs i := by
    have hSm : (∑ i, ψs i) ∈ cuspMemberSubmodule F Φ₀ ξ := Submodule.sum_mem _ (fun i _ => hψm i)
    have hsub : φ - ∑ i, ψs i ∈ contMemberSubmodule F Φ₀ ξ :=
      ⟨(memberSubmodule F Φ₀ ξ).sub_mem hφm.1.1.1 hSm.1.1.1, hφc.sub hSm.2⟩
    have hcl : toCuspSubcarrier F hΦ₀ σ ξ ⟨∑ i, ψs i, hSm⟩ = ∑ i, toCuspSubcarrier F hΦ₀ σ ξ ⟨ψs i, hψm i⟩ := by
      have e : (⟨∑ i, ψs i, hSm⟩ : ↥(cuspMemberSubmodule F Φ₀ ξ)) = ∑ i, (⟨ψs i, hψm i⟩ : ↥(cuspMemberSubmodule F Φ₀ ξ)) := by
        apply Subtype.ext; simp
      rw [e, map_sum]
    have h0 : toCarrier F hΦ₀ σ ξ ⟨φ - ∑ i, ψs i, hsub.1⟩ = 0 := by
      have e1 : (⟨φ - ∑ i, ψs i, hsub.1⟩ : ↥(memberSubmodule F Φ₀ ξ)) = ⟨φ, hφm.1.1.1⟩ - ⟨∑ i, ψs i, hSm.1.1.1⟩ := rfl
      have e2 : (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφm⟩ : Carrier F Φ₀ σ) = toCarrier F hΦ₀ σ ξ ⟨φ, hφm.1.1.1⟩ := rfl
      have e3 : (toCuspSubcarrier F hΦ₀ σ ξ ⟨∑ i, ψs i, hSm⟩ : Carrier F Φ₀ σ) = toCarrier F hΦ₀ σ ξ ⟨∑ i, ψs i, hSm.1.1.1⟩ := rfl
      have e4 : toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφm⟩ = toCuspSubcarrier F hΦ₀ σ ξ ⟨∑ i, ψs i, hSm⟩ := by
        rw [hcl, hsum]; exact Finset.sum_congr rfl (fun i _ => (hψcl i).symm)
      rw [e1, map_sub, ← e2, ← e3, e4, sub_self]
    have := AutomorphicForm.CuspidalSpectrum.eq_zero_of_toCarrier_eq_zero F hΦ₀ σ ξ (φ - ∑ i, ψs i) hsub h0
    rwa [sub_eq_zero] at this

  rw [hφsum]
  refine Submodule.sum_mem _ (fun i _ => ?_)
  by_cases hψ0 : ψs i = 0
  · rw [hψ0]; exact Submodule.zero_mem _
  have hψt : ψs i ∈ archCutSubmodule F tys := by
    have e : ψs i = lam⁻¹ • rightConv F (ψs i) f' := by rw [hψeig i, smul_smul, inv_mul_cancel₀ hlam, one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (AutomorphicForm.rightConv_mem_archCutSubmodule_of_isArchBiFinite F tys (ψs i) (hψm i).2 f' hf' hft')
  have hcut : Vs i ⊓ archCutSubmodule F tys ≠ ⊥ := by
    intro h
    have : ψs i ∈ Vs i ⊓ archCutSubmodule F tys := Submodule.mem_inf.mpr ⟨hψV i, hψt⟩
    rw [h] at this
    exact hψ0 ((Submodule.mem_bot ℂ).mp this)
  exact Submodule.mem_iSup_of_mem (Vs i)
    (Submodule.mem_iSup_of_mem ⟨hVc i, ⟨ψs i, hψV i, hψ0, hmeets i⟩, hcut⟩ (hψV i))

theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂) (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (tys : AutomorphicForm.ArchTypeFamily F) (Ψ : HeckeEigensystem F ℂ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) (lam : ℂ) (hlam : lam ≠ 0)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : φ ∈ isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ ⊓ archCutSubmodule F tys)
    (heig : rightConv F φ f = lam • φ) :
    φ ∈ ⨆ (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
        (_ : IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ V ∧ CuspConstituentMeets F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ V ∧
              V ⊓ archCutSubmodule F tys ≠ ⊥), V := by
  classical
  by_cases hφ0 : φ = 0
  · rw [hφ0]; exact Submodule.zero_mem _

  by_cases hcpos : 0 < c
  swap
  · exfalso
    have hbot := AutomorphicForm.isotypicCuspSubmodule_eq_bot_of_nonpos F c u d₁ d₂ T (not_lt.mp hcpos) hd hcov ξ N S Ψ
    have : φ ∈ (⊥ : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) := hbot ▸ hφ.1
    exact hφ0 ((Submodule.mem_bot ℂ).mp this)
  by_cases hd₁pos : 0 < d₁
  · exact core F c u d₁ d₂ T hcpos hd₁pos hd hcov ξ N hN S tys Ψ f hf lam hlam φ hφ heig

  have hd₂ : 0 < d₂ := by
    by_contra hle
    exact SDGlue.false_of_coversModCentre_of_nonpos F c u d₁ d₂ T (not_lt.mp hle) hcov
  set d₁' : ℝ := d₂ / 2 with hd₁'def
  have hle : d₁ ≤ d₁' := by rw [hd₁'def]; linarith [not_lt.mp hd₁pos]
  have hd₁' : 0 < d₁' := by rw [hd₁'def]; linarith
  have hlt : d₁' < d₂ := by rw [hd₁'def]; linarith
  have hcov' := AutomorphicForm.coversModCentre_of_le_of_lt_of_coversModCentre F c u d₁ d₂ d₁' T hle hlt hcov
  have hsub := SDGlue.window_mono F c u d₁ d₂ d₁' T hle

  have hφ' : φ ∈ isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁' d₂) (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ N S Ψ ⊓ archCutSubmodule F tys :=
    Submodule.mem_inf.mpr ⟨SDGlue.isotypicCuspSubmodule_mono F hsub ξ N S Ψ hφ.1, hφ.2⟩
  have hcore := core F c u d₁' d₂ T hcpos hd₁' hlt hcov' ξ N hN S tys Ψ f hf lam hlam φ hφ' heig

  have hφI : IsIsotypicCuspFormAt F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ N S Ψ φ := AutomorphicForm.isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule F _ _ _ ξ N S Ψ φ hφ.1 hφ0
  have heq : cuspKFiniteSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁' d₂) (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ = cuspKFiniteSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ :=
    le_antisymm
      (AutomorphicForm.CuspidalConstituent.cuspKFiniteSubmodule_le_cuspKFiniteSubmodule_of_le_of_exists_ne_zero F c u d₁ d₂ d₁' T hcpos hle hd₁' hlt hcov ξ ⟨φ, hφI.smoothCusp.1.1, hφI.continuous, hφ0⟩)
      (SDGlue.cuspKFiniteSubmodule_mono F hsub ξ)

  have hmono : (⨆ (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
        (_ : IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁' d₂) (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ V ∧ CuspConstituentMeets F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁' d₂) (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ N S Ψ V ∧
              V ⊓ archCutSubmodule F tys ≠ ⊥), V) ≤
      ⨆ (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
        (_ : IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ V ∧ CuspConstituentMeets F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ N S Ψ V ∧
              V ⊓ archCutSubmodule F tys ≠ ⊥), V :=
    iSup₂_mono' fun V hV =>
      ⟨V, ⟨SDGlue.isCuspConstituent_of_eq F ξ heq hV.1,
        SDGlue.cuspConstituentMeets_of_le F ξ N S Ψ (hV.1.1.le.trans heq.le) hV.2.1, hV.2.2⟩, le_rfl⟩
  exact hmono hcore

end S_AutomorphicForm_CuspidalConstituent_mem_iSup_isCuspConstituent_of_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_rightConv_eq_smul
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_mem_iSup_isCuspConstituent_of_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_rightConv_eq_smul (solution)
