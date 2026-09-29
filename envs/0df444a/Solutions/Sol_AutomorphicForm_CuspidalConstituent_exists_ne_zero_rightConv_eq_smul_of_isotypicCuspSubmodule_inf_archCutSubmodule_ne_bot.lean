-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.exists_ne_zero_rightConv_eq_smul_of_isotypicCuspSubmodule_inf_archCutSubmodule_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/6ce5dd39-8d08-5fb0-85bf-d0f6e72a533e

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchSpherical
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_norm_toCarrier_sub_lt
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_slice_sub_mem_eigenspace_orthogonal
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_hasModulus_of_isAutomorphicFnAt_of_continuous
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_isotypicCuspSubmodule_le_cuspMemberSubmodule
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isSlabFundamentalDomain
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_eq_zero_of_toCarrier_eq_zero
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isCompactOperator_isSymmetric_lift_rightConv
import Theorems.Thm_ContinuousLinearMap_orthogonal_iSup_eigenspace_ne_zero_eq_ker
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_exists_ne_zero_rightConv_eq_smul_of_isotypicCuspSubmodule_inf_archCutSubmodule_ne_bot
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"
p2m_attr_erase "simp" "AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg"
p2m_attr_erase "simp" "RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace BenchES

variable {F : Type} [Field F] [NumberField F]

theorem iso_le_level (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ) (N : Ideal (𝓞 F))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψ : HeckeEigensystem F ℂ) :
    isotypicCuspSubmodule F pins ξ N S Ψ ≤ levelInvariantSubmodule F pins N :=
  Submodule.span_le.mpr fun _ hφ => hφ.level_invariant

theorem iso_le_member (D : Set (AdelicGL2 (𝓞 F) F)) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (N : Ideal (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψ : HeckeEigensystem F ℂ) :
    isotypicCuspSubmodule F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ N S Ψ ≤ memberSubmodule F D ξ :=
  Submodule.span_le.mpr fun _ hφ => hφ.smoothCusp.1.1

theorem exists_slice (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁)
    (hd : d₁ < d₂) (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (tys : AutomorphicForm.ArchTypeFamily F) (Ψ : HeckeEigensystem F ℂ)
    (hX : isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ ⊓ archCutSubmodule F tys ≠ ⊥) :
    ∃ (f : AdelicGL2 (𝓞 F) F → ℂ) (_ : IsFactorizableTestFn F f) (lam : ℂ) (_ : lam ≠ 0)
      (ψ : AdelicGL2 (𝓞 F) F → ℂ),
      ψ ∈ isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ ⊓ archCutSubmodule F tys ∧
      ψ ≠ 0 ∧ rightConv F ψ f = lam • ψ := by
  classical
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hX
  have hxi : x ∈ isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ := (Submodule.mem_inf.mp hx).1
  have hxt : x ∈ archCutSubmodule F tys := (Submodule.mem_inf.mp hx).2
  obtain ⟨σ, hσ⟩ := AutomorphicForm.CuspidalSpectrum.exists_hasModulus_of_isAutomorphicFnAt_of_continuous
    F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) ξ x (iso_le_member (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) ξ N S Ψ hxi) (continuous_of_mem_isotypicCuspSubmodule hxi) hx0
  obtain ⟨α, β, Φ₀, hΦ₀⟩ := AutomorphicForm.CuspidalSpectrum.exists_isSlabFundamentalDomain F
  have hxm : x ∈ cuspMemberSubmodule F Φ₀ ξ :=
    AutomorphicForm.CuspidalSpectrum.isotypicCuspSubmodule_le_cuspMemberSubmodule F c u d₁ d₂ T hd hcov ξ N S Ψ hΦ₀ hxi
  have hxU : x ∈ levelInvariantSubmodule F (fdPins F Φ₀) N := iso_le_level (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ hxi
  haveI : CompleteSpace ↥(cuspSubcarrier F hΦ₀ σ ξ) := by
    unfold cuspSubcarrier
    exact (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  set L := toCuspSubcarrier F hΦ₀ σ ξ with hL
  by_contra hcon

  have hsmall : ∀ ε : ℝ, 0 < ε → ‖L ⟨x, hxm⟩‖ < ε := by
    intro ε hε
    obtain ⟨f, hf, hsph, hflat, hxf, hnorm⟩ := AutomorphicForm.CuspidalSpectrum.exists_norm_toCarrier_sub_lt
      F hΦ₀ σ ξ hσ N hN tys x hxm hxU hxt ε hε
    obtain ⟨Tc, hcpt, hsymm, hcomm⟩ :=
      AutomorphicForm.CuspidalSpectrum.exists_isCompactOperator_isSymmetric_lift_rightConv F hΦ₀ σ ξ hσ f hf hflat

    have horth : ∀ (μ : ℂ) (hμ : μ ≠ 0),
        L ⟨x, hxm⟩ ∈ (Module.End.eigenspace (Tc : Module.End ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) μ)ᗮ := by
      intro μ hμ
      obtain ⟨ψ, hψm, hψiso, hψeig, hψorth⟩ :=
        AutomorphicForm.CuspidalSpectrum.exists_slice_sub_mem_eigenspace_orthogonal F c u d₁ d₂ T hc hd₁ hd hcov ξ N hN S tys Ψ
          x hx hΦ₀ σ hσ hxm f hf hsph hflat Tc hcomm μ hμ
      have hψ0 : ψ = 0 := by
        by_contra hne
        exact hcon ⟨f, hf, μ, hμ, ψ, hψiso, hne, hψeig⟩
      have h0 : toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψm⟩ = 0 := by
        have : (⟨ψ, hψm⟩ : ↥(cuspMemberSubmodule F Φ₀ ξ)) = 0 := Subtype.ext hψ0
        rw [this, map_zero]
      refine (Submodule.mem_orthogonal' _ _).mpr fun y hy => ?_
      have h1 := hψorth y hy
      rw [h0, sub_zero] at h1
      exact h1
    have hker : L ⟨x, hxm⟩ ∈ (⨆ (μ : ℂ) (_ : μ ≠ 0), Module.End.eigenspace (Tc : Module.End ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) μ)ᗮ := by
      rw [← Submodule.iInf_orthogonal, Submodule.mem_iInf]
      intro μ
      by_cases hμ : μ ≠ 0
      · rw [iSup_pos hμ]; exact horth μ hμ
      · rw [iSup_neg hμ, Submodule.bot_orthogonal_eq_top]; exact Submodule.mem_top
    have hT0 : Tc (L ⟨x, hxm⟩) = 0 := by
      rw [ContinuousLinearMap.orthogonal_iSup_eigenspace_ne_zero_eq_ker hcpt hsymm] at hker
      exact hker
    have hTx : Tc (L ⟨x, hxm⟩) = L ⟨rightConv F x f, hxf⟩ := hcomm ⟨x, hxm⟩ hxf
    have : ‖L ⟨x, hxm⟩‖ = ‖L ⟨x, hxm⟩ - L ⟨rightConv F x f, hxf⟩‖ := by
      rw [← hTx, hT0, sub_zero]
    rw [hL] at this ⊢
    rw [this]
    exact hnorm
  have hLx : L ⟨x, hxm⟩ = 0 := by
    rw [← norm_eq_zero]
    exact le_antisymm (le_of_forall_pos_lt_add fun ε hε => by simpa using hsmall ε hε) (norm_nonneg _)
  have hsub : toCarrier F hΦ₀ σ ξ ⟨x, hxm.1.1.1⟩ = 0 := by
    have h2 := congrArg (fun z : ↥(cuspSubcarrier F hΦ₀ σ ξ) => (z : Carrier F Φ₀ σ)) hLx
    simpa [hL, toCuspSubcarrier_apply_coe] using h2
  exact hx0 (AutomorphicForm.CuspidalSpectrum.eq_zero_of_toCarrier_eq_zero F hΦ₀ σ ξ x ⟨hxm.1.1.1, hxm.2⟩ hsub)

end BenchES

end

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁)
    (hd : d₁ < d₂) (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (tys : AutomorphicForm.ArchTypeFamily F) (Ψ : HeckeEigensystem F ℂ)
    (hX : isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ ⊓ archCutSubmodule F tys ≠ ⊥) :
    ∃ (f : AdelicGL2 (𝓞 F) F → ℂ) (_ : IsFactorizableTestFn F f) (lam : ℂ) (_ : lam ≠ 0)
      (ψ : AdelicGL2 (𝓞 F) F → ℂ),
      ψ ∈ isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ ⊓ archCutSubmodule F tys ∧
      ψ ≠ 0 ∧ rightConv F ψ f = lam • ψ :=
  BenchES.exists_slice c u d₁ d₂ T hc hd₁ hd hcov ξ N hN S tys Ψ hX

end S_AutomorphicForm_CuspidalConstituent_exists_ne_zero_rightConv_eq_smul_of_isotypicCuspSubmodule_inf_archCutSubmodule_ne_bot
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_exists_ne_zero_rightConv_eq_smul_of_isotypicCuspSubmodule_inf_archCutSubmodule_ne_bot (solution)
