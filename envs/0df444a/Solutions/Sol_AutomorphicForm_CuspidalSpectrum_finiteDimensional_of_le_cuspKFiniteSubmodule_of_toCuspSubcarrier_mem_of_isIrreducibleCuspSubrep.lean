-- Prove2me | solution 1 for AutomorphicForm.CuspidalSpectrum.finiteDimensional_of_le_cuspKFiniteSubmodule_of_toCuspSubcarrier_mem_of_isIrreducibleCuspSubrep
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/23553cec-22aa-54a6-98d7-f5bd22a0a62a

import Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_ArchSpherical
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_inf_invariants_le_iSup_isIrreducible_of_isCuspSubrep
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_rightConv_injOn_of_finiteDimensional_of_forall_apply_mul_eq
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isCompactOperator_isSymmetric_lift_rightConv
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_map_inf_orthogonal_eq_bot_or_le_of_isIrreducibleCuspSubrep
import Theorems.Thm_ContinuousLinearMap_le_ker_or_finiteDimensional_of_forall_inf_highPart_orthogonal
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_eq_zero_of_toCarrier_eq_zero
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_cuspKFiniteSubmodule_le_cuspMemberSubmodule
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_isCuspSubrep_cuspKFiniteSubmodule_inf_map_subtype_comap_toCuspSubcarrier_of_isClosedCuspSubrep
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_rightConv_mem_cuspMemberSubmodule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalSpectrum_finiteDimensional_of_le_cuspKFiniteSubmodule_of_toCuspSubcarrier_mem_of_isIrreducibleCuspSubrep
p2m_attr_erase "instance" "AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv"
p2m_attr_erase "simp" "RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace IrredAdmProof

variable {F : Type} [Field F] [NumberField F]

private theorem finiteDimensional_single {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) (hM : IsIrreducibleCuspSubrep F hΦ₀ σ ξ M)
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F)
    (τ : ∀ w : InfinitePlace F, ArchRepAt F w) (hirr : ∀ w, (τ w).ρ.IsIrreducible)
    (X : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hXc : X ≤ cuspMemberSubmodule F Φ₀ ξ)
    (hXM : ∀ (ψ : AdelicGL2 (𝓞 F) F → ℂ) (hψ : ψ ∈ X), toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hXc hψ⟩ ∈ M)
    (hXU : ∀ ψ ∈ X, ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U, ψ (g * k) = ψ g)
    (hXt : X ≤ archCutSubmodule F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F)) :
    FiniteDimensional ℂ ↥X := by
  classical
  by_cases hX0 : X = ⊥
  · rw [hX0]; infer_instance
  obtain ⟨x, hxX, hx0⟩ := (Submodule.ne_bot_iff X).mp hX0
  have hxc : x ∈ cuspMemberSubmodule F Φ₀ ξ := hXc hxX

  set L : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := Submodule.span ℂ {x} with hL
  haveI hLfd : FiniteDimensional ℂ ↥L := FiniteDimensional.span_of_finite ℂ (Set.finite_singleton x)
  have hLc : ∀ y ∈ L, Continuous y := by
    intro y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    exact hxc.2.const_smul a
  have hLU : ∀ y ∈ L, ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U, y (g * k) = y g := by
    intro y hy g k hk
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    simp only [Pi.smul_apply, hXU x hxX g k hk]
  have hLt : L ≤ archCutSubmodule F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F) :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (hXt hxX))
  obtain ⟨f, hf, hsph, hflat, hinj⟩ :=
    AutomorphicForm.CuspidalConstituent.exists_rightConv_injOn_of_finiteDimensional_of_forall_apply_mul_eq
      F U hU O hO hUO (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F) σ L hLfd hLc hLU hLt
  have hxf : rightConv F x f ≠ 0 := fun h => hx0 (hinj x (Submodule.subset_span rfl) h)
  have hxfm : rightConv F x f ∈ cuspMemberSubmodule F Φ₀ ξ :=
    AutomorphicForm.CuspidalSpectrum.rightConv_mem_cuspMemberSubmodule F hΦ₀ ξ f hf x hxc

  obtain ⟨Tc, hTc, hsymm, hcomm⟩ :=
    AutomorphicForm.CuspidalSpectrum.exists_isCompactOperator_isSymmetric_lift_rightConv F hΦ₀ σ ξ hσ f hf hflat

  have hdich := AutomorphicForm.CuspidalSpectrum.map_inf_orthogonal_eq_bot_or_le_of_isIrreducibleCuspSubrep
    F hΦ₀ σ ξ hσ M hM U hU O hO hUO τ hirr f hf hsph hflat Tc hsymm hcomm X hXc hXM hXU hXt

  haveI : CompleteSpace ↥(cuspSubcarrier F hΦ₀ σ ξ) := by
    have hcl : IsClosed ((cuspSubcarrier F hΦ₀ σ ξ : Submodule ℂ (Carrier F Φ₀ σ)) : Set (Carrier F Φ₀ σ)) := by
      unfold cuspSubcarrier; exact Submodule.isClosed_topologicalClosure _
    exact hcl.completeSpace_coe
  set φ : ↥X →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ) := (toCuspSubcarrier F hΦ₀ σ ξ).comp (Submodule.inclusion hXc) with hφ
  rcases ContinuousLinearMap.le_ker_or_finiteDimensional_of_forall_inf_highPart_orthogonal (𝕜 := ℂ) hTc hsymm
      (Submodule.map φ ⊤) hdich with hker | hfd
  ·
    exfalso
    have hxim : φ ⟨x, hxX⟩ ∈ Submodule.map φ ⊤ := Submodule.mem_map_of_mem trivial
    have h1 : Tc (φ ⟨x, hxX⟩) = 0 := LinearMap.mem_ker.mp (hker hxim)
    have h2 : φ ⟨x, hxX⟩ = toCuspSubcarrier F hΦ₀ σ ξ ⟨x, hxc⟩ := rfl
    rw [h2, hcomm ⟨x, hxc⟩ hxfm] at h1
    have h3 : toCarrier F hΦ₀ σ ξ ⟨rightConv F x f, hxfm.1.1.1⟩ = 0 := by
      have := congrArg (fun v : ↥(cuspSubcarrier F hΦ₀ σ ξ) => (v : Carrier F Φ₀ σ)) h1
      simpa [toCuspSubcarrier_apply_coe] using this
    exact hxf (AutomorphicForm.CuspidalSpectrum.eq_zero_of_toCarrier_eq_zero F hΦ₀ σ ξ (rightConv F x f)
      ⟨hxfm.1.1.1, hxfm.2⟩ h3)
  ·
    have hφinj : Function.Injective φ := by
      intro a b hab
      have h0 : φ (a - b) = 0 := by rw [map_sub, hab, sub_self]
      have hmem : ((a - b : ↥X) : AdelicGL2 (𝓞 F) F → ℂ) ∈ cuspMemberSubmodule F Φ₀ ξ := hXc (a - b).2
      have h3 : toCarrier F hΦ₀ σ ξ ⟨((a - b : ↥X) : AdelicGL2 (𝓞 F) F → ℂ), hmem.1.1.1⟩ = 0 := by
        have := congrArg (fun v : ↥(cuspSubcarrier F hΦ₀ σ ξ) => (v : Carrier F Φ₀ σ)) h0
        simp [toCuspSubcarrier_apply_coe] at this
        exact this
      have := AutomorphicForm.CuspidalSpectrum.eq_zero_of_toCarrier_eq_zero F hΦ₀ σ ξ _ ⟨hmem.1.1.1, hmem.2⟩ h3
      exact sub_eq_zero.mp (Subtype.ext this)
    haveI : FiniteDimensional ℂ ↥(LinearMap.range φ) := by rw [LinearMap.range_eq_map]; exact hfd
    exact LinearEquiv.finiteDimensional (LinearEquiv.ofInjective φ hφinj).symm

end IrredAdmProof

open IrredAdmProof in
theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (σ : ℝ) (hσ : HasModulus F ξ σ)
    {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) (hM : IsIrreducibleCuspSubrep F hΦ₀ σ ξ M)
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F)
    (tys : ArchTypeFamily F)
    (Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hYK : Y ≤ cuspKFiniteSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ)
    (hYM : ∀ ψ ∈ Y, ∃ h : ψ ∈ cuspMemberSubmodule F Φ₀ ξ, toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, h⟩ ∈ M)
    (hYU : ∀ ψ ∈ Y, ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U, ψ (g * k) = ψ g)
    (hYt : Y ≤ archCutSubmodule F tys) :
    FiniteDimensional ℂ ↥Y := by
  classical

  have hV := AutomorphicForm.CuspidalSpectrum.isCuspSubrep_cuspKFiniteSubmodule_inf_map_subtype_comap_toCuspSubcarrier_of_isClosedCuspSubrep
    F c u d₁ d₂ T hc hd₁ hd hcov ξ σ hσ hΦ₀ M hM.1
  set VM : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
    cuspKFiniteSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ ⊓
      Submodule.map (cuspMemberSubmodule F Φ₀ ξ).subtype (Submodule.comap (toCuspSubcarrier F hΦ₀ σ ξ) M) with hVM
  have hmem := AutomorphicForm.CuspidalSpectrum.cuspKFiniteSubmodule_le_cuspMemberSubmodule F c u d₁ d₂ T hc hd₁ hd hcov ξ hΦ₀

  obtain ⟨n, τs, hirr, hsplit⟩ :=
    AutomorphicForm.CuspidalConstituent.exists_inf_invariants_le_iSup_isIrreducible_of_isCuspSubrep
      F c u d₁ d₂ T ξ U hU O hO hUO tys VM hV

  have hYle : Y ≤ VM ⊓ Representation.invariants ((rightRegular F).comp U.subtype) ⊓ archCutSubmodule F tys := by
    intro ψ hψ
    obtain ⟨h, hMψ⟩ := hYM ψ hψ
    refine ⟨⟨⟨hYK hψ, ⟨⟨ψ, h⟩, hMψ, rfl⟩⟩, ?_⟩, hYt hψ⟩
    refine (Representation.mem_invariants _ _).mpr fun k => ?_
    funext g
    exact hYU ψ hψ g k k.2

  have hfd : ∀ j : Fin n, FiniteDimensional ℂ ↥(VM ⊓ Representation.invariants ((rightRegular F).comp U.subtype) ⊓
      archCutSubmodule F (⟨fun _ => 1, fun w _ => τs j w⟩ : AutomorphicForm.ArchTypeFamily F)) := by
    intro j
    set X := VM ⊓ Representation.invariants ((rightRegular F).comp U.subtype) ⊓
      archCutSubmodule F (⟨fun _ => 1, fun w _ => τs j w⟩ : AutomorphicForm.ArchTypeFamily F) with hX
    have hXc : X ≤ cuspMemberSubmodule F Φ₀ ξ := fun ψ hψ => hmem hψ.1.1.1
    refine finiteDimensional_single hΦ₀ σ ξ hσ M hM U hU O hO hUO (τs j) (hirr j) X hXc ?_ ?_ inf_le_right
    · intro ψ hψ
      obtain ⟨φ, hφM, hφψ⟩ := hψ.1.1.2
      have : (⟨ψ, hXc hψ⟩ : ↥(cuspMemberSubmodule F Φ₀ ξ)) = φ := Subtype.ext hφψ.symm
      rw [this]; exact hφM
    · intro ψ hψ g k hk
      have h := (Representation.mem_invariants _ _).mp hψ.1.2 ⟨k, hk⟩
      exact congrFun h g
  haveI := hfd
  haveI : FiniteDimensional ℂ ↥(⨆ j : Fin n, VM ⊓ Representation.invariants ((rightRegular F).comp U.subtype) ⊓
      archCutSubmodule F (⟨fun _ => 1, fun w _ => τs j w⟩ : AutomorphicForm.ArchTypeFamily F)) :=
    Submodule.finiteDimensional_iSup _
  exact Submodule.finiteDimensional_of_le (hYle.trans hsplit)

end S_AutomorphicForm_CuspidalSpectrum_finiteDimensional_of_le_cuspKFiniteSubmodule_of_toCuspSubcarrier_mem_of_isIrreducibleCuspSubrep
end P2MW
export P2MW.S_AutomorphicForm_CuspidalSpectrum_finiteDimensional_of_le_cuspKFiniteSubmodule_of_toCuspSubcarrier_mem_of_isIrreducibleCuspSubrep (solution)
