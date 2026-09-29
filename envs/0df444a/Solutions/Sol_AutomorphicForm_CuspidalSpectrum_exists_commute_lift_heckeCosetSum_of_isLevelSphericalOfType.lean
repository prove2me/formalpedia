-- Prove2me | solution 1 for AutomorphicForm.CuspidalSpectrum.exists_commute_lift_heckeCosetSum_of_isLevelSphericalOfType
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/a679e8f3-85e2-5330-9c98-316be931c482

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_ArchSpherical
import Theorems.Thm_AutomorphicForm_cosetSum_rightConv_of_isLevelSphericalOfType
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isLift_rightTranslate
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_rightTranslate_mem_cuspMemberSubmodule
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_map_cuspSubcarrier_le_cuspLevelSubcarrier_of_isLift_rightConv
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_apply_eq_zero_of_mem_orthogonal_cuspLevelSubcarrier_of_isLift_rightConv_of_rightInvariant
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isLift_rightConv
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_apply_mem_cuspSubcarrier_of_isLift_rightConv
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_isCuspidalFn_rightConv
import Theorems.Thm_AutomorphicForm_isKfSmooth_rightConv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_commute_lift_heckeCosetSum_of_isLevelSphericalOfType
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg"
p2m_attr_erase "simp" "RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem solution
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (hσ : HasModulus F ξ σ) (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (tys : AutomorphicForm.ArchTypeFamily F)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (hsph : IsLevelSphericalOfType F tys ((productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N) f)
    (Tc : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ))
    (hcomm : ∀ (φ : ↥(cuspMemberSubmodule F Φ₀ ξ)) (hφ' : rightConv F φ f ∈ cuspMemberSubmodule F Φ₀ ξ),
        Tc (toCuspSubcarrier F hΦ₀ σ ξ φ) = toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F φ f, hφ'⟩)
    (g : AdelicGL2 (𝓞 F) F) (hg : g ∈ finiteAdelicGL2Subgroup F) (n : ℕ) (reps : Fin n → AdelicGL2 (𝓞 F) F)
    (h1 : ∀ i, ∃ u' ∈ (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N, ∃ u'' ∈ (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N, reps i = u' * g * u'')
    (h2 : ∀ x : AdelicGL2 (𝓞 F) F, (∃ u' ∈ (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N, ∃ u'' ∈ (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N, x = u' * g * u'') → ∃ i, ∃ u' ∈ (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N, x = reps i * u')
    (h3 : ∀ i j, (reps i)⁻¹ * reps j ∈ (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N → i = j) :
    ∃ S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ), S.comp Tc = Tc.comp S ∧
      ∀ φ : ↥(cuspMemberSubmodule F Φ₀ ξ),
        (φ : AdelicGL2 (𝓞 F) F → ℂ) ∈ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N →
        ∃ h : (fun x => ∑ i, (φ : AdelicGL2 (𝓞 F) F → ℂ) (x * reps i)) ∈ cuspMemberSubmodule F Φ₀ ξ,
          S (toCuspSubcarrier F hΦ₀ σ ξ φ) = toCuspSubcarrier F hΦ₀ σ ξ ⟨fun x => ∑ i, (φ : AdelicGL2 (𝓞 F) F → ℂ) (x * reps i), h⟩ := by
  classical
  obtain ⟨hfc, hfcs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F f hf
  haveI : CompleteSpace ↥(cuspSubcarrier F hΦ₀ σ ξ) := by
    unfold cuspSubcarrier
    exact (Submodule.isClosed_topologicalClosure _).completeSpace_coe

  have hfU : ∀ x : AdelicGL2 (𝓞 F) F, ∀ u' ∈ (fdPins F Φ₀).U N, f (u' * x) = f x := by
    obtain ⟨fa, -, -, -, hfac⟩ := hsph
    intro x u' hu'
    have harch : AdelicLevel.glArch (𝓞 F) F u' = 1 := (Subgroup.mem_inf.mp hu').2
    have himg : (AdelicLevel.glFin (𝓞 F) F u' * AdelicLevel.glFin (𝓞 F) F x ∈
        (AdelicLevel.glFin (𝓞 F) F) '' (((productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N : Subgroup (AdelicGL2 (𝓞 F) F)) : Set (AdelicGL2 (𝓞 F) F))) ↔
        (AdelicLevel.glFin (𝓞 F) F x ∈
        (AdelicLevel.glFin (𝓞 F) F) '' (((productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N : Subgroup (AdelicGL2 (𝓞 F) F)) : Set (AdelicGL2 (𝓞 F) F))) := by
      constructor
      · rintro ⟨k, hk, hkz⟩
        refine ⟨u'⁻¹ * k, Subgroup.mul_mem _ (Subgroup.inv_mem _ hu') hk, ?_⟩
        rw [map_mul, map_inv, hkz, inv_mul_cancel_left]
      · rintro ⟨k, hk, hkx⟩
        exact ⟨u' * k, Subgroup.mul_mem _ hu' hk, by rw [map_mul, hkx]⟩
    rw [hfac, hfac x, map_mul, harch, one_mul, map_mul]
    simp only [Set.indicator_apply, himg]
  have hfU' : ∀ x : AdelicGL2 (𝓞 F) F, ∀ u' ∈ (fdPins F Φ₀).U N, f (x * u') = f x := by
    obtain ⟨fa, -, -, -, hfac⟩ := hsph
    intro x u' hu'
    have harch : AdelicLevel.glArch (𝓞 F) F u' = 1 := (Subgroup.mem_inf.mp hu').2
    have himg : (AdelicLevel.glFin (𝓞 F) F x * AdelicLevel.glFin (𝓞 F) F u' ∈
        (AdelicLevel.glFin (𝓞 F) F) '' (((productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N : Subgroup (AdelicGL2 (𝓞 F) F)) : Set (AdelicGL2 (𝓞 F) F))) ↔
        (AdelicLevel.glFin (𝓞 F) F x ∈
        (AdelicLevel.glFin (𝓞 F) F) '' (((productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N : Subgroup (AdelicGL2 (𝓞 F) F)) : Set (AdelicGL2 (𝓞 F) F))) := by
      constructor
      · rintro ⟨k, hk, hkz⟩
        refine ⟨k * u'⁻¹, Subgroup.mul_mem _ hk (Subgroup.inv_mem _ hu'), ?_⟩
        rw [map_mul, map_inv, hkz, mul_inv_cancel_right]
      · rintro ⟨k, hk, hkx⟩
        exact ⟨k * u', Subgroup.mul_mem _ hk hu', by rw [map_mul, hkx]⟩
    rw [hfac, hfac x, map_mul, harch, mul_one, map_mul]
    simp only [Set.indicator_apply, himg]

  obtain ⟨Tf, -, hTf, -, -⟩ :=
    AutomorphicForm.CuspidalSpectrum.exists_isLift_rightConv F α β Φ₀ hΦ₀ σ ξ hσ f hfc hfcs
  have memf : ∀ φ : ↥(cuspMemberSubmodule F Φ₀ ξ), rightConv F φ f ∈ cuspMemberSubmodule F Φ₀ ξ := by
    intro φ
    have hcont : (φ : AdelicGL2 (𝓞 F) F → ℂ) ∈ contMemberSubmodule F Φ₀ ξ := ⟨φ.2.1.1.1, φ.2.2⟩
    have hmaps := hTf.mapsTo φ hcont
    refine ⟨⟨⟨hmaps.1, ?_⟩, AutomorphicForm.isKfSmooth_rightConv F φ f hf⟩, hmaps.2⟩
    exact AutomorphicForm.isCuspidalFn_rightConv F Φ₀ (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (fun v => heckeGen (𝓞 F) F v) φ φ.2.2 φ.2.1.1.2 f hf
  have hdense : Dense (Set.range (toCuspSubcarrier F hΦ₀ σ ξ)) := by
    rw [Subtype.dense_iff]
    intro v hv
    have hv' : v ∈ closure ((Submodule.map (toCarrier F hΦ₀ σ ξ)
        (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype (cuspMemberSubmodule F Φ₀ ξ))) : Set (Carrier F Φ₀ σ)) := by
      rw [← Submodule.topologicalClosure_coe]
      exact hv
    refine closure_mono ?_ hv'
    rintro _ ⟨ψ, hψ, rfl⟩
    exact ⟨toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψ⟩, ⟨_, rfl⟩, rfl⟩
  have hTc_eq : (cuspSubcarrier F hΦ₀ σ ξ).subtypeL.comp Tc = Tf.comp (cuspSubcarrier F hΦ₀ σ ξ).subtypeL := by
    refine ContinuousLinearMap.ext_on (hdense.mono Submodule.subset_span) ?_
    rintro _ ⟨φ, rfl⟩
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, Submodule.subtypeL_apply,
      hcomm φ (memf φ), toCuspSubcarrier_apply_coe, toCuspSubcarrier_apply_coe]
    exact (hTf.comm φ ⟨φ.2.1.1.1, φ.2.2⟩).symm
  have hTc : ∀ v : ↥(cuspSubcarrier F hΦ₀ σ ξ), ((Tc v : ↥(cuspSubcarrier F hΦ₀ σ ξ)) : Carrier F Φ₀ σ) = Tf v := fun v =>
    congrArg (fun A : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] Carrier F Φ₀ σ => A v) hTc_eq

  have hLcH : cuspLevelSubcarrier F hΦ₀ σ ξ N ≤ cuspSubcarrier F hΦ₀ σ ξ := by
    unfold cuspLevelSubcarrier cuspSubcarrier
    exact Submodule.topologicalClosure_mono (Submodule.map_mono (Submodule.comap_mono inf_le_left))
  set LH : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ) := Submodule.comap (cuspSubcarrier F hΦ₀ σ ξ).subtype (cuspLevelSubcarrier F hΦ₀ σ ξ N) with hLH
  have hLHclosed : IsClosed (LH : Set ↥(cuspSubcarrier F hΦ₀ σ ξ)) := by
    have h1 : IsClosed ((cuspLevelSubcarrier F hΦ₀ σ ξ N : Submodule ℂ (Carrier F Φ₀ σ)) : Set (Carrier F Φ₀ σ)) := by
      unfold cuspLevelSubcarrier
      exact Submodule.isClosed_topologicalClosure _
    exact h1.preimage continuous_subtype_val
  haveI : CompleteSpace ↥LH := hLHclosed.completeSpace_coe
  set PN : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ) := LH.starProjection with hPN

  have hrange : ∀ v : ↥(cuspSubcarrier F hΦ₀ σ ξ), Tc v ∈ LH := by
    intro v
    show ((Tc v : ↥(cuspSubcarrier F hΦ₀ σ ξ)) : Carrier F Φ₀ σ) ∈ cuspLevelSubcarrier F hΦ₀ σ ξ N
    rw [hTc v]
    exact AutomorphicForm.CuspidalSpectrum.map_cuspSubcarrier_le_cuspLevelSubcarrier_of_isLift_rightConv F hΦ₀ σ ξ N f hf hfU
      Tf hTf (Submodule.mem_map_of_mem v.2)
  have hker : ∀ v : ↥(cuspSubcarrier F hΦ₀ σ ξ), v ∈ LHᗮ → Tc v = 0 := by
    intro v hv
    apply Subtype.ext
    rw [hTc v]
    refine AutomorphicForm.CuspidalSpectrum.apply_eq_zero_of_mem_orthogonal_cuspLevelSubcarrier_of_isLift_rightConv_of_rightInvariant
      F hΦ₀ σ ξ N f hf hfU' Tf hTf v v.2 ?_
    rw [Submodule.mem_orthogonal]
    intro y hy
    exact (Submodule.mem_orthogonal _ _).mp hv ⟨y, hLcH hy⟩ hy

  have hL := fun i => AutomorphicForm.CuspidalSpectrum.exists_isLift_rightTranslate F α β Φ₀ hΦ₀ σ ξ hσ (reps i)
  choose Tr Tr' hTr hTr' hadj hnorm using hL
  have memr : ∀ (i : Fin n) (φ : AdelicGL2 (𝓞 F) F → ℂ), φ ∈ cuspMemberSubmodule F Φ₀ ξ →
      rightTranslate F (reps i) φ ∈ cuspMemberSubmodule F Φ₀ ξ := fun i φ hφ =>
    AutomorphicForm.CuspidalSpectrum.rightTranslate_mem_cuspMemberSubmodule F hΦ₀ ξ (reps i) φ hφ
  have hinv : ∀ (i : Fin n) (v : ↥(cuspSubcarrier F hΦ₀ σ ξ)), Tr i (v : Carrier F Φ₀ σ) ∈ cuspSubcarrier F hΦ₀ σ ξ := by
    intro i v
    have hM : ∀ x ∈ ((Submodule.map (toCarrier F hΦ₀ σ ξ)
        (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype (cuspMemberSubmodule F Φ₀ ξ))) : Set (Carrier F Φ₀ σ)),
        Tr i x ∈ ((Submodule.map (toCarrier F hΦ₀ σ ξ)
        (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype (cuspMemberSubmodule F Φ₀ ξ))) : Set (Carrier F Φ₀ σ)) := by
      rintro _ ⟨ψ, hψ, rfl⟩
      refine ⟨⟨rightTranslate F (reps i) ψ, (memr i ψ hψ).1.1.1⟩, memr i ψ hψ, ?_⟩
      exact ((hTr i).comm ψ ⟨ψ.2, hψ.2⟩).symm
    have hv : (v : Carrier F Φ₀ σ) ∈ closure ((Submodule.map (toCarrier F hΦ₀ σ ξ)
        (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype (cuspMemberSubmodule F Φ₀ ξ))) : Set (Carrier F Φ₀ σ)) := by
      rw [← Submodule.topologicalClosure_coe]
      exact v.2
    have h1 := image_closure_subset_closure_image (Tr i).continuous ⟨(v : Carrier F Φ₀ σ), hv, rfl⟩
    have h2 := closure_mono (by rintro _ ⟨x, hx, rfl⟩; exact hM x hx) h1
    rw [← Submodule.topologicalClosure_coe] at h2
    exact h2
  let Sraw : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ) :=
    ((∑ i, Tr i).comp (cuspSubcarrier F hΦ₀ σ ξ).subtypeL).codRestrict (cuspSubcarrier F hΦ₀ σ ξ) fun v => by
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply]
      exact Submodule.sum_mem _ fun i _ => hinv i v
  have Sraw_apply : ∀ v : ↥(cuspSubcarrier F hΦ₀ σ ξ), (Sraw v : Carrier F Φ₀ σ) = ∑ i, Tr i v := by
    intro v
    show ((∑ i, Tr i).comp (cuspSubcarrier F hΦ₀ σ ξ).subtypeL) v = _
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply]
    rfl

  have memsum : ∀ φ : ↥(cuspMemberSubmodule F Φ₀ ξ),
      (fun x => ∑ i, (φ : AdelicGL2 (𝓞 F) F → ℂ) (x * reps i)) ∈ cuspMemberSubmodule F Φ₀ ξ := by
    intro φ
    have hfeq : (fun x => ∑ i, (φ : AdelicGL2 (𝓞 F) F → ℂ) (x * reps i)) =
        ∑ i, rightTranslate F (reps i) (φ : AdelicGL2 (𝓞 F) F → ℂ) := by
      funext x; simp only [Finset.sum_apply, rightTranslate_apply]
    rw [hfeq]
    exact Submodule.sum_mem _ fun i _ => memr i φ φ.2
  have Sraw_lift : ∀ φ : ↥(cuspMemberSubmodule F Φ₀ ξ),
      Sraw (toCuspSubcarrier F hΦ₀ σ ξ φ) =
        toCuspSubcarrier F hΦ₀ σ ξ ⟨fun x => ∑ i, (φ : AdelicGL2 (𝓞 F) F → ℂ) (x * reps i), memsum φ⟩ := by
    intro φ
    apply Subtype.ext
    rw [Sraw_apply, toCuspSubcarrier_apply_coe, toCuspSubcarrier_apply_coe]
    have hstep : ∀ i, Tr i (toCarrier F hΦ₀ σ ξ ⟨φ, φ.2.1.1.1⟩) =
        toCarrier F hΦ₀ σ ξ ⟨rightTranslate F (reps i) φ, (memr i φ φ.2).1.1.1⟩ :=
      fun i => (hTr i).comm φ ⟨φ.2.1.1.1, φ.2.2⟩
    simp only [hstep]
    rw [← map_sum]
    congr 1
    apply Subtype.ext
    rw [Submodule.coe_sum]
    funext x
    simp only [Finset.sum_apply, rightTranslate_apply]

  have key : ∀ (φ : ↥(cuspMemberSubmodule F Φ₀ ξ)),
      (φ : AdelicGL2 (𝓞 F) F → ℂ) ∈ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N →
      Sraw (Tc (toCuspSubcarrier F hΦ₀ σ ξ φ)) = Tc (Sraw (toCuspSubcarrier F hΦ₀ σ ξ φ)) := by
    intro φ hφU
    rw [hcomm φ (memf φ), Sraw_lift, Sraw_lift, hcomm _ (memf _)]
    congr 1
    apply Subtype.ext
    exact AutomorphicForm.cosetSum_rightConv_of_isLevelSphericalOfType F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) N hN
      (tys : AutomorphicForm.ArchTypeFamily F) f hsph g hg n reps h1 h2 h3 φ φ.2.2 hφU
  have hcommL : ∀ w : ↥LH, Sraw (Tc (w : ↥(cuspSubcarrier F hΦ₀ σ ξ))) = Tc (Sraw (w : ↥(cuspSubcarrier F hΦ₀ σ ξ))) := by

    let DL : Set ↥LH := {w | ∃ (φ : ↥(cuspMemberSubmodule F Φ₀ ξ)),
      (φ : AdelicGL2 (𝓞 F) F → ℂ) ∈ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ∧ (w : ↥(cuspSubcarrier F hΦ₀ σ ξ)) = toCuspSubcarrier F hΦ₀ σ ξ φ}
    have hDL : Dense DL := by
      rw [Subtype.dense_iff]
      intro z hz
      rw [closure_subtype]
      have hz' : ((z : ↥(cuspSubcarrier F hΦ₀ σ ξ)) : Carrier F Φ₀ σ) ∈ closure ((Submodule.map (toCarrier F hΦ₀ σ ξ)
          (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype
            (cuspMemberSubmodule F Φ₀ ξ ⊓ levelInvariantSubmodule F (fdPins F Φ₀) N))) : Set (Carrier F Φ₀ σ)) := by
        rw [← Submodule.topologicalClosure_coe]
        exact hz
      refine closure_mono ?_ hz'
      rintro _ ⟨ψ, hψ, rfl⟩
      have hψm : (ψ : AdelicGL2 (𝓞 F) F → ℂ) ∈ cuspMemberSubmodule F Φ₀ ξ := (Submodule.mem_inf.mp hψ).1
      have hψU : (ψ : AdelicGL2 (𝓞 F) F → ℂ) ∈ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N := (Submodule.mem_inf.mp hψ).2
      have hmemLH : toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψm⟩ ∈ LH := by
        show ((toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψm⟩ : ↥(cuspSubcarrier F hΦ₀ σ ξ)) : Carrier F Φ₀ σ) ∈ cuspLevelSubcarrier F hΦ₀ σ ξ N
        rw [toCuspSubcarrier_apply_coe]
        unfold cuspLevelSubcarrier
        exact Submodule.le_topologicalClosure _ ⟨ψ, hψ, rfl⟩
      exact ⟨toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψm⟩, ⟨⟨toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψm⟩, hmemLH⟩, ⟨⟨ψ, hψm⟩, hψU, rfl⟩, rfl⟩, rfl⟩
    have hext : ((Sraw.comp Tc).comp LH.subtypeL) = ((Tc.comp Sraw).comp LH.subtypeL) := by
      refine ContinuousLinearMap.ext_on (hDL.mono Submodule.subset_span) ?_
      rintro w ⟨φ, hφU, hw⟩
      simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
      rw [hw]
      exact key φ hφU
    intro w
    have := congrArg (fun A : ↥LH →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ) => A w) hext
    simpa only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply] using this

  refine ⟨Sraw.comp PN, ?_, ?_⟩
  · ext1 v
    have hPT : PN (Tc v) = Tc v := Submodule.starProjection_eq_self_iff.mpr (hrange v)
    have hdec : Tc v = Tc (PN v) := by
      have h0 : Tc (v - PN v) = 0 := hker _ (Submodule.sub_starProjection_mem_orthogonal v)
      rw [map_sub, sub_eq_zero] at h0
      exact h0
    have hPmem : PN v ∈ LH := by
      rw [hPN]
      exact (LH.orthogonalProjection v).2
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, hPT, hdec]
    exact hcommL ⟨PN v, hPmem⟩
  · intro φ hφU
    refine ⟨memsum φ, ?_⟩
    have hmemLH : toCuspSubcarrier F hΦ₀ σ ξ φ ∈ LH := by
      show ((toCuspSubcarrier F hΦ₀ σ ξ φ : ↥(cuspSubcarrier F hΦ₀ σ ξ)) : Carrier F Φ₀ σ) ∈ cuspLevelSubcarrier F hΦ₀ σ ξ N
      rw [toCuspSubcarrier_apply_coe]
      unfold cuspLevelSubcarrier
      refine Submodule.le_topologicalClosure _ ⟨⟨φ, φ.2.1.1.1⟩, ?_, rfl⟩
      exact Submodule.mem_inf.mpr ⟨φ.2, hφU⟩
    rw [ContinuousLinearMap.comp_apply, Submodule.starProjection_eq_self_iff.mpr hmemLH]
    exact Sraw_lift φ

end S_AutomorphicForm_CuspidalSpectrum_exists_commute_lift_heckeCosetSum_of_isLevelSphericalOfType
end P2MW
export P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_commute_lift_heckeCosetSum_of_isLevelSphericalOfType (solution)
