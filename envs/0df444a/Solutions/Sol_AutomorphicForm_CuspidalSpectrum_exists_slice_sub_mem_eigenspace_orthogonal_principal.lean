-- Prove2me | solution 1 for AutomorphicForm.CuspidalSpectrum.exists_slice_sub_mem_eigenspace_orthogonal_principal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/6a45278a-2c9a-54f8-8655-0e31a0175b0a

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_ArchSpherical
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isCompactOperator_isSymmetric_lift_rightConv
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_rightConv_mem_cuspMemberSubmodule
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_eq_zero_of_toCarrier_eq_zero
import Theorems.Thm_AutomorphicForm_rightConv_mem_archCutSubmodule_of_isArchBiFinite
import Theorems.Thm_AutomorphicForm_exists_forall_norm_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isCuspidalFn_of_isFundamentalDomain
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Definitions.Def_NumberField_SiegelVolume
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_mem_cuspMemberSubmodule_toCuspSubcarrier_eq_rightConv_eq_smul
import Theorems.Thm_HeckeIntegralSeam_heckeCosetSum_eq_of_isHeckeCosetSystem
import Theorems.Thm_ContinuousLinearMap_map_eigenspace_orthogonal_le_of_commute
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_commute_lift_cosetSum_of_isLevelSphericalOfType_of_isCompact
import Theorems.Thm_AutomorphicForm_isCompact_principalLevel_inf_finiteAdelicGL2Subgroup
import Theorems.Thm_AutomorphicForm_isOpen_principalLevel
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_slice_sub_mem_eigenspace_orthogonal_principal
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply"
p2m_attr_erase "simp" "AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel NumberField.AdelicHaar.adeleBorel

open scoped ProbabilityTheory Topology

private theorem mem_invariants_rightRegular_of_forall {F : Type} [Field F] [NumberField F]
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (h : ∀ g : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, φ (g * u) = φ g) :
    φ ∈ Representation.invariants ((AutomorphicForm.CuspidalConstituent.rightRegular F).comp U.subtype) := by
  rw [Representation.mem_invariants]
  intro u
  funext x
  show AutomorphicForm.CuspidalConstituent.rightTranslate F (u : AdelicGL2 (𝓞 F) F) φ x = φ x
  rw [AutomorphicForm.CuspidalConstituent.rightTranslate_apply]
  exact h x u u.2

theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (tys : AutomorphicForm.ArchTypeFamily F) (Ψ : HeckeEigensystem F ℂ)
    (x : AdelicGL2 (𝓞 F) F → ℂ)
    (hxi : x ∈ isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ ⊓ archCutSubmodule F tys)
    {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (σ : ℝ) (hσ : HasModulus F ξ σ) (hxm : x ∈ cuspMemberSubmodule F Φ₀ ξ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (hsph : IsLevelSphericalOfType F tys ((productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N) f)
    (hflat : flat F σ f = f)
    (Tc : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ))
    (hcomm : ∀ (φ : ↥(cuspMemberSubmodule F Φ₀ ξ)) (hφ' : rightConv F φ f ∈ cuspMemberSubmodule F Φ₀ ξ),
        Tc (toCuspSubcarrier F hΦ₀ σ ξ φ) = toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F φ f, hφ'⟩)
    (μ : ℂ) (hμ : μ ≠ 0) :
    ∃ (ψ : AdelicGL2 (𝓞 F) F → ℂ) (hψm : ψ ∈ cuspMemberSubmodule F Φ₀ ξ),
      ψ ∈ isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ ⊓ archCutSubmodule F tys ∧
      rightConv F ψ f = μ • ψ ∧
      ∀ y ∈ Module.End.eigenspace (Tc : Module.End ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) μ,
        ⟪toCuspSubcarrier F hΦ₀ σ ξ ⟨x, hxm⟩ - toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψm⟩, y⟫_ℂ = 0 := by
  classical
  haveI hBorel : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI hHaar := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  haveI hHc : CompleteSpace ↥(cuspSubcarrier F hΦ₀ σ ξ) := by
    unfold cuspSubcarrier; exact (Submodule.isClosed_topologicalClosure _).completeSpace_coe

  obtain ⟨Ts, hTs_cpt, hTs_sym, hTs_comm⟩ :=
    AutomorphicForm.CuspidalSpectrum.exists_isCompactOperator_isSymmetric_lift_rightConv F hΦ₀ σ ξ hσ f hf hflat
  have hmc : ∀ φ : ↥(cuspMemberSubmodule F Φ₀ ξ), rightConv F φ f ∈ cuspMemberSubmodule F Φ₀ ξ := fun φ =>
    AutomorphicForm.CuspidalSpectrum.rightConv_mem_cuspMemberSubmodule F hΦ₀ ξ f hf φ φ.2
  have hdense : Dense (Set.range (toCuspSubcarrier F hΦ₀ σ ξ) : Set ↥(cuspSubcarrier F hΦ₀ σ ξ)) := by
    rw [Subtype.dense_iff]
    intro z hz
    have hz' : z ∈ closure ((Submodule.map (toCarrier F hΦ₀ σ ξ)
        (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype (cuspMemberSubmodule F Φ₀ ξ)) : Set (Carrier F Φ₀ σ))) := by
      rw [← Submodule.topologicalClosure_coe]; exact hz
    refine closure_mono ?_ hz'
    rintro _ ⟨ψ, hψ, rfl⟩
    exact ⟨toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψ⟩, ⟨⟨ψ, hψ⟩, rfl⟩, rfl⟩
  have hTc_eq : Tc = Ts := by
    have hspan : Dense ((Submodule.span ℂ (Set.range (toCuspSubcarrier F hΦ₀ σ ξ)) : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) : Set ↥(cuspSubcarrier F hΦ₀ σ ξ)) :=
      hdense.mono Submodule.subset_span
    refine ContinuousLinearMap.ext_on hspan ?_
    rintro _ ⟨φ, rfl⟩
    rw [hcomm φ (hmc φ), hTs_comm φ (hmc φ)]
  have hTc_cpt : IsCompactOperator Tc := hTc_eq ▸ hTs_cpt
  have hTc_sym : (Tc : ↥(cuspSubcarrier F hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)).IsSymmetric := hTc_eq ▸ hTs_sym

  set Eμ : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ) := Module.End.eigenspace (Tc : Module.End ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) μ with hEμ
  have hEμ_mem : ∀ w, w ∈ Eμ ↔ Tc w = μ • w := fun w => by rw [hEμ, Module.End.mem_eigenspace_iff]; rfl
  have hEμ_closed : IsClosed (Eμ : Set ↥(cuspSubcarrier F hΦ₀ σ ξ)) := by
    have : (Eμ : Set ↥(cuspSubcarrier F hΦ₀ σ ξ)) = (fun w => Tc w - μ • w) ⁻¹' {0} := by
      ext w; simp only [SetLike.mem_coe, hEμ_mem, Set.mem_preimage, Set.mem_singleton_iff, sub_eq_zero]
    rw [this]
    exact isClosed_singleton.preimage (Tc.continuous.sub (continuous_const.fun_smul continuous_id))
  haveI : CompleteSpace ↥Eμ := hEμ_closed.completeSpace_coe
  let P := Eμ.orthogonalProjection
  set xH : ↥(cuspSubcarrier F hΦ₀ σ ξ) := toCuspSubcarrier F hΦ₀ σ ξ ⟨x, hxm⟩ with hxH
  set vE : ↥(cuspSubcarrier F hΦ₀ σ ξ) := ((P xH : ↥Eμ) : ↥(cuspSubcarrier F hΦ₀ σ ξ)) with hvE
  have hvE_mem : vE ∈ Eμ := (P xH).2
  have hvE_eig : Tc vE = μ • vE := (hEμ_mem vE).mp hvE_mem
  have hres_perp : xH - vE ∈ Eμᗮ := Submodule.sub_starProjection_mem_orthogonal xH

  obtain ⟨ψ, hψm, hψv, hψf⟩ :=
    AutomorphicForm.CuspidalSpectrum.exists_mem_cuspMemberSubmodule_toCuspSubcarrier_eq_rightConv_eq_smul
      F hΦ₀ σ ξ hσ f hf Tc hcomm μ hμ vE hvE_eig
  refine ⟨ψ, hψm, ?_, hψf, ?_⟩
  swap
  ·
    intro y hy
    rw [hψv]
    exact Submodule.inner_left_of_mem_orthogonal hy hres_perp

  have hsph' := hsph
  obtain ⟨fa, hfaT, hfabf, hfak, hfac⟩ := hsph'
  have hbf : IsArchBiFinite F tys f := IsArchBiFinite.of_factorization F hfac hfabf
  have hfU : ∀ x : AdelicGL2 (𝓞 F) F, ∀ u' ∈ (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N, f (u' * x) = f x := by
    intro x u' hu'
    have harch : glArch (𝓞 F) F u' = 1 := (Subgroup.mem_inf.mp hu').2
    have himg : (glFin (𝓞 F) F u' * glFin (𝓞 F) F x ∈
        (glFin (𝓞 F) F) '' (((productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N : Subgroup (AdelicGL2 (𝓞 F) F)) : Set (AdelicGL2 (𝓞 F) F))) ↔
        (glFin (𝓞 F) F x ∈ (glFin (𝓞 F) F) '' (((productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N : Subgroup (AdelicGL2 (𝓞 F) F)) : Set (AdelicGL2 (𝓞 F) F))) := by
      constructor
      · rintro ⟨k, hk, hkz⟩
        refine ⟨u'⁻¹ * k, Subgroup.mul_mem _ (Subgroup.inv_mem _ hu') hk, ?_⟩
        rw [map_mul, map_inv, hkz, inv_mul_cancel_left]
      · rintro ⟨k, hk, hkx⟩
        exact ⟨u' * k, Subgroup.mul_mem _ hu' hk, by rw [map_mul, hkx]⟩
    rw [hfac, hfac x, map_mul, harch, one_mul, map_mul]
    simp only [Set.indicator_apply, himg]

  have hconvU : ∀ (θ : AdelicGL2 (𝓞 F) F → ℂ) (x : AdelicGL2 (𝓞 F) F), ∀ u' ∈ (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N, rightConv F θ f (x * u') = rightConv F θ f x := by
    intro θ x u' hu'
    simp only [rightConv_apply]
    have h1 := integral_mul_left_eq_self (μ := adelicGLHaar (Fin 2) (𝓞 F) F) (fun y => θ (x * y) * f (u'⁻¹ * y)) u'
    simp only [inv_mul_cancel_left] at h1

    rw [show (fun y => θ (x * u' * y) * f y) = fun y => θ (x * (u' * y)) * f y from funext fun y => by rw [mul_assoc], h1]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    show θ (x * y) * f (u'⁻¹ * y) = θ (x * y) * f y
    rw [hfU y u'⁻¹ (inv_mem hu')]
  have hψ_eq : ψ = μ⁻¹ • rightConv F ψ f := by rw [hψf, smul_smul, inv_mul_cancel₀ hμ, one_smul]
  have hψU : ∀ g : AdelicGL2 (𝓞 F) F, ∀ u' ∈ (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N, ψ (g * u') = ψ g := by
    intro g u' hu'
    rw [hψ_eq]
    simp only [Pi.smul_apply, smul_eq_mul, hconvU ψ g u' hu']
  have hψc : Continuous ψ := hψm.2

  have hcut : ψ ∈ archCutSubmodule F tys := by
    rw [hψ_eq]
    exact Submodule.smul_mem _ _ (AutomorphicForm.rightConv_mem_archCutSubmodule_of_isArchBiFinite F tys ψ hψc f hf hbf)
  refine Submodule.mem_inf.mpr ⟨?_, hcut⟩
  by_cases hψ0 : ψ = 0
  · rw [hψ0]; exact Submodule.zero_mem _

  have hx0 : x ≠ 0 := by
    intro hx
    apply hψ0
    have hxH0 : xH = 0 := by
      rw [hxH]
      have : (⟨x, hxm⟩ : ↥(cuspMemberSubmodule F Φ₀ ξ)) = 0 := Subtype.ext hx
      rw [this, map_zero]
    have hvE0 : vE = 0 := by rw [hvE, hxH0, ContinuousLinearMap.map_zero, Submodule.coe_zero]
    have h0 : toCarrier F hΦ₀ σ ξ ⟨ψ, hψm.1.1.1⟩ = 0 := by
      have hc := congrArg Subtype.val hψv
      rw [toCuspSubcarrier_apply_coe, hvE0, Submodule.coe_zero] at hc
      exact hc
    exact AutomorphicForm.CuspidalSpectrum.eq_zero_of_toCarrier_eq_zero F hΦ₀ σ ξ ψ ⟨hψm.1.1.1, hψm.2⟩ h0
  have hxiso := (Submodule.mem_inf.mp hxi).1
  obtain ⟨φ₀, hφ₀, hφ₀ne⟩ : ∃ φ₀ : AdelicGL2 (𝓞 F) F → ℂ, IsIsotypicCuspFormAt F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ φ₀ ∧ φ₀ ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hx0
    have hle : isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ ≤ ⊥ := by
      unfold isotypicCuspSubmodule
      exact Submodule.span_le.mpr fun φ hφ => by simp [hall φ hφ]
    exact (Submodule.mem_bot ℂ).mp (hle hxiso)

  have hψlx0 := ((mem_memberSubmodule_iff' F Φ₀ ξ ψ).mp hψm.1.1.1)
  have hMemD : MemLp ψ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) := by
    haveI hRinv : (adelicGLHaar (Fin 2) (𝓞 F) F).IsMulRightInvariant := NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar F

    have hDclosed : IsClosed (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) := by
      refine Set.Finite.isClosed_biUnion (Finset.finite_toSet T) fun x _ => ?_
      exact (Homeomorph.mulRight x).isClosed_image.mpr (isClosed_centreCutSiegelSet c u d₁ d₂)
    have hDfin : adelicGLHaar (Fin 2) (𝓞 F) F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) < ⊤ := by
      refine (measure_biUnion_finset_le T _).trans_lt (ENNReal.sum_lt_top.mpr fun x _ => ?_)
      have himg : (· * x) '' centreCutSiegelSet F c u d₁ d₂ = (· * x⁻¹) ⁻¹' centreCutSiegelSet F c u d₁ d₂ := by
        ext g; constructor
        · rintro ⟨h, hh, rfl⟩; simpa [mul_inv_cancel_right] using hh
        · intro hg; exact ⟨g * x⁻¹, hg, by simp only [inv_mul_cancel_right]⟩
      rw [himg, ← Measure.map_apply (measurable_mul_const x⁻¹) (isClosed_centreCutSiegelSet c u d₁ d₂).measurableSet,
        map_mul_right_eq_self]
      exact NumberField.SiegelVolume.measure_centreCutSiegelSet_lt_top (F := F) (adelicGLHaar (Fin 2) (𝓞 F) F) hc u hd₁ d₂
    haveI : IsFiniteMeasure ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) := isFiniteMeasure_restrict.mpr hDfin.ne

    obtain ⟨C, hC⟩ := AutomorphicForm.exists_forall_norm_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isCuspidalFn_of_isFundamentalDomain
      F ξ f hf c u d₁ d₂ T hc hd₁ α β hΦ₀.pos_right hΦ₀.lt Φ₀ hΦ₀.isFundamentalDomain
    have hb := hC ψ hψlx0.1 hψm.1.1.2 hψc hψlx0.2
    refine MemLp.of_bound hψc.aestronglyMeasurable (‖μ⁻¹‖ * (C * (eLpNorm ψ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀)).toReal))
      ((ae_restrict_mem hDclosed.measurableSet).mono fun g hg => ?_)
    calc ‖ψ g‖ = ‖μ⁻¹ * rightConv F ψ f g‖ := by
          conv_lhs => rw [hψ_eq]
          rfl
      _ = ‖μ⁻¹‖ * ‖rightConv F ψ f g‖ := norm_mul _ _
      _ ≤ ‖μ⁻¹‖ * (C * (eLpNorm ψ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀)).toReal) :=
          mul_le_mul_of_nonneg_left (hb g hg) (norm_nonneg _)
  have hsmoothD : IsSmoothCuspAutomorphicFnAt F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ ψ := by
    refine ⟨⟨?_, hψm.1.1.2⟩, hψm.1.2⟩
    exact (lsXiMemberAt_iff (𝓞 F) F (adelicGLHaar (Fin 2) (𝓞 F) F) ⊤ ξ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) ψ).mpr ⟨hψlx0.1, hMemD⟩
  refine IsIsotypicCuspFormAt.mem_isotypicCuspSubmodule ⟨hsmoothD, hψc, hψU, ?_, ?_⟩
  ·
    intro v hv

    obtain ⟨reps, hsys, heig₀⟩ := hφ₀.hecke_eigen v hv
    have hgen_eig : ∀ φ : AdelicGL2 (𝓞 F) F → ℂ, IsIsotypicCuspFormAt F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ φ →
        (∀ g, ∀ u' ∈ (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N, φ (g * u') = φ g) ∧ ∀ g, SmoothCusp.heckeCosetSum F reps φ g = Ψ.a v * φ g := by
      intro φ hφ
      refine ⟨hφ.level_invariant, fun g => ?_⟩
      obtain ⟨reps', hsys', heig'⟩ := hφ.hecke_eigen v hv
      rw [← heig' g]
      unfold SmoothCusp.heckeCosetSum
      exact HeckeIntegralSeam.heckeCosetSum_eq_of_isHeckeCosetSystem hsys' hsys hφ.level_invariant g
    have hx_eig : (∀ g, ∀ u' ∈ (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N, x (g * u') = x g) ∧ ∀ g, SmoothCusp.heckeCosetSum F reps x g = Ψ.a v * x g := by
      unfold isotypicCuspSubmodule at hxiso
      refine Submodule.span_induction
        (p := fun (θ : AdelicGL2 (𝓞 F) F → ℂ) _ => (∀ g, ∀ u' ∈ (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N, θ (g * u') = θ g) ∧
          ∀ g, SmoothCusp.heckeCosetSum F reps θ g = Ψ.a v * θ g) ?_ ?_ ?_ ?_ hxiso
      · exact fun θ hθ => hgen_eig θ hθ
      · exact ⟨fun _ _ _ => rfl, fun g => by
          show ∑ i, (0 : AdelicGL2 (𝓞 F) F → ℂ) (g * reps i) = Ψ.a v * (0 : AdelicGL2 (𝓞 F) F → ℂ) g
          simp only [Pi.zero_apply, Finset.sum_const_zero, mul_zero]⟩
      · intro θ₁ θ₂ _ _ ih₁ ih₂
        refine ⟨fun g u' hu' => by rw [Pi.add_apply, Pi.add_apply, ih₁.1 g u' hu', ih₂.1 g u' hu'], fun g => ?_⟩
        have e1 := ih₁.2 g
        have e2 := ih₂.2 g
        simp only [SmoothCusp.heckeCosetSum, Pi.add_apply] at e1 e2 ⊢
        rw [Finset.sum_add_distrib, e1, e2, mul_add]
      · intro a θ _ ih
        refine ⟨fun g u' hu' => by rw [Pi.smul_apply, Pi.smul_apply, ih.1 g u' hu'], fun g => ?_⟩
        have e1 := ih.2 g
        simp only [SmoothCusp.heckeCosetSum, Pi.smul_apply, smul_eq_mul] at e1 ⊢
        rw [← Finset.mul_sum, e1]
        ring

    have hgKf : heckeGen (𝓞 F) F v ∈ finiteAdelicGL2Subgroup F := by
      rw [mem_finiteAdelicGL2Subgroup_iff]
      refine Matrix.GeneralLinearGroup.ext fun i j => ?_
      rw [glArch_apply, Units.val_one]
      exact heckeGenAt_fst _ i j
    have h1 : ∀ i, ∃ u' ∈ (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N, ∃ u'' ∈ (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N, reps i = u' * heckeGen (𝓞 F) F v * u'' := by
      intro i
      obtain ⟨u', hu', u'', hu'', h⟩ := HeckePair.mem_doubleCoset_iff.mp (hsys.mem_doubleCoset i)
      exact ⟨u', hu', u'', hu'', h.symm⟩
    have h2 : ∀ y : AdelicGL2 (𝓞 F) F, (∃ u' ∈ (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N, ∃ u'' ∈ (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N, y = u' * heckeGen (𝓞 F) F v * u'') →
        ∃ i, ∃ u' ∈ (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N, y = reps i * u' := by
      rintro y ⟨u', hu', u'', hu'', rfl⟩
      obtain ⟨i, hi⟩ := hsys.covers (u' * heckeGen (𝓞 F) F v * u'') (HeckePair.mem_doubleCoset_iff.mpr ⟨u', hu', u'', hu'', rfl⟩)
      refine ⟨i, (reps i)⁻¹ * (u' * heckeGen (𝓞 F) F v * u''), ?_, by rw [mul_inv_cancel_left]⟩
      have := QuotientGroup.eq.mp hi.symm
      exact this
    have h3 : ∀ i j, (reps i)⁻¹ * reps j ∈ (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N → i = j := by
      intro i j hij
      exact hsys.mk_injective (QuotientGroup.eq.mpr hij)
    obtain ⟨Sv, hSv_comm, hSv_act⟩ :=
      AutomorphicForm.CuspidalSpectrum.exists_commute_lift_cosetSum_of_isLevelSphericalOfType_of_isCompact F hΦ₀ σ ξ hσ
        (principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (AutomorphicForm.isCompact_principalLevel_inf_finiteAdelicGL2Subgroup F N) (principalLevel (𝓞 F) F N)
        (AutomorphicForm.isOpen_principalLevel F N hN) rfl
        tys f hf hsph Tc hcomm (heckeGen (𝓞 F) F v) hgKf _ reps h1 h2 h3

    obtain ⟨hxs, hSx⟩ := hSv_act ⟨x, hxm⟩ (mem_invariants_rightRegular_of_forall _ x hx_eig.1)
    have hSx' : Sv xH = Ψ.a v • xH := by
      rw [hxH, hSx]
      have : (⟨fun y => ∑ i, (x : AdelicGL2 (𝓞 F) F → ℂ) (y * reps i), hxs⟩ : ↥(cuspMemberSubmodule F Φ₀ ξ)) = Ψ.a v • ⟨x, hxm⟩ := by
        apply Subtype.ext
        funext y
        show ∑ i, x (y * reps i) = (Ψ.a v • x) y
        rw [Pi.smul_apply, smul_eq_mul]
        exact hx_eig.2 y
      rw [this, map_smul]

    obtain ⟨hCP1, hCP2⟩ := ContinuousLinearMap.map_eigenspace_orthogonal_le_of_commute hTc_cpt hTc_sym Sv hSv_comm μ hμ
    have hSvE : Sv vE = Ψ.a v • vE := by
      have hin : Sv vE - Ψ.a v • vE ∈ Eμ := Eμ.sub_mem (hCP1 ⟨vE, hvE_mem, rfl⟩) (Eμ.smul_mem _ hvE_mem)
      have hr : Sv (xH - vE) - Ψ.a v • (xH - vE) ∈ Eμᗮ := (Eμᗮ).sub_mem (hCP2 ⟨xH - vE, hres_perp, rfl⟩) ((Eμᗮ).smul_mem _ hres_perp)
      have hsum : (Sv vE - Ψ.a v • vE) + (Sv (xH - vE) - Ψ.a v • (xH - vE)) = 0 := by
        rw [map_sub, smul_sub, hSx']; abel
      have heq : Sv vE - Ψ.a v • vE = -(Sv (xH - vE) - Ψ.a v • (xH - vE)) := eq_neg_of_add_eq_zero_left hsum
      have hin' : Sv vE - Ψ.a v • vE ∈ Eμᗮ := by rw [heq]; exact (Eμᗮ).neg_mem hr
      have hboth : Sv vE - Ψ.a v • vE ∈ Eμ ⊓ Eμᗮ := Submodule.mem_inf.mpr ⟨hin, hin'⟩
      rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at hboth
      exact sub_eq_zero.mp hboth

    obtain ⟨hψs, hSψ⟩ := hSv_act ⟨ψ, hψm⟩ (mem_invariants_rightRegular_of_forall _ ψ hψU)
    obtain ⟨dψ, hdψ⟩ : ∃ dψ : ↥(cuspMemberSubmodule F Φ₀ ξ), dψ = ⟨_, hψs⟩ - Ψ.a v • ⟨ψ, hψm⟩ := ⟨_, rfl⟩
    have hcl : toCuspSubcarrier F hΦ₀ σ ξ dψ = 0 := by
      rw [hdψ, map_sub, map_smul, ← hSψ, hψv, hSvE, sub_self]
    have h0 : toCarrier F hΦ₀ σ ξ ⟨(dψ : AdelicGL2 (𝓞 F) F → ℂ), dψ.2.1.1.1⟩ = 0 := by
      have hc := congrArg Subtype.val hcl
      rw [toCuspSubcarrier_apply_coe, Submodule.coe_zero] at hc
      exact hc
    have hzero := AutomorphicForm.CuspidalSpectrum.eq_zero_of_toCarrier_eq_zero F hΦ₀ σ ξ _ ⟨dψ.2.1.1.1, dψ.2.2⟩ h0
    refine ⟨reps, hsys, fun g => ?_⟩
    have hg := congrFun hzero g
    rw [hdψ, Submodule.coe_sub, Submodule.coe_smul, Pi.sub_apply, Pi.zero_apply, sub_eq_zero, Pi.smul_apply, smul_eq_mul] at hg
    exact hg
  ·
    have hψlx := ((mem_memberSubmodule_iff' F Φ₀ ξ ψ).mp hψm.1.1.1).1
    have hφ₀lx : IsLsXiFunction (𝓞 F) F ⊤ ξ φ₀ :=
      ((lsXiMemberAt_iff (𝓞 F) F (adelicGLHaar (Fin 2) (𝓞 F) F) ⊤ ξ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) φ₀).mp hφ₀.smoothCusp.1.1).1
    obtain ⟨g₀, hg₀⟩ := Function.ne_iff.mp hφ₀ne
    have key_c : ∀ (d : (AdeleRing (𝓞 F) F)ˣ) (b : ℂ),
        (∀ g, φ₀ (centralScalar (𝓞 F) F d * g) = b * φ₀ g) → ∀ g, ψ (centralScalar (𝓞 F) F d * g) = b * ψ g := by
      intro d b hb g
      have h1 := hφ₀lx.central_transform ⟨d, Subgroup.mem_top d⟩ g₀
      have hξ : ((ξ ⟨d, Subgroup.mem_top d⟩ : ℂˣ) : ℂ) = b := mul_right_cancel₀ hg₀ (h1.symm.trans (hb g₀))
      have h3 := hψlx.central_transform ⟨d, Subgroup.mem_top d⟩ g
      rw [hξ] at h3
      exact h3
    intro v hv g
    exact key_c _ _ (hφ₀.central_eigen v hv) g

end S_AutomorphicForm_CuspidalSpectrum_exists_slice_sub_mem_eigenspace_orthogonal_principal
end P2MW
export P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_slice_sub_mem_eigenspace_orthogonal_principal (solution)
