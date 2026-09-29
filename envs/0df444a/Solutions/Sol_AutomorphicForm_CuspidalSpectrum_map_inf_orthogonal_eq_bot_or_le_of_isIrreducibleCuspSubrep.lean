-- Prove2me | solution 1 for AutomorphicForm.CuspidalSpectrum.map_inf_orthogonal_eq_bot_or_le_of_isIrreducibleCuspSubrep
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/74b21382-52e2-5ac6-bb0d-d4061f308326

import Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_ArchSpherical
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_map_inf_eq_bot_or_le_of_isIrreducibleCuspSubrep_of_isClosed
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_commute_lift_rightTranslate_rowIsometry_of_isCompact
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_commute_lift_cosetSum_of_isLevelSphericalOfType_of_isCompact
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_commute_lift_rightConv_of_isArchBiFinite_of_isCompact
import Theorems.Thm_ContinuousLinearMap_map_highPart_orthogonal_le_of_commute
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalSpectrum_map_inf_orthogonal_eq_bot_or_le_of_isIrreducibleCuspSubrep
p2m_attr_erase "instance" "AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AdelicDock.coe_finEmbed AdelicDock.splice_apply_self"
p2m_attr_erase "simp" "AdelicDock.coe_localEmbed AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem solution
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) (hM : IsIrreducibleCuspSubrep F hΦ₀ σ ξ M)
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F)
    (τ : ∀ w : InfinitePlace F, ArchRepAt F w) (hirr : ∀ w, (τ w).ρ.IsIrreducible)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (hsph : IsLevelSphericalOfType F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F) U f)
    (hflat : flat F σ f = f)
    (Tc : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ))
    (hsymm : (Tc : ↥(cuspSubcarrier F hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)).IsSymmetric)
    (hcomm : ∀ (φ : ↥(cuspMemberSubmodule F Φ₀ ξ)) (hφ' : rightConv F φ f ∈ cuspMemberSubmodule F Φ₀ ξ),
        Tc (toCuspSubcarrier F hΦ₀ σ ξ φ) = toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F φ f, hφ'⟩)
    (Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hYc : Y ≤ cuspMemberSubmodule F Φ₀ ξ)
    (hYM : ∀ (ψ : AdelicGL2 (𝓞 F) F → ℂ) (hψ : ψ ∈ Y), toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hYc hψ⟩ ∈ M)
    (hYU : ∀ ψ ∈ Y, ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U, ψ (g * k) = ψ g)
    (hYt : Y ≤ archCutSubmodule F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F))
    (r : ℝ) (hr : 0 < r) :
    Submodule.map ((toCuspSubcarrier F hΦ₀ σ ξ).comp (Submodule.inclusion hYc)) ⊤ ⊓
        (⨆ (μ : ℂ) (_ : r ≤ ‖μ‖), Module.End.eigenspace (Tc : Module.End ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) μ)ᗮ = ⊥ ∨
      Submodule.map ((toCuspSubcarrier F hΦ₀ σ ξ).comp (Submodule.inclusion hYc)) ⊤ ≤
        (⨆ (μ : ℂ) (_ : r ≤ ‖μ‖), Module.End.eigenspace (Tc : Module.End ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) μ)ᗮ  := by
  classical
  haveI : CompleteSpace ↥(cuspSubcarrier F hΦ₀ σ ξ) := by
    unfold cuspSubcarrier; exact (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  set low : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ) :=
    (⨆ (μ : ℂ) (_ : r ≤ ‖μ‖), Module.End.eigenspace (Tc : Module.End ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) μ)ᗮ with hlow
  have hlowc : IsClosed (low : Set ↥(cuspSubcarrier F hΦ₀ σ ξ)) := by
    rw [hlow]; exact Submodule.isClosed_orthogonal _
  have memL : ∀ {φ : AdelicGL2 (𝓞 F) F → ℂ}, φ ∈ Submodule.map (cuspMemberSubmodule F Φ₀ ξ).subtype (Submodule.comap (toCuspSubcarrier F hΦ₀ σ ξ) low) ↔
      ∃ hφ : φ ∈ cuspMemberSubmodule F Φ₀ ξ, toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩ ∈ low := by
    intro φ
    constructor
    · rintro ⟨ψ, hψ, rfl⟩; exact ⟨ψ.2, by simpa using hψ⟩
    · rintro ⟨hφ, hl⟩; exact ⟨⟨φ, hφ⟩, hl, rfl⟩

  have lowStable : ∀ (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)),
      S.comp Tc = Tc.comp S → ∀ v ∈ low, S v ∈ low := by
    intro S hS v hv
    rw [hlow] at hv ⊢
    exact ContinuousLinearMap.map_highPart_orthogonal_le_of_commute hsymm hS r ⟨v, hv, rfl⟩

  have hLk : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion),
      ∀ φ ∈ Submodule.map (cuspMemberSubmodule F Φ₀ ξ).subtype (Submodule.comap (toCuspSubcarrier F hΦ₀ σ ξ) low), rightTranslate F (rowIsometryInclAt₀ F w k) φ ∈ Submodule.map (cuspMemberSubmodule F Φ₀ ξ).subtype (Submodule.comap (toCuspSubcarrier F hΦ₀ σ ξ) low) := by
    intro w k φ hφ
    obtain ⟨hφc, hl⟩ := memL.mp hφ
    obtain ⟨S, hS, hSφ⟩ :=
      AutomorphicForm.CuspidalSpectrum.exists_commute_lift_rightTranslate_rowIsometry_of_isCompact
        F hΦ₀ σ ξ hσ U hU O hO hUO (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F) f hf hsph Tc hcomm w k
    obtain ⟨h', e⟩ := hSφ ⟨φ, hφc⟩
    refine memL.mpr ⟨h', ?_⟩
    rw [← e]; exact lowStable S hS _ hl
  have hLhecke : ∀ g ∈ finiteAdelicGL2Subgroup F, ∀ (n : ℕ) (reps : Fin n → AdelicGL2 (𝓞 F) F),
      (∀ i, ∃ u ∈ U, ∃ u' ∈ U, reps i = u * g * u') →
      (∀ x : AdelicGL2 (𝓞 F) F, (∃ u ∈ U, ∃ u' ∈ U, x = u * g * u') → ∃ i, ∃ u ∈ U, x = reps i * u) →
      (∀ i j, (reps i)⁻¹ * reps j ∈ U → i = j) →
      ∀ φ ∈ Submodule.map (cuspMemberSubmodule F Φ₀ ξ).subtype (Submodule.comap (toCuspSubcarrier F hΦ₀ σ ξ) low) ⊓ Representation.invariants ((rightRegular F).comp U.subtype),
        (fun x => ∑ i, φ (x * reps i)) ∈ Submodule.map (cuspMemberSubmodule F Φ₀ ξ).subtype (Submodule.comap (toCuspSubcarrier F hΦ₀ σ ξ) low) := by
    intro g hg n reps h1 h2 h3 φ hφ
    obtain ⟨hφc, hl⟩ := memL.mp hφ.1
    obtain ⟨S, hS, hSφ⟩ :=
      AutomorphicForm.CuspidalSpectrum.exists_commute_lift_cosetSum_of_isLevelSphericalOfType_of_isCompact
        F hΦ₀ σ ξ hσ U hU O hO hUO (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F) f hf hsph Tc hcomm g hg n reps h1 h2 h3
    obtain ⟨h', e⟩ := hSφ ⟨φ, hφc⟩ hφ.2
    refine memL.mpr ⟨h', ?_⟩
    rw [← e]; exact lowStable S hS _ hl
  have hLconv : ∀ h : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F h → IsArchBiFinite F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F) h →
      (∀ x : AdelicGL2 (𝓞 F) F, ∀ u' ∈ U, h (u' * x) = h x ∧ h (x * u') = h x) →
      ∀ φ ∈ Submodule.map (cuspMemberSubmodule F Φ₀ ξ).subtype (Submodule.comap (toCuspSubcarrier F hΦ₀ σ ξ) low), rightConv F φ h ∈ Submodule.map (cuspMemberSubmodule F Φ₀ ξ).subtype (Submodule.comap (toCuspSubcarrier F hΦ₀ σ ξ) low) := by
    intro h hh hbh hhU φ hφ
    obtain ⟨hφc, hl⟩ := memL.mp hφ
    obtain ⟨S, hS, hSφ⟩ :=
      AutomorphicForm.CuspidalSpectrum.exists_commute_lift_rightConv_of_isArchBiFinite_of_isCompact
        F hΦ₀ σ ξ hσ U hU O hO hUO τ hirr f hf hsph Tc hcomm h hh hbh hhU
    obtain ⟨h', e⟩ := hSφ ⟨φ, hφc⟩
    refine memL.mpr ⟨h', ?_⟩
    rw [← e]; exact lowStable S hS _ hl

  exact AutomorphicForm.CuspidalSpectrum.map_inf_eq_bot_or_le_of_isIrreducibleCuspSubrep_of_isClosed
    F hΦ₀ σ ξ hσ M hM U hU O hO hUO (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F) Y hYc hYM hYU hYt low hlowc hLk hLhecke hLconv

end S_AutomorphicForm_CuspidalSpectrum_map_inf_orthogonal_eq_bot_or_le_of_isIrreducibleCuspSubrep
end P2MW
export P2MW.S_AutomorphicForm_CuspidalSpectrum_map_inf_orthogonal_eq_bot_or_le_of_isIrreducibleCuspSubrep (solution)
