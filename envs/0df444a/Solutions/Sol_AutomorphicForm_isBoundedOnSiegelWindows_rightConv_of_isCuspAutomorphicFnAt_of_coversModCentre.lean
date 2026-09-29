-- Prove2me | solution 1 for AutomorphicForm.isBoundedOnSiegelWindows_rightConv_of_isCuspAutomorphicFnAt_of_coversModCentre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/3af811c0-c566-577a-a403-0959e55eb45e

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Theorems.Thm_AutomorphicForm_continuous_rightConv_and_contDiff_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_exists_norm_rightConv_mul_le_of_lt_localHeight_of_isCuspAutomorphicFnAt_of_coversModCentre
import Theorems.Thm_AutomorphicForm_WindowedSiegel_isCompact_centreCutSiegelSet_inter_heightCap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isBoundedOnSiegelWindows_rightConv_of_isCuspAutomorphicFnAt_of_coversModCentre
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm

theorem solution
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (χ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : IsCuspAutomorphicFnAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) χ φ)
    (hcont : Continuous φ)
    (f : AdelicGL2 (𝓞 K) K → ℂ)
    (hf : IsFactorizableTestFn K f) :
    IsBoundedOnSiegelWindows K (rightConv K φ f) := by
  intro c' u' d₁' d₂' T' hc' hd₁'

  have key : ∀ t : AdelicGL2 (𝓞 K) K, ∃ C : ℝ, ∀ s ∈ centreCutSiegelSet K c' u' d₁' d₂',
      ‖rightConv K φ f (s * t)‖ ≤ C := by
    intro t
    obtain ⟨Ccap, C₁, hhigh⟩ :=
      exists_norm_rightConv_mul_le_of_lt_localHeight_of_isCuspAutomorphicFnAt_of_coversModCentre K c u d₁ d₂ T hd
        hcov χ φ hφ hcont f hf c' u' d₁' d₂' t hc' hd₁'
    have hcpt : IsCompact (centreCutSiegelSet K c' u' d₁' d₂' ∩
        {g | ∀ w : InfinitePlace K, localHeight (archComponent K w (glArch (𝓞 K) K g)) ≤ Ccap}) :=
      isCompact_centreCutSiegelSet_inter_heightCap K hc' hd₁'
    have hcont' : Continuous (rightConv K φ f) :=
      (continuous_rightConv_and_contDiff_of_isFactorizableTestFn K φ hcont f hf).1
    have hmul : Continuous fun a : AdelicGL2 (𝓞 K) K => a * t := continuous_id.mul continuous_const
    obtain ⟨C₂, hC₂⟩ := (hcpt.image hmul).exists_bound_of_continuousOn hcont'.continuousOn
    refine ⟨max C₁ C₂, fun s hs => ?_⟩
    by_cases hcap : ∀ w : InfinitePlace K, localHeight (archComponent K w (glArch (𝓞 K) K s)) ≤ Ccap
    · exact (hC₂ (s * t) ⟨s, ⟨hs, hcap⟩, rfl⟩).trans (le_max_right _ _)
    · simp only [not_forall, not_le] at hcap
      exact (hhigh s hs hcap).trans (le_max_left _ _)
  choose Cof hCof using key
  refine ⟨∑ t ∈ T', max (Cof t) 0, fun g hg => ?_⟩
  obtain ⟨t, ht, hg'⟩ := Set.mem_iUnion₂.mp hg
  obtain ⟨s, hs, rfl⟩ := hg'
  calc ‖rightConv K φ f (s * t)‖ ≤ Cof t := hCof t s hs
    _ ≤ max (Cof t) 0 := le_max_left _ _
    _ ≤ ∑ t ∈ T', max (Cof t) 0 :=
        Finset.single_le_sum (f := fun t => max (Cof t) 0) (fun i _ => le_max_right _ _) ht

end S_AutomorphicForm_isBoundedOnSiegelWindows_rightConv_of_isCuspAutomorphicFnAt_of_coversModCentre
end P2MW
export P2MW.S_AutomorphicForm_isBoundedOnSiegelWindows_rightConv_of_isCuspAutomorphicFnAt_of_coversModCentre (solution)
