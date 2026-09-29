-- Prove2me | solution 1 for AutomorphicForm.exists_forall_norm_rightConv_le_of_ideleNorm_det_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/8291a20e-dc0a-51ed-b9c9-06062a828db0

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicHeight
import Theorems.Thm_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre
import Theorems.Thm_AutomorphicForm_isBoundedOnSiegelWindows_rightConv_of_isCuspAutomorphicFnAt_of_coversModCentre
import Theorems.Thm_AutomorphicForm_SiegelCovering_exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_norm_rightConv_le_of_ideleNorm_det_mem_Icc
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain NumberField.TateGlobal NumberField.AdelicHeight

namespace C5aD1

variable {F : Type} [Field F] [NumberField F]

theorem centralScalar_mul_comm (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    g * centralScalar (𝓞 F) F z = centralScalar (𝓞 F) F z * g := by
  refine Units.ext ?_
  simp only [Units.val_mul, centralScalar]
  exact ((Matrix.scalar_commute (n := Fin 2) (z : AdeleRing (𝓞 F) F) (fun r => Commute.all _ r)
    (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))).eq).symm

theorem rightConv_globalPoints_mul {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), φ (globalPoints (𝓞 F) F γ * g) = φ g)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F) :
    rightConv F φ f (globalPoints (𝓞 F) F γ * g) = rightConv F φ f g := by
  rw [← rightConv_comp_mul_left]
  congr 1
  funext x
  exact hφ γ x

theorem rightConv_centralScalar_mul {φ : AdelicGL2 (𝓞 F) F → ℂ} {z : (AdeleRing (𝓞 F) F)ˣ} {cz : ℂ}
    (hφ : ∀ g : AdelicGL2 (𝓞 F) F, φ (centralScalar (𝓞 F) F z * g) = cz * φ g)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) :
    rightConv F φ f (centralScalar (𝓞 F) F z * g) = cz * rightConv F φ f g := by
  rw [← rightConv_comp_mul_left]
  simp only [rightConv, hφ, mul_assoc]
  exact integral_const_mul _ _

end C5aD1

open C5aD1 in
theorem solution
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsCuspAutomorphicFnAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ φ)
    (hcont : Continuous φ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (α β : ℝ) (hα : 0 < α) :
    ∃ M : ℝ, ∀ g : AdelicGL2 (𝓞 F) F,
      ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β → ‖rightConv F φ f g‖ ≤ M := by
  classical

  have hls : IsLsXiFunction (𝓞 F) F _ ξ φ := by
    letI := (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).mS
    exact ((lsXiMemberAt_iff _ _ _ _ ξ _ φ).mp hφ.1).1
  have hZ : ∀ n : (AdeleRing (𝓞 F) F)ˣ, n ∈ (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z := fun n => by
    rw [productionPinsOf_Z]; exact Subgroup.mem_top n

  obtain ⟨T₀, c₀, hc₀, u₀, hcov₀⟩ :=
    AutomorphicForm.SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet F
  have hcov₁ := hcov₀ 1 2 two_pos (by norm_num)
  obtain ⟨N, hN⟩ := AutomorphicForm.exists_finset_central_slab_covering_of_coversModCentre F c₀ u₀ 1 2 T₀
    (by norm_num) hcov₁ α β hα

  obtain ⟨C', hC'⟩ :=
    (AutomorphicForm.isBoundedOnSiegelWindows_rightConv_of_isCuspAutomorphicFnAt_of_coversModCentre F c u d₁ d₂ T
      hd hcov ξ φ hφ hcont f hf) c₀ u₀ 1 2 T₀ hc₀ one_pos
  refine ⟨(∑ n ∈ N, ‖((ξ ⟨n, hZ n⟩ : ℂˣ) : ℂ)‖) * max C' 0, fun g hg => ?_⟩
  obtain ⟨γ, n, hn, x, hx, hmem⟩ := hN g hg
  obtain ⟨s, hs, hsg⟩ := hmem

  have hsg' : s * (centralScalar (𝓞 F) F n * x) = globalPoints (𝓞 F) F γ * g := hsg
  have h1 : rightConv F φ f g = ((ξ ⟨n, hZ n⟩ : ℂˣ) : ℂ) * rightConv F φ f (s * x) := by
    rw [← rightConv_globalPoints_mul hls.left_invariant f γ g, ← hsg', ← mul_assoc, centralScalar_mul_comm,
      mul_assoc]
    exact rightConv_centralScalar_mul (fun g' => hls.central_transform ⟨n, hZ n⟩ g') f (s * x)
  have h2 : ‖rightConv F φ f (s * x)‖ ≤ max C' 0 :=
    (hC' (s * x) (Set.mem_iUnion₂.mpr ⟨x, hx, s, hs, rfl⟩)).trans (le_max_left _ _)
  have h3 : ‖((ξ ⟨n, hZ n⟩ : ℂˣ) : ℂ)‖ ≤ ∑ m ∈ N, ‖((ξ ⟨m, hZ m⟩ : ℂˣ) : ℂ)‖ :=
    Finset.single_le_sum (f := fun m => ‖((ξ ⟨m, hZ m⟩ : ℂˣ) : ℂ)‖) (fun _ _ => norm_nonneg _) hn
  rw [h1, norm_mul]
  exact mul_le_mul h3 h2 (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)

end S_AutomorphicForm_exists_forall_norm_rightConv_le_of_ideleNorm_det_mem_Icc
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_norm_rightConv_le_of_ideleNorm_det_mem_Icc (solution)
