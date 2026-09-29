-- Prove2me | solution 1 for AutomorphicForm.exists_norm_rightConv_le_mul_inv_adelicHeight_pow_of_ideleNorm_det_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/80761f67-006b-5301-abb6-41c612dc3732

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicHeight
import Theorems.Thm_AutomorphicForm_SiegelCovering_exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet
import Theorems.Thm_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre
import Theorems.Thm_AutomorphicForm_exists_norm_rightConv_mul_le_mul_inv_archHeight_pow_of_lt_localHeight_of_isCuspAutomorphicFnAt_of_coversModCentre
import Theorems.Thm_NumberField_AdelicHeight_adelicHeight_globalPoints_mul_of_apply_one_zero_eq_zero
import Theorems.Thm_NumberField_AdelicHeight_exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_norm_rightConv_le_mul_inv_adelicHeight_pow_of_ideleNorm_det_mem_Icc
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain NumberField.TateGlobal NumberField.AdelicHeight

namespace C5aD4a

variable {F : Type} [Field F] [NumberField F]

theorem rightConv_globalPoints_mul {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), φ (globalPoints (𝓞 F) F γ * g) = φ g)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F) :
    rightConv F φ f (globalPoints (𝓞 F) F γ * g) = rightConv F φ f g := by
  rw [← rightConv_comp_mul_left]
  congr 1
  funext x
  exact hφ γ x

theorem le_sum_max_zero {ι : Type*} {s : Finset ι} (g : ι → ℝ) {a : ι} (ha : a ∈ s) :
    g a ≤ ∑ p ∈ s, max (g p) 0 :=
  le_trans (le_max_left (g a) 0)
    (Finset.single_le_sum (f := fun p => max (g p) 0) (fun p _ => le_max_right (g p) 0) ha)

theorem pow_le_archHeight_of_forall_le {c : ℝ} (hc : 0 ≤ c) (g : GL (Fin 2) (InfiniteAdeleRing F))
    (h : ∀ w : InfinitePlace F, c ≤ localHeight (archComponent F w g)) :
    c ^ (∑ w : InfinitePlace F, w.mult) ≤ archHeight F g := by
  unfold archHeight
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod (fun w _ => pow_nonneg hc _) fun w _ => pow_le_pow_left₀ hc (h w) _

theorem archHeight_le_pow_of_forall_le {B : ℝ} (g : GL (Fin 2) (InfiniteAdeleRing F))
    (h : ∀ w : InfinitePlace F, localHeight (archComponent F w g) ≤ B) :
    archHeight F g ≤ B ^ (∑ w : InfinitePlace F, w.mult) := by
  unfold archHeight
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod (fun w _ => pow_nonneg (localHeight_pos _).le _) fun w _ =>
    pow_le_pow_left₀ (localHeight_pos _).le (h w) _

end C5aD4a

open C5aD4a in
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
    (α β : ℝ) (hα : 0 < α) (k : ℕ) :
    ∃ H₀ Cst : ℝ, ∀ h : AdelicGL2 (𝓞 F) F,
      ideleNorm F (Matrix.GeneralLinearGroup.det h) ∈ Set.Icc α β → H₀ ≤ adelicHeight F h →
        ‖rightConv F φ f h‖ ≤ Cst * (adelicHeight F h)⁻¹ ^ k := by
  classical

  have hls : IsLsXiFunction (𝓞 F) F _ ξ φ := by
    letI := (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).mS
    exact ((lsXiMemberAt_iff _ _ _ _ ξ _ φ).mp hφ.1).1

  obtain ⟨T₀, c₀, hc₀, u₀, hcov₀⟩ :=
    AutomorphicForm.SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet F
  have hcov₁ := hcov₀ 1 2 two_pos (by norm_num)
  obtain ⟨N, hN⟩ := AutomorphicForm.exists_finset_central_slab_covering_of_coversModCentre F c₀ u₀ 1 2 T₀
    (by norm_num) hcov₁ α β hα
  choose Ccap Cdec hdec using fun t : AdelicGL2 (𝓞 F) F =>
    AutomorphicForm.exists_norm_rightConv_mul_le_mul_inv_archHeight_pow_of_lt_localHeight_of_isCuspAutomorphicFnAt_of_coversModCentre
      F c u d₁ d₂ T hd hcov ξ φ hφ hcont f hf c₀ u₀ 1 2 t hc₀ one_pos k

  set P : Finset ((AdeleRing (𝓞 F) F)ˣ × AdelicGL2 (𝓞 F) F) := N ×ˢ T₀ with hPdef
  set tr : (AdeleRing (𝓞 F) F)ˣ × AdelicGL2 (𝓞 F) F → AdelicGL2 (𝓞 F) F :=
    fun p => centralScalar (𝓞 F) F p.1 * p.2 with htrdef
  obtain ⟨κ, K, hκ, hdist⟩ :=
    NumberField.AdelicHeight.exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact F
      (↑(P.image tr)) (P.image tr).finite_toSet.isCompact

  set m : ℕ := ∑ w : InfinitePlace F, w.mult with hmdef
  set A₀ : ℝ := c₀ ^ m with hA₀def
  have hA₀ : 0 < A₀ := pow_pos hc₀ _
  set CcapS : ℝ := ∑ p ∈ P, max (Ccap (tr p)) 0 with hCcapSdef
  set CS : ℝ := ∑ p ∈ P, max (Cdec (tr p)) 0 with hCSdef
  have hCS : 0 ≤ CS := Finset.sum_nonneg fun _ _ => le_max_right _ _
  set B : ℝ := (max CcapS 1) ^ m with hBdef
  refine ⟨max (1 / (κ * A₀) + 1) (K * B + 1), CS * K ^ k, fun h hdet hH => ?_⟩

  obtain ⟨γ, n, hn, x, hx, hmem⟩ := hN h hdet
  obtain ⟨s, hs, hsg⟩ := hmem
  have hsg' : s * (centralScalar (𝓞 F) F n * x) = globalPoints (𝓞 F) F γ * h := hsg
  have hp : (n, x) ∈ P := Finset.mem_product.mpr ⟨hn, hx⟩
  have htrC : tr (n, x) ∈ (↑(P.image tr) : Set (AdelicGL2 (𝓞 F) F)) :=
    Finset.mem_coe.mpr (Finset.mem_image_of_mem tr hp)
  have htr : tr (n, x) = centralScalar (𝓞 F) F n * x := rfl
  obtain ⟨hs1, hs2, -, -⟩ := mem_centreCutSiegelSet_iff.mp hs
  have hHs : adelicHeight F s = archHeight F (glArch (𝓞 F) F s) := adelicHeight_eq_archHeight_of_mem hs1
  have hfloor : A₀ ≤ archHeight F (glArch (𝓞 F) F s) := pow_le_archHeight_of_forall_le hc₀.le _ hs2
  have hApos := archHeight_pos F (glArch (𝓞 F) F s)
  have hHpos := adelicHeight_pos h
  have hHspos := adelicHeight_pos s
  obtain ⟨hlo, hhi⟩ := hdist s (tr (n, x)) htrC
  rw [htr, hsg'] at hlo hhi
  have hH1 : 1 / (κ * A₀) + 1 ≤ adelicHeight F h := (le_max_left _ _).trans hH
  have hH2 : K * B + 1 ≤ adelicHeight F h := (le_max_right _ _).trans hH

  have hγh_ge : κ * A₀ ≤ adelicHeight F (globalPoints (𝓞 F) F γ * h) := by
    calc κ * A₀ ≤ κ * adelicHeight F s := by
          rw [hHs]; exact mul_le_mul_of_nonneg_left hfloor hκ.le
      _ ≤ _ := hlo
  have hκA := mul_pos hκ hA₀
  have hγ10 : (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    by_contra hne
    have hle := adelicHeight_globalPoints_mul_mul_adelicHeight_le_one γ hne h
    have hgt : 1 < adelicHeight F (globalPoints (𝓞 F) F γ * h) * adelicHeight F h := by
      calc (1 : ℝ) < κ * A₀ * (1 / (κ * A₀) + 1) := by
            rw [mul_add, mul_one_div_cancel hκA.ne', mul_one]; linarith
        _ ≤ _ := mul_le_mul hγh_ge hH1 (by positivity) (adelicHeight_pos _).le
    linarith
  have hHeq : adelicHeight F (globalPoints (𝓞 F) F γ * h) = adelicHeight F h :=
    NumberField.AdelicHeight.adelicHeight_globalPoints_mul_of_apply_one_zero_eq_zero F γ hγ10 h
  rw [hHeq] at hhi

  have hK : 0 < K := (mul_pos_iff_of_pos_right hHspos).mp (hHpos.trans_le hhi)
  have harch_ge : adelicHeight F h / K ≤ archHeight F (glArch (𝓞 F) F s) := by
    rw [div_le_iff₀ hK, ← hHs, mul_comm]; exact hhi
  have hCcap_le : Ccap (centralScalar (𝓞 F) F n * x) ≤ CcapS := by
    rw [← htr, hCcapSdef]
    exact le_sum_max_zero (fun p => Ccap (tr p)) hp
  have hC_le : Cdec (centralScalar (𝓞 F) F n * x) ≤ CS := by
    rw [← htr, hCSdef]
    exact le_sum_max_zero (fun p => Cdec (tr p)) hp

  have hw : ∃ w : InfinitePlace F,
      Ccap (centralScalar (𝓞 F) F n * x) < localHeight (archComponent F w (glArch (𝓞 F) F s)) := by
    by_contra hall
    push Not at hall
    have hB : archHeight F (glArch (𝓞 F) F s) ≤ B :=
      archHeight_le_pow_of_forall_le _ fun w => ((hall w).trans hCcap_le).trans (le_max_left _ _)
    have : adelicHeight F h ≤ K * B := by
      rw [← div_le_iff₀' hK]; exact harch_ge.trans hB
    linarith

  have hbound := hdec (centralScalar (𝓞 F) F n * x) s hs hw
  rw [← rightConv_globalPoints_mul hls.left_invariant f γ h, ← hsg']
  refine hbound.trans ?_
  have hinv : (archHeight F (glArch (𝓞 F) F s))⁻¹ ≤ K * (adelicHeight F h)⁻¹ := by
    have := inv_anti₀ (div_pos hHpos hK) harch_ge
    rwa [inv_div, div_eq_mul_inv] at this
  calc Cdec (centralScalar (𝓞 F) F n * x) * (archHeight F (glArch (𝓞 F) F s))⁻¹ ^ k
      ≤ CS * (K * (adelicHeight F h)⁻¹) ^ k :=
        mul_le_mul hC_le (pow_le_pow_left₀ (inv_nonneg.mpr hApos.le) hinv k) (by positivity) hCS
    _ = CS * K ^ k * (adelicHeight F h)⁻¹ ^ k := by rw [mul_pow]; ring

end S_AutomorphicForm_exists_norm_rightConv_le_mul_inv_adelicHeight_pow_of_ideleNorm_det_mem_Icc
end P2MW
export P2MW.S_AutomorphicForm_exists_norm_rightConv_le_mul_inv_adelicHeight_pow_of_ideleNorm_det_mem_Icc (solution)
