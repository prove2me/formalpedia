-- Prove2me | solution 1 for AutomorphicForm.isRapidlyDecreasingOnSiegelSets_rightConv_of_isCuspAutomorphicFnAt_of_norm_apply_eq_one_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/28534d7b-22ca-5419-8b5d-3a5425568d55

import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Theorems.Thm_AutomorphicForm_exists_norm_rightConv_mul_le_mul_inv_archHeight_pow_of_lt_localHeight_of_isCuspAutomorphicFnAt_of_coversModCentre
import Theorems.Thm_AutomorphicForm_isBoundedOnSiegelWindows_rightConv_of_isCuspAutomorphicFnAt_of_coversModCentre
import Definitions.Def_NumberField_AdelicVolume
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isRapidlyDecreasingOnSiegelSets_rightConv_of_isCuspAutomorphicFnAt_of_norm_apply_eq_one_rat
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering LanglandsTunnell.RankinSelberg

namespace RapidGlueRat

open AutomorphicForm NumberField NumberField.AdelicLevel

theorem archHeight_rat (w : InfinitePlace ℚ) (x : GL (Fin 2) (InfiniteAdeleRing ℚ)) :
    archHeight ℚ x = WindowedSiegel.localHeight (archComponent ℚ w x) := by
  unfold archHeight
  rw [Fintype.prod_subsingleton _ w]
  have : w.mult = 1 := by
    rw [NumberField.InfinitePlace.mult, if_pos (SiegelCovering.isReal_infinitePlace_rat w)]
  rw [this, pow_one]

end RapidGlueRat

open NumberField.AdelicVolume in
theorem solution
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (χ : (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ)).Z →* ℂˣ)
    (hχu : ∀ z, ‖((χ z : ℂˣ) : ℂ)‖ = 1)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hφ : IsCuspAutomorphicFnAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ)) χ φ)
    (hcont : Continuous φ)
    (f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hf : IsFactorizableTestFn ℚ f) :
    IsRapidlyDecreasingOnSiegelSets ℚ (rightConv ℚ φ f) := by
  classical
  intro c' u' t hc' N
  set Fφ := rightConv ℚ φ f with hF
  obtain ⟨Ccap, C₁, hA⟩ :=
    AutomorphicForm.exists_norm_rightConv_mul_le_mul_inv_archHeight_pow_of_lt_localHeight_of_isCuspAutomorphicFnAt_of_coversModCentre ℚ c u d₁ d₂ T hd hcov χ φ hφ hcont f hf c' u' 1 4 t hc' one_pos N
  obtain ⟨C₂, hB⟩ :=
    (AutomorphicForm.isBoundedOnSiegelWindows_rightConv_of_isCuspAutomorphicFnAt_of_coversModCentre ℚ c u d₁ d₂ T hd hcov χ φ hφ hcont f hf) c' u' 1 4 {t} hc' one_pos
  refine ⟨max (|C₁| * (1 + c'⁻¹) ^ N) (|C₂| * (1 + |Ccap|) ^ N), ?_⟩
  intro g hg

  set v₀ : InfinitePlace ℚ := default with hv₀
  have h2 : (2 : v₀.Completion) ≠ 0 := by
    have := norm_two_completion (F := ℚ) v₀
    intro h; rw [h, norm_zero] at this; norm_num at this
  obtain ⟨n, hn⟩ := exists_mem_Ico_zpow (archDetNorm_pos v₀ g) (by norm_num : (1 : ℝ) < 4)
  set a : (v₀.Completion)ˣ := (Units.mk0 (2 : v₀.Completion) h2) ^ (-n) with ha
  set z := archCentralUnit ℚ v₀ a with hz
  set s := centralScalar (𝓞 ℚ) ℚ z * g with hs
  have hna : ‖(a : v₀.Completion)‖ * ‖(a : v₀.Completion)‖ = (4 : ℝ) ^ (-n) := by
    rw [ha, Units.val_zpow_eq_zpow_val, Units.val_mk0, norm_zpow, norm_two_completion, ← mul_zpow]
    norm_num
  have hdet : archDetNorm v₀ s ∈ Set.Icc (1 : ℝ) 4 := by
    rw [hs, hz, archDetNorm_centralScalar_mul, hna]
    obtain ⟨h1, h2'⟩ := hn
    have h4 : (0 : ℝ) < 4 ^ n := zpow_pos (by norm_num) n
    constructor
    · rw [zpow_neg, ← div_eq_inv_mul, le_div_iff₀ h4]; linarith
    · rw [zpow_neg, ← div_eq_inv_mul, div_le_iff₀ h4, zpow_add_one₀ (by norm_num)] at *; linarith

  have hsW : s ∈ integralWindowedSiegelSet ℚ c' u' :=
    centralScalar_mul_mem_integralWindowedSiegelSet (archCentralUnit_snd v₀ a) (archCentralUnit_fst_ne_zero v₀ a) hg
  have hHs : archHeight ℚ (glArch (𝓞 ℚ) ℚ s) = archHeight ℚ (glArch (𝓞 ℚ) ℚ g) := by
    rw [hs, map_mul]
    refine archHeight_scalar_entries_mul ℚ (archCentralUnit_fst_ne_zero v₀ a) ?_ ?_ ?_ ?_ _
    · rw [glArch_apply, centralScalar_apply_eq]
    · rw [glArch_apply, centralScalar_apply_ne _ (by decide)]; rfl
    · rw [glArch_apply, centralScalar_apply_ne _ (by decide)]; rfl
    · rw [glArch_apply, centralScalar_apply_eq]
  have hsC : s ∈ centreCutSiegelSet ℚ c' u' 1 4 := by
    obtain ⟨hfin, hH, hx⟩ := hsW
    refine ⟨hfin, fun w => ?_, hx, fun w => ?_⟩
    · rw [← RapidGlueRat.archHeight_rat]; exact hH
    · rw [Subsingleton.elim w v₀]; exact hdet

  have hinv : ‖Fφ (s * t)‖ = ‖Fφ (g * t)‖ := by
    have hLs : IsLsXiFunction (𝓞 ℚ) ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ)).Z χ φ := by
      letI : MeasurableSpace (AdelicGL2 (𝓞 ℚ) ℚ) := (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ)).mS
      exact ((lsXiMemberAt_iff (𝓞 ℚ) ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ)).μ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ)).Z χ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ)).D φ).mp hφ.1).1
    have key : Fφ (s * t) = ((χ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * Fφ (g * t) := by
      rw [hF, hs, mul_assoc, rightConv_apply, rightConv_apply, ← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show φ (centralScalar (𝓞 ℚ) ℚ z * (g * t) * x) * f x = _
      rw [mul_assoc (centralScalar (𝓞 ℚ) ℚ z), hLs.central_transform ⟨z, Subgroup.mem_top z⟩, mul_assoc]
    rw [key, norm_mul, hχu, one_mul]
  have hHpos : 0 < archHeight ℚ (glArch (𝓞 ℚ) ℚ g) := archHeight_pos ℚ _
  have hHc : c' ≤ archHeight ℚ (glArch (𝓞 ℚ) ℚ g) := hg.2.1
  rw [← hinv]
  by_cases hcap : Ccap < WindowedSiegel.localHeight (archComponent ℚ v₀ (glArch (𝓞 ℚ) ℚ s))
  ·
    have h1 := hA s hsC ⟨v₀, hcap⟩
    rw [hHs] at h1
    refine le_trans ?_ (le_max_left _ _)
    have hq : (1 + archHeight ℚ (glArch (𝓞 ℚ) ℚ g)) / archHeight ℚ (glArch (𝓞 ℚ) ℚ g) ≤ 1 + c'⁻¹ := by
      rw [add_div, div_self hHpos.ne', one_div]
      have := inv_anti₀ hc' hHc
      linarith
    calc ‖Fφ (s * t)‖ * (1 + archHeight ℚ (glArch (𝓞 ℚ) ℚ g)) ^ N
        ≤ C₁ * (archHeight ℚ (glArch (𝓞 ℚ) ℚ g))⁻¹ ^ N * (1 + archHeight ℚ (glArch (𝓞 ℚ) ℚ g)) ^ N := by
          gcongr
      _ = C₁ * ((1 + archHeight ℚ (glArch (𝓞 ℚ) ℚ g)) / archHeight ℚ (glArch (𝓞 ℚ) ℚ g)) ^ N := by
          rw [div_eq_mul_inv, mul_pow]; try ring
      _ ≤ |C₁| * ((1 + archHeight ℚ (glArch (𝓞 ℚ) ℚ g)) / archHeight ℚ (glArch (𝓞 ℚ) ℚ g)) ^ N :=
          mul_le_mul_of_nonneg_right (le_abs_self _)
            (pow_nonneg (div_nonneg (by linarith [hHpos.le]) hHpos.le) N)
      _ ≤ |C₁| * (1 + c'⁻¹) ^ N := by
          gcongr
  ·
    push Not at hcap
    have hHle : archHeight ℚ (glArch (𝓞 ℚ) ℚ g) ≤ |Ccap| := by
      rw [← hHs, RapidGlueRat.archHeight_rat v₀]; exact hcap.trans (le_abs_self _)
    have h2 : ‖Fφ (s * t)‖ ≤ C₂ := hB (s * t) (by
      simp only [Finset.mem_singleton, Set.mem_iUnion, Set.mem_image, exists_prop]
      exact ⟨t, rfl, s, hsC, rfl⟩)
    refine le_trans ?_ (le_max_right _ _)
    calc ‖Fφ (s * t)‖ * (1 + archHeight ℚ (glArch (𝓞 ℚ) ℚ g)) ^ N
        ≤ C₂ * (1 + archHeight ℚ (glArch (𝓞 ℚ) ℚ g)) ^ N := by gcongr
      _ ≤ |C₂| * (1 + archHeight ℚ (glArch (𝓞 ℚ) ℚ g)) ^ N :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg (by linarith [hHpos.le]) N)
      _ ≤ |C₂| * (1 + |Ccap|) ^ N := by gcongr

end S_AutomorphicForm_isRapidlyDecreasingOnSiegelSets_rightConv_of_isCuspAutomorphicFnAt_of_norm_apply_eq_one_rat
end P2MW
export P2MW.S_AutomorphicForm_isRapidlyDecreasingOnSiegelSets_rightConv_of_isCuspAutomorphicFnAt_of_norm_apply_eq_one_rat (solution)
