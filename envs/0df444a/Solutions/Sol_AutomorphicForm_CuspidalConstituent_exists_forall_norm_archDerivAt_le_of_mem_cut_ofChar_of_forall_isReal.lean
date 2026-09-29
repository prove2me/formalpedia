-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.exists_forall_norm_archDerivAt_le_of_mem_cut_ofChar_of_forall_isReal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/6af2142d-601b-5927-9206-3401fb15cd6f

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_iterate_lower_mem_cut_ofChar_and_iterate_raise_mem_cut_ofChar
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_isArchSmoothAt_and_continuous_foldr_archDerivAt_of_mem_cut
import Theorems.Thm_AutomorphicForm_archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_norm_le_mul_ideleNorm_det_rpow_of_isCuspConstituent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_exists_forall_norm_archDerivAt_le_of_mem_cut_ofChar_of_forall_isReal
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

noncomputable section

namespace BddSlab25

variable {K : Type} [Field K] [NumberField K]

def Bdd (e₁ e₂ : ℝ) (f : AdelicGL2 (𝓞 K) K → ℂ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ g : AdelicGL2 (𝓞 K) K,
    NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ → ‖f g‖ ≤ C

theorem Bdd.add {e₁ e₂ : ℝ} {f₁ f₂ : AdelicGL2 (𝓞 K) K → ℂ} (h₁ : Bdd e₁ e₂ f₁) (h₂ : Bdd e₁ e₂ f₂) :
    Bdd e₁ e₂ (f₁ + f₂) := by
  obtain ⟨C₁, hC₁, h₁⟩ := h₁
  obtain ⟨C₂, hC₂, h₂⟩ := h₂
  refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, fun g hg => ?_⟩
  rw [Pi.add_apply]
  exact (norm_add_le _ _).trans (add_le_add (h₁ g hg) (h₂ g hg))

theorem Bdd.smul {e₁ e₂ : ℝ} {f : AdelicGL2 (𝓞 K) K → ℂ} (h : Bdd e₁ e₂ f) (a : ℂ) : Bdd e₁ e₂ (a • f) := by
  obtain ⟨C, hC, h⟩ := h
  refine ⟨‖a‖ * C, mul_nonneg (norm_nonneg _) hC, fun g hg => ?_⟩
  rw [Pi.smul_apply, smul_eq_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (h g hg) (norm_nonneg _)

theorem Bdd.sub {e₁ e₂ : ℝ} {f₁ f₂ : AdelicGL2 (𝓞 K) K → ℂ} (h₁ : Bdd e₁ e₂ f₁) (h₂ : Bdd e₁ e₂ f₂) :
    Bdd e₁ e₂ (f₁ - f₂) := by
  have h : f₁ - f₂ = f₁ + (-1 : ℂ) • f₂ := by
    funext g; simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [h]
  exact h₁.add (h₂.smul _)

theorem Bdd.of_le₃ {e₁ e₂ : ℝ} {f f₁ f₂ f₃ : AdelicGL2 (𝓞 K) K → ℂ} (h₁ : Bdd e₁ e₂ f₁) (h₂ : Bdd e₁ e₂ f₂)
    (h₃ : Bdd e₁ e₂ f₃) (a : ℝ) (ha : 0 ≤ a)
    (hle : ∀ g, ‖f g‖ ≤ ‖f₁ g‖ + ‖f₂ g‖ + a * ‖f₃ g‖) : Bdd e₁ e₂ f := by
  obtain ⟨C₁, hC₁, h₁⟩ := h₁
  obtain ⟨C₂, hC₂, h₂⟩ := h₂
  obtain ⟨C₃, hC₃, h₃⟩ := h₃
  refine ⟨C₁ + C₂ + a * C₃, by positivity, fun g hg => (hle g).trans ?_⟩
  exact add_le_add (add_le_add (h₁ g hg) (h₂ g hg)) (mul_le_mul_of_nonneg_left (h₃ g hg) ha)

theorem Bdd.of_rpow {e₁ e₂ : ℝ} (he₁ : 0 < e₁) {z : AdelicGL2 (𝓞 K) K → ℂ} {a : ℝ}
    (h : ∃ M : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
      ‖z g‖ ≤ M * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ a) :
    Bdd e₁ e₂ z := by
  obtain ⟨M, hM⟩ := h
  refine ⟨|M| * max (e₁ ^ a) (e₂ ^ a), mul_nonneg (abs_nonneg _)
    ((Real.rpow_nonneg he₁.le a).trans (le_max_left _ _)), fun g hg => (hM g).trans ?_⟩
  set t := NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) with ht
  have ht0 : 0 ≤ t ^ a := Real.rpow_nonneg (he₁.le.trans hg.1) a
  have hta : t ^ a ≤ max (e₁ ^ a) (e₂ ^ a) := by
    rcases le_or_gt 0 a with ha | ha
    · exact (Real.rpow_le_rpow (he₁.le.trans hg.1) hg.2 ha).trans (le_max_right _ _)
    · exact (Real.rpow_le_rpow_of_nonpos he₁ hg.1 ha.le).trans (le_max_left _ _)
  exact (mul_le_mul_of_nonneg_right (le_abs_self M) ht0).trans (mul_le_mul_of_nonneg_left hta (abs_nonneg _))

variable {w : InfinitePlace K}

def Lo (hw : w.IsReal) (x : AdelicGL2 (𝓞 K) K → ℂ) : AdelicGL2 (𝓞 K) K → ℂ :=
  archDerivAt hw .H x - Complex.I • (archDerivAt hw .E x + archDerivAt hw .Fm x)

def Ra (hw : w.IsReal) (x : AdelicGL2 (𝓞 K) K → ℂ) : AdelicGL2 (𝓞 K) K → ℂ :=
  archDerivAt hw .H x + Complex.I • (archDerivAt hw .E x + archDerivAt hw .Fm x)

theorem two_I_ne_zero : (2 * Complex.I : ℂ) ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero

theorem archDerivAt_H_eq (hw : w.IsReal) (x : AdelicGL2 (𝓞 K) K → ℂ) :
    archDerivAt hw .H x = (1 / 2 : ℂ) • (Lo hw x + Ra hw x) := by
  funext g
  simp only [Lo, Ra, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem archDerivAt_E_eq (hw : w.IsReal) (m : ℤ) (x : AdelicGL2 (𝓞 K) K → ℂ) (hxs : IsArchSmoothAt hw x)
    (hxm : HasArchCharacterAt₀ K w (archWeightCharAt hw m) x) :
    archDerivAt hw .E x =
      ((2 * Complex.I)⁻¹ / 2 : ℂ) • (Ra hw x - Lo hw x) + (Complex.I * m / 2 : ℂ) • x := by
  have hW := AutomorphicForm.archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt K w hw m x hxs hxm
  have hκ : ((2 * Complex.I)⁻¹ : ℂ) * (2 * Complex.I) = 1 := inv_mul_cancel₀ two_I_ne_zero
  funext g
  have hWg := congrFun hW g
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hWg
  simp only [Lo, Ra, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (-(archDerivAt hw .E x g + archDerivAt hw .Fm x g) / 2) * hκ + (1 / 2 : ℂ) * hWg

theorem archDerivAt_Fm_eq (hw : w.IsReal) (m : ℤ) (x : AdelicGL2 (𝓞 K) K → ℂ) (hxs : IsArchSmoothAt hw x)
    (hxm : HasArchCharacterAt₀ K w (archWeightCharAt hw m) x) :
    archDerivAt hw .Fm x =
      ((2 * Complex.I)⁻¹ / 2 : ℂ) • (Ra hw x - Lo hw x) - (Complex.I * m / 2 : ℂ) • x := by
  have hW := AutomorphicForm.archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt K w hw m x hxs hxm
  have hκ : ((2 * Complex.I)⁻¹ : ℂ) * (2 * Complex.I) = 1 := inv_mul_cancel₀ two_I_ne_zero
  funext g
  have hWg := congrFun hW g
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hWg
  simp only [Lo, Ra, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (-(archDerivAt hw .E x g + archDerivAt hw .Fm x g) / 2) * hκ - (1 / 2 : ℂ) * hWg

theorem bdd_archDerivAt {e₁ e₂ : ℝ} (hw : w.IsReal) (m : ℤ) {x : AdelicGL2 (𝓞 K) K → ℂ}
    (hxs : IsArchSmoothAt hw x) (hxm : HasArchCharacterAt₀ K w (archWeightCharAt hw m) x)
    (h0 : Bdd e₁ e₂ x) (hL : Bdd e₁ e₂ (Lo hw x)) (hR : Bdd e₁ e₂ (Ra hw x)) (d : ArchDir) :
    Bdd e₁ e₂ (archDerivAt hw d x) := by
  cases d
  · rw [archDerivAt_H_eq hw x]
    exact (hL.add hR).smul _
  · rw [archDerivAt_E_eq hw m x hxs hxm]
    exact ((hR.sub hL).smul _).add (h0.smul _)
  · rw [archDerivAt_Fm_eq hw m x hxs hxm]
    exact ((hR.sub hL).smul _).sub (h0.smul _)

theorem archDerivAt_sub' {hw : w.IsReal} {φ ψ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : IsArchSmoothAt hw φ) (hψ : IsArchSmoothAt hw ψ) (d : ArchDir) :
    archDerivAt hw d (φ - ψ) = archDerivAt hw d φ - archDerivAt hw d ψ := by
  have h1 : φ - ψ = φ + (-1 : ℂ) • ψ := by
    funext g; simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [h1, archDerivAt_add hφ (hψ.smul _) d, archDerivAt_smul]
  funext g; simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

theorem bdd_archDerivAt₂ {e₁ e₂ : ℝ} (hw : w.IsReal) (m : ℤ) {x : AdelicGL2 (𝓞 K) K → ℂ}
    (hxs : IsArchSmoothAt hw x) (hxm : HasArchCharacterAt₀ K w (archWeightCharAt hw m) x)
    (hLs : IsArchSmoothAt hw (Lo hw x)) (hRs : IsArchSmoothAt hw (Ra hw x))
    (d d' : ArchDir) (h0 : Bdd e₁ e₂ (archDerivAt hw d x)) (hL : Bdd e₁ e₂ (archDerivAt hw d (Lo hw x)))
    (hR : Bdd e₁ e₂ (archDerivAt hw d (Ra hw x))) :
    Bdd e₁ e₂ (archDerivAt hw d (archDerivAt hw d' x)) := by
  cases d'
  · rw [archDerivAt_H_eq hw x, archDerivAt_smul, archDerivAt_add hLs hRs]
    exact (hL.add hR).smul _
  · rw [archDerivAt_E_eq hw m x hxs hxm, archDerivAt_add ((hRs.sub hLs).smul _) (hxs.smul _),
      archDerivAt_smul, archDerivAt_smul, archDerivAt_sub' hRs hLs]
    exact ((hR.sub hL).smul _).add (h0.smul _)
  · rw [archDerivAt_Fm_eq hw m x hxs hxm]
    have h1 : ((2 * Complex.I)⁻¹ / 2 : ℂ) • (Ra hw x - Lo hw x) - (Complex.I * m / 2 : ℂ) • x =
        ((2 * Complex.I)⁻¹ / 2 : ℂ) • (Ra hw x - Lo hw x) + (-(Complex.I * m / 2) : ℂ) • x := by
      funext g; simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [h1, archDerivAt_add ((hRs.sub hLs).smul _) (hxs.smul _), archDerivAt_smul, archDerivAt_smul,
      archDerivAt_sub' hRs hLs]
    exact ((hR.sub hL).smul _).add (h0.smul _)

section Main

abbrev pins (K : Type) [Field K] [NumberField K] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) :=
  productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
    (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)

theorem main
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (pins K c u d₁ d₂ T).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K (pins K c u d₁ d₂ T) ξ V)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (hreal : ∀ v : InfinitePlace K, v.IsReal)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (χ : ∀ v : InfinitePlace K, rowIsometrySubgroup₀ v.Completion →* ℂˣ)
    (w : InfinitePlace K) (hw : w.IsReal) (n : ℤ) (hχ : χ w = archWeightCharAt hw n)
    (y : AdelicGL2 (𝓞 K) K → ℂ)
    (hy : y ∈ V ⊓ levelInvariantSubmodule K (pins K c u d₁ d₂ T) N ⊓ archCutSubmodule K (ArchTypeFamily.ofChar K χ))
    (e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ < e₂) :
    ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
      NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
      ‖y g‖ ≤ B ∧ (∀ d : ArchDir, ‖archDerivAt hw d y g‖ ≤ B) ∧
        (∀ d d' : ArchDir, ‖archDerivAt hw d (archDerivAt hw d' y) g‖ ≤ B) := by
  classical

  let χ' : ℤ → ∀ v : InfinitePlace K, rowIsometrySubgroup₀ v.Completion →* ℂˣ :=
    fun m => Function.update χ w (archWeightCharAt hw m)
  have hχ' : ∀ (m : ℤ) (v : InfinitePlace K), v ≠ w → χ' m v = χ v :=
    fun m v hv => Function.update_of_ne hv _ _
  have hχ'w : ∀ m : ℤ, χ' m w = archWeightCharAt hw m := fun m => Function.update_self _ _ _
  have hχ'χ' : ∀ (m₀ m : ℤ) (v : InfinitePlace K), v ≠ w → χ' m v = χ' m₀ v :=
    fun m₀ m v hv => by rw [hχ' m v hv, hχ' m₀ v hv]

  let cut : AutomorphicForm.ArchTypeFamily K → Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ) :=
    fun tys => V ⊓ levelInvariantSubmodule K (pins K c u d₁ d₂ T) N ⊓ archCutSubmodule K tys

  have bdd_of_cut : ∀ (tys : AutomorphicForm.ArchTypeFamily K) (z : AdelicGL2 (𝓞 K) K → ℂ), z ∈ cut tys →
      Bdd e₁ e₂ z := fun tys z hz =>
    Bdd.of_rpow he₁ (AutomorphicForm.CuspidalConstituent.exists_norm_le_mul_ideleNorm_det_rpow_of_isCuspConstituent
      K c u d₁ d₂ T hc hd₁ hd hcov ξ N hN tys V hV z hz w₀ hξ)
  have smooth_of_cut : ∀ (tys : AutomorphicForm.ArchTypeFamily K) (z : AdelicGL2 (𝓞 K) K → ℂ), z ∈ cut tys →
      IsArchSmoothAt hw z := fun tys z hz =>
    (AutomorphicForm.CuspidalConstituent.isArchSmoothAt_and_continuous_foldr_archDerivAt_of_mem_cut
      K c u d₁ d₂ T hc hd₁ hd hcov ξ V hV N hN tys z hz w hw []).1
  have weight_of_cut : ∀ (χ₁ : ∀ v : InfinitePlace K, rowIsometrySubgroup₀ v.Completion →* ℂˣ) (m : ℤ)
      (hm : χ₁ w = archWeightCharAt hw m) (z : AdelicGL2 (𝓞 K) K → ℂ), z ∈ cut (ArchTypeFamily.ofChar K χ₁) →
      HasArchCharacterAt₀ K w (archWeightCharAt hw m) z := fun χ₁ m hm z hz => by
    have h := (AutomorphicForm.mem_archCutSubmodule_ofChar_iff K χ₁ z).mp (Submodule.mem_inf.mp hz).2 w
    rwa [hm] at h

  have step : ∀ (m : ℤ) (z : AdelicGL2 (𝓞 K) K → ℂ), z ∈ cut (ArchTypeFamily.ofChar K (χ' m)) →
      Lo hw z ∈ cut (ArchTypeFamily.ofChar K (χ' (m - 2))) ∧
      Ra hw z ∈ cut (ArchTypeFamily.ofChar K (χ' (m + 2))) := by
    intro m z hz
    have hG := AutomorphicForm.CuspidalConstituent.iterate_lower_mem_cut_ofChar_and_iterate_raise_mem_cut_ofChar
      K c u d₁ d₂ T hc hd₁ hd hcov ξ V hV hreal N hN (χ' m) w hw m (hχ'w m) χ' (hχ'χ' m) hχ'w z hz
    refine ⟨?_, ?_⟩
    · have h := hG.1 1
      simp only [Function.iterate_one, Nat.cast_one, mul_one] at h
      exact h
    · have h := hG.2 1
      simp only [Function.iterate_one, Nat.cast_one, mul_one] at h
      exact h

  have hχ'n : χ' n = χ := by
    funext v
    by_cases hv : v = w
    · subst hv; rw [hχ'w, hχ]
    · exact hχ' n v hv
  have hy' : y ∈ cut (ArchTypeFamily.ofChar K (χ' n)) := by rw [hχ'n]; exact hy

  obtain ⟨hLy, hRy⟩ := step n y hy'
  obtain ⟨hLLy, hRLy⟩ := step (n - 2) (Lo hw y) hLy
  obtain ⟨hLRy, hRRy⟩ := step (n + 2) (Ra hw y) hRy

  have sy := smooth_of_cut _ y hy'
  have sLy := smooth_of_cut _ _ hLy
  have sRy := smooth_of_cut _ _ hRy
  have wy := weight_of_cut (χ' n) n (hχ'w n) y hy'
  have wLy := weight_of_cut (χ' (n - 2)) (n - 2) (hχ'w (n - 2)) _ hLy
  have wRy := weight_of_cut (χ' (n + 2)) (n + 2) (hχ'w (n + 2)) _ hRy

  have by0 := bdd_of_cut _ y hy'
  have bLy := bdd_of_cut _ _ hLy
  have bRy := bdd_of_cut _ _ hRy
  have bLLy := bdd_of_cut _ _ hLLy
  have bRLy := bdd_of_cut _ _ hRLy
  have bLRy := bdd_of_cut _ _ hLRy
  have bRRy := bdd_of_cut _ _ hRRy

  have b1 : ∀ d, Bdd e₁ e₂ (archDerivAt hw d y) := bdd_archDerivAt hw n sy wy by0 bLy bRy
  have b1L : ∀ d, Bdd e₁ e₂ (archDerivAt hw d (Lo hw y)) := bdd_archDerivAt hw (n - 2) sLy wLy bLy bLLy bRLy
  have b1R : ∀ d, Bdd e₁ e₂ (archDerivAt hw d (Ra hw y)) := bdd_archDerivAt hw (n + 2) sRy wRy bRy bLRy bRRy

  have b2 : ∀ d d', Bdd e₁ e₂ (archDerivAt hw d (archDerivAt hw d' y)) := fun d d' =>
    bdd_archDerivAt₂ hw n sy wy sLy sRy d d' (b1 d) (b1L d) (b1R d)

  obtain ⟨C₀, hC₀, h₀⟩ := by0
  choose C₁ hC₁ h₁ using b1
  choose C₂ hC₂ h₂ using b2
  refine ⟨C₀ + (C₁ .H + C₁ .E + C₁ .Fm) +
    (C₂ .H .H + C₂ .H .E + C₂ .H .Fm + C₂ .E .H + C₂ .E .E + C₂ .E .Fm + C₂ .Fm .H + C₂ .Fm .E + C₂ .Fm .Fm),
    fun g hg => ⟨?_, fun d => ?_, fun d d' => ?_⟩⟩
  · have := h₀ g hg
    have := hC₁ .H; have := hC₁ .E; have := hC₁ .Fm
    have := hC₂ .H .H; have := hC₂ .H .E; have := hC₂ .H .Fm
    have := hC₂ .E .H; have := hC₂ .E .E; have := hC₂ .E .Fm
    have := hC₂ .Fm .H; have := hC₂ .Fm .E; have := hC₂ .Fm .Fm
    linarith
  · have := h₁ d g hg
    have := hC₁ .H; have := hC₁ .E; have := hC₁ .Fm
    have := hC₂ .H .H; have := hC₂ .H .E; have := hC₂ .H .Fm
    have := hC₂ .E .H; have := hC₂ .E .E; have := hC₂ .E .Fm
    have := hC₂ .Fm .H; have := hC₂ .Fm .E; have := hC₂ .Fm .Fm
    cases d <;> linarith
  · have := h₂ d d' g hg
    have := hC₁ .H; have := hC₁ .E; have := hC₁ .Fm
    have := hC₂ .H .H; have := hC₂ .H .E; have := hC₂ .H .Fm
    have := hC₂ .E .H; have := hC₂ .E .E; have := hC₂ .E .Fm
    have := hC₂ .Fm .H; have := hC₂ .Fm .E; have := hC₂ .Fm .Fm
    cases d <;> cases d' <;> linarith

end Main

end BddSlab25

end

theorem solution
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ V)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (hreal : ∀ v : InfinitePlace K, v.IsReal)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (χ : ∀ v : InfinitePlace K, rowIsometrySubgroup₀ v.Completion →* ℂˣ)
    (w : InfinitePlace K) (hw : w.IsReal) (n : ℤ) (hχ : χ w = archWeightCharAt hw n)
    (y : AdelicGL2 (𝓞 K) K → ℂ)
    (hy : y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K (ArchTypeFamily.ofChar K χ))
    (e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ < e₂) :
    ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
      NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
      ‖y g‖ ≤ B ∧ (∀ d : ArchDir, ‖archDerivAt hw d y g‖ ≤ B) ∧
        (∀ d d' : ArchDir, ‖archDerivAt hw d (archDerivAt hw d' y) g‖ ≤ B) :=
  BddSlab25.main K c u d₁ d₂ T hc hd₁ hd hcov ξ V hV w₀ hξ hreal N hN χ w hw n hχ y hy e₁ e₂ he₁ he

end S_AutomorphicForm_CuspidalConstituent_exists_forall_norm_archDerivAt_le_of_mem_cut_ofChar_of_forall_isReal
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_exists_forall_norm_archDerivAt_le_of_mem_cut_ofChar_of_forall_isReal (solution)
