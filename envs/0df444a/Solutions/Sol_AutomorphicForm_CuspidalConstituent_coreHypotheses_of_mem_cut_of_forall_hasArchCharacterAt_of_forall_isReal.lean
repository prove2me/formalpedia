-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.coreHypotheses_of_mem_cut_of_forall_hasArchCharacterAt_of_forall_isReal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/d76e40a8-5c79-5e1d-8290-00135185b544

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_isArchSmoothAt_and_continuous_foldr_archDerivAt_of_mem_cut
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_iterate_lower_mem_cut_ofChar_and_iterate_raise_mem_cut_ofChar
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_norm_whittakerCoefficient_le_mul_ideleNorm_det_rpow_of_isCuspConstituent
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_forall_isArchSmoothAt_and_archCasimirAt_eq_smul_of_isCuspConstituent
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_casimir_real_and_pos_or_discrete_or_trivial_of_isCuspConstituent_of_forall_isReal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_coreHypotheses_of_mem_cut_of_forall_hasArchCharacterAt_of_forall_isReal
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_CuspidalConstituent_coreHypotheses_of_mem_cut_of_forall_hasArchCharacterAt_of_forall_isReal.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain"
open AutomorphicForm.CuspidalConstituent

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "productionPinsOf AdelicGL2 globalPoints centralScalar finiteAdelicGL2Subgroup lsXiMemberAt_iff ArchTypeFamily ArchTypeFamily.ofChar archCutSubmodule mem_archCutSubmodule_ofChar_iff rowIsometrySubgroup₀ HasArchCharacterAt₀ archRealGLAt IsArchSmoothAt ArchDir archDerivAt archCasimirAt archCasimirAt_const archWeightCharAt whittakerCoefficient CuspidalConstituent.isArchSmoothAt_and_continuous_foldr_archDerivAt_of_mem_cut CuspidalConstituent.iterate_lower_mem_cut_ofChar_and_iterate_raise_mem_cut_ofChar CuspidalConstituent.exists_norm_whittakerCoefficient_le_mul_ideleNorm_det_rpow_of_isCuspConstituent CuspidalConstituent.exists_forall_isArchSmoothAt_and_archCasimirAt_eq_smul_of_isCuspConstituent CuspidalConstituent.casimir_real_and_pos_or_discrete_or_trivial_of_isCuspConstituent_of_forall_isReal"
namespace CoreSupply25Cut
p2m_open "AutomorphicForm"

variable (K : Type) [Field K] [NumberField K]

theorem rightTranslate_one (φ : AdelicGL2 (𝓞 K) K → ℂ) : rightTranslate K 1 φ = φ := by
  funext x; simp [rightTranslate]

theorem isLsXi_of_mem_cuspKFiniteSubmodule
    (D : Set (AdelicGL2 (𝓞 K) K))
    (ξ : (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z →* ℂˣ)
    {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : φ ∈ cuspKFiniteSubmodule K (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ) :
    (∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), φ (globalPoints (𝓞 K) K γ * g) = φ g) ∧
    (∀ (z : (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z) (g : AdelicGL2 (𝓞 K) K),
        φ (centralScalar (𝓞 K) K (z : (AdeleRing (𝓞 K) K)ˣ) * g) = ((ξ z : ℂˣ) : ℂ) * φ g) ∧
    Continuous φ := by
  refine Submodule.span_induction (p := fun φ _ =>
    (∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), φ (globalPoints (𝓞 K) K γ * g) = φ g) ∧
    (∀ (z : (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z) (g : AdelicGL2 (𝓞 K) K),
        φ (centralScalar (𝓞 K) K (z : (AdeleRing (𝓞 K) K)ˣ) * g) = ((ξ z : ℂˣ) : ℂ) * φ g) ∧
    Continuous φ) ?_ ?_ ?_ ?_ hφ
  · rintro φ ⟨hsat, hcont, -⟩
    have h1 := hsat 1
    rw [rightTranslate_one] at h1
    letI : MeasurableSpace (AdelicGL2 (𝓞 K) K) := NumberField.AdelicHaar.glBorel (Fin 2) (𝓞 K) K
    have hls := ((lsXiMemberAt_iff (𝓞 K) K _ _ ξ _ φ).mp h1.1.1).1
    exact ⟨hls.left_invariant, hls.central_transform, hcont⟩
  · exact ⟨fun _ _ => rfl, fun _ _ => by simp, continuous_zero⟩
  · rintro u w - - ⟨hu1, hu2, hu3⟩ ⟨hw1, hw2, hw3⟩
    refine ⟨fun γ g => by simp only [Pi.add_apply, hu1, hw1], fun z g => ?_, hu3.add hw3⟩
    simp only [Pi.add_apply, hu2, hw2]; ring
  · rintro r u - ⟨hu1, hu2, hu3⟩
    refine ⟨fun γ g => by simp only [Pi.smul_apply, hu1], fun z g => ?_, hu3.const_smul r⟩
    simp only [Pi.smul_apply, smul_eq_mul, hu2]; ring

end AutomorphicForm.CoreSupply25Cut

open AutomorphicForm.CoreSupply25Cut

namespace AutomorphicForm
p2m_export "AutomorphicForm" "productionPinsOf AdelicGL2 globalPoints centralScalar finiteAdelicGL2Subgroup lsXiMemberAt_iff ArchTypeFamily ArchTypeFamily.ofChar archCutSubmodule mem_archCutSubmodule_ofChar_iff rowIsometrySubgroup₀ HasArchCharacterAt₀ archRealGLAt IsArchSmoothAt ArchDir archDerivAt archCasimirAt archCasimirAt_const archWeightCharAt whittakerCoefficient CuspidalConstituent.isArchSmoothAt_and_continuous_foldr_archDerivAt_of_mem_cut CuspidalConstituent.iterate_lower_mem_cut_ofChar_and_iterate_raise_mem_cut_ofChar CuspidalConstituent.exists_norm_whittakerCoefficient_le_mul_ideleNorm_det_rpow_of_isCuspConstituent CuspidalConstituent.exists_forall_isArchSmoothAt_and_archCasimirAt_eq_smul_of_isCuspConstituent CuspidalConstituent.casimir_real_and_pos_or_discrete_or_trivial_of_isCuspConstituent_of_forall_isReal"
namespace CoreSupply25
p2m_open "AutomorphicForm"

theorem main
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
    (hreal : ∀ v : InfinitePlace K, v.IsReal)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily K)
    (y : AdelicGL2 (𝓞 K) K → ℂ)
    (hy : y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (nw : ∀ v : InfinitePlace K, v.IsReal → ℤ)
    (hyn : ∀ (v : InfinitePlace K) (hv : v.IsReal), HasArchCharacterAt₀ K v (archWeightCharAt hv (nw v hv)) y) :
    Continuous y ∧
    (∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), y (globalPoints (𝓞 K) K γ * g) = y g) ∧
    (∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      y (centralScalar (𝓞 K) K z * g) = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * y g) ∧
    (∀ (v : InfinitePlace K) (hv : v.IsReal) (l : List ArchDir),
      IsArchSmoothAt hv (l.foldr (archDerivAt hv) y) ∧ Continuous (l.foldr (archDerivAt hv) y)) ∧
    (∃ C₀ : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
      ‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
              g‖ ≤
        C₀ * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w₀ / 2)) ∧
    ∃ lam : ∀ v : InfinitePlace K, v.IsReal → ℝ,
      (∀ (v : InfinitePlace K) (hv : v.IsReal), archCasimirAt hv y = ((lam v hv : ℝ) : ℂ) • y) ∧
      ∀ (v : InfinitePlace K) (hv : v.IsReal),
        0 < lam v hv ∨
        (∃ (ε : ℝ) (k₀ M : ℕ), (ε = 1 ∨ ε = -1) ∧ 2 ≤ k₀ ∧ lam v hv = ((k₀ : ℝ) / 2) * (1 - (k₀ : ℝ) / 2) ∧
          ((nw v hv : ℤ) : ℝ) = ε * (k₀ + 2 * M) ∧ (fun z : AdelicGL2 (𝓞 K) K → ℂ =>
          archDerivAt hv .H z - ((ε : ℂ) * Complex.I) • (archDerivAt hv .E z + archDerivAt hv .Fm z))^[M + 1] y = 0 ∧
          ∃ Mgr : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
            ‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) ((fun z : AdelicGL2 (𝓞 K) K → ℂ =>
          archDerivAt hv .H z - ((ε : ℂ) * Complex.I) • (archDerivAt hv .E z + archDerivAt hv .Fm z))^[M] y) 1
              g‖ ≤
              Mgr * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w₀ / 2)) ∨
        (lam v hv = 0 ∧ ∀ (g : AdelicGL2 (𝓞 K) K) (h : GL (Fin 2) ℝ),
          Matrix.GeneralLinearGroup.det h = 1 → y (g * archRealGLAt hv h) = y g)  := by
  classical

  have hyV : y ∈ V := hy.1.1
  obtain ⟨hleft, hcent, hcontY⟩ := isLsXi_of_mem_cuspKFiniteSubmodule K _ ξ (hV.1.le hyV)
  refine ⟨hcontY, hleft, fun z g => hcent ⟨z, Subgroup.mem_top z⟩ g, fun v hv l =>
    AutomorphicForm.CuspidalConstituent.isArchSmoothAt_and_continuous_foldr_archDerivAt_of_mem_cut
      K c u d₁ d₂ T hc hd₁ hd hcov ξ V hV N hN tys y hy v hv l,
    AutomorphicForm.CuspidalConstituent.exists_norm_whittakerCoefficient_le_mul_ideleNorm_det_rpow_of_isCuspConstituent
      K c u d₁ d₂ T hc hd₁ hd hcov ξ N hN tys V hV y hy w₀ hξ, ?_⟩

  by_cases hy0 : y = 0
  · subst hy0
    refine ⟨fun _ _ => 1, fun v hv => ?_, fun v hv => Or.inl one_pos⟩
    have h0 : archCasimirAt hv (0 : AdelicGL2 (𝓞 K) K → ℂ) = 0 := archCasimirAt_const hv 0
    rw [h0, smul_zero]

  have hX : V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
      (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
      (adelicBox K)) N ⊓ archCutSubmodule K tys ≠ ⊥ := by
    intro h; apply hy0; have h' := hy; rw [h] at h'; exact (Submodule.mem_bot ℂ).1 h'
  have hCAS := fun (v : InfinitePlace K) (hv : v.IsReal) =>
    AutomorphicForm.CuspidalConstituent.exists_forall_isArchSmoothAt_and_archCasimirAt_eq_smul_of_isCuspConstituent
      K c u d₁ d₂ T hc hd₁ hd hcov ξ V hV N hN tys hX v hv
  choose lamC hlamC using hCAS
  have hlam' : ∀ (v : InfinitePlace K) (hv : v.IsReal), ∀ x ∈ V, IsArchSmoothAt hv x ∧ archCasimirAt hv x = lamC v hv • x :=
    fun v hv x hx => ⟨(hlamC v hv x hx).1, (hlamC v hv x hx).2.2.2⟩
  have hUNIT := fun (v : InfinitePlace K) (hv : v.IsReal) =>
    AutomorphicForm.CuspidalConstituent.casimir_real_and_pos_or_discrete_or_trivial_of_isCuspConstituent_of_forall_isReal
      K c u d₁ d₂ T hc hd₁ hd hcov ξ V hV w₀ hξ N hN tys hX hreal v hv (lamC v hv) (hlam' v hv)
  have hreC : ∀ (v : InfinitePlace K) (hv : v.IsReal), lamC v hv = (((lamC v hv).re : ℝ) : ℂ) :=
    fun v hv => Complex.ext (by simp) (by simp [(hUNIT v hv).1])
  refine ⟨fun v hv => (lamC v hv).re, fun v hv => ?_, fun v hv => ?_⟩
  · rw [← hreC]; exact (hlamC v hv y hyV).2.2.2

  rcases (hUNIT v hv).2 with hA | ⟨k₀, hk₀, hlamB, hwt⟩ | ⟨hlam0, hinv⟩
  · exact Or.inl hA
  ·
    right; left
    set n : ℤ := nw v hv with hn_def
    obtain ⟨hk₀n, hpar⟩ := hwt n N tys y hN hy (fun v' hv' => ⟨nw v' hv', hyn v' hv'⟩) (hyn v hv) hy0
    obtain ⟨M, hM⟩ : ∃ mm : ℕ, (|n| : ℤ) = k₀ + 2 * (mm : ℤ) := by
      have hev : (2 : ℤ) ∣ (|n| - k₀) := by
        have h2 : (2 : ℤ) ∣ (n - k₀) := Int.dvd_of_emod_eq_zero hpar
        rcases abs_choice n with h | h
        · rwa [h]
        · rw [h]; have : -n - (k₀ : ℤ) = -(n - k₀) - 2 * k₀ := by ring
          rw [this]; exact dvd_sub (dvd_neg.2 h2) (dvd_mul_right 2 _)
      obtain ⟨q, hq⟩ := hev
      refine ⟨q.toNat, ?_⟩
      have hq0 : 0 ≤ q := by omega
      rw [Int.toNat_of_nonneg hq0]; omega
    have hn0 : n ≠ 0 := by intro h; rw [h] at hk₀n; simp at hk₀n; omega
    have hlamR : (lamC v hv).re = ((k₀ : ℝ) / 2) * (1 - (k₀ : ℝ) / 2) := by
      have : lamC v hv = ((((k₀ : ℝ) / 2) * (1 - (k₀ : ℝ) / 2) : ℝ) : ℂ) := by rw [hlamB]; push_cast; ring
      rw [this, Complex.ofReal_re]

    let χ : ∀ v' : InfinitePlace K, rowIsometrySubgroup₀ v'.Completion →* ℂˣ :=
      fun v' => archWeightCharAt (hreal v') (nw v' (hreal v'))
    have hyχ : y ∈ archCutSubmodule K (ArchTypeFamily.ofChar K χ) :=
      (mem_archCutSubmodule_ofChar_iff K χ y).2 fun v' => hyn v' (hreal v')
    have hycut : y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K (ArchTypeFamily.ofChar K χ) := ⟨⟨hyV, hy.1.2⟩, hyχ⟩
    have hχw : χ v = archWeightCharAt hv n := rfl
    let χ' : ℤ → ∀ v' : InfinitePlace K, rowIsometrySubgroup₀ v'.Completion →* ℂˣ :=
      fun m v' => archWeightCharAt (hreal v') (if v' = v then m else nw v' (hreal v'))
    have hχ' : ∀ (m : ℤ) (v' : InfinitePlace K), v' ≠ v → χ' m v' = χ v' := by
      intro m v' hv'; simp only [χ', χ, if_neg hv']
    have hχ'w : ∀ m : ℤ, χ' m v = archWeightCharAt hv m := by
      intro m
      show archWeightCharAt (hreal v) (if v = v then m else nw v (hreal v)) = archWeightCharAt hv m
      rw [if_pos rfl]
    obtain ⟨hGl, hGr⟩ :=
      AutomorphicForm.CuspidalConstituent.iterate_lower_mem_cut_ofChar_and_iterate_raise_mem_cut_ofChar
        K c u d₁ d₂ T hc hd₁ hd hcov ξ V hV hreal N hN χ v hv n hχw χ' hχ' hχ'w y hycut

    have core : ∀ (ε : ℝ) (εz : ℤ), (εz : ℝ) = ε → (ε = 1 ∨ ε = -1) → (εz = 1 ∨ εz = -1) →
        n = εz * ((k₀ : ℤ) + 2 * (M : ℤ)) →
        (∀ j : ℕ, (fun z : AdelicGL2 (𝓞 K) K → ℂ =>
          archDerivAt hv .H z - ((ε : ℂ) * Complex.I) • (archDerivAt hv .E z + archDerivAt hv .Fm z))^[j] y ∈
          V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) N ⊓ archCutSubmodule K (ArchTypeFamily.ofChar K (χ' (n - 2 * εz * j)))) →
        ∃ (ε : ℝ) (k₀ M : ℕ), (ε = 1 ∨ ε = -1) ∧ 2 ≤ k₀ ∧ (lamC v hv).re = ((k₀ : ℝ) / 2) * (1 - (k₀ : ℝ) / 2) ∧
          ((nw v hv : ℤ) : ℝ) = ε * (k₀ + 2 * M) ∧ (fun z : AdelicGL2 (𝓞 K) K → ℂ =>
          archDerivAt hv .H z - ((ε : ℂ) * Complex.I) • (archDerivAt hv .E z + archDerivAt hv .Fm z))^[M + 1] y = 0 ∧
          ∃ Mgr : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
            ‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) ((fun z : AdelicGL2 (𝓞 K) K → ℂ =>
          archDerivAt hv .H z - ((ε : ℂ) * Complex.I) • (archDerivAt hv .E z + archDerivAt hv .Fm z))^[M] y) 1
              g‖ ≤
              Mgr * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w₀ / 2) := by
      intro ε εz hεε hε hεz hnz hmem
      have hnR : (n : ℝ) = ε * (k₀ + 2 * M) := by rw [← hεε]; exact_mod_cast hnz
      set Lop : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) := (fun z : AdelicGL2 (𝓞 K) K → ℂ =>
          archDerivAt hv .H z - ((ε : ℂ) * Complex.I) • (archDerivAt hv .E z + archDerivAt hv .Fm z)) with hLop
      have hlow : Lop^[M + 1] y = 0 := by
        by_contra hx
        have hxχ := (mem_archCutSubmodule_ofChar_iff K _ _).1 (hmem (M + 1)).2 v
        rw [hχ'w] at hxχ
        have h := (hwt _ N (ArchTypeFamily.ofChar K (χ' (n - 2 * εz * ((M + 1 : ℕ) : ℤ)))) _ hN (hmem (M + 1))
          (fun v' hv' => ⟨if v' = v then (n - 2 * εz * ((M + 1 : ℕ) : ℤ)) else nw v' (hreal v'),
            (mem_archCutSubmodule_ofChar_iff K _ _).1 (hmem (M + 1)).2 v'⟩) hxχ hx).1
        have hq : n - 2 * εz * ((M + 1 : ℕ) : ℤ) = εz * ((k₀ : ℤ) - 2) := by rw [hnz]; push_cast; ring
        rw [hq] at h
        have hk2 : (0 : ℤ) ≤ (k₀ : ℤ) - 2 := by omega
        rcases hεz with h1 | h1 <;> subst h1
        · rw [one_mul, abs_of_nonneg hk2] at h; omega
        · rw [neg_one_mul, abs_neg, abs_of_nonneg hk2] at h; omega
      obtain ⟨MW, hMW⟩ :=
        AutomorphicForm.CuspidalConstituent.exists_norm_whittakerCoefficient_le_mul_ideleNorm_det_rpow_of_isCuspConstituent
          K c u d₁ d₂ T hc hd₁ hd hcov ξ N hN (ArchTypeFamily.ofChar K (χ' (n - 2 * εz * M))) V hV (Lop^[M] y) (hmem M) w₀ hξ
      exact ⟨ε, k₀, M, hε, hk₀, hlamR, hnR, hlow, MW, hMW⟩

    rcases lt_or_gt_of_ne hn0 with hneg | hpos
    · have habs : |n| = -n := abs_of_neg hneg
      refine core (-1) (-1) (by norm_num) (Or.inr rfl) (Or.inr rfl) (by rw [habs] at hM; omega) ?_
      intro j
      have hfun : (fun x : AdelicGL2 (𝓞 K) K → ℂ =>
          archDerivAt hv .H x - ((((-1 : ℤ) : ℝ) : ℂ) * Complex.I) • (archDerivAt hv .E x + archDerivAt hv .Fm x)) =
          fun x => archDerivAt hv .H x + Complex.I • (archDerivAt hv .E x + archDerivAt hv .Fm x) := by
        funext x; push_cast; rw [neg_one_mul, neg_smul, sub_neg_eq_add]
      have hidx : n - 2 * (-1 : ℤ) * (j : ℤ) = n + 2 * (j : ℤ) := by ring
      rw [show ((-1 : ℝ) : ℂ) = (((-1 : ℤ) : ℝ) : ℂ) by push_cast; ring, hfun, hidx]
      exact hGr j
    · have habs : |n| = n := abs_of_pos hpos
      refine core 1 1 (by norm_num) (Or.inl rfl) (Or.inl rfl) (by rw [habs] at hM; omega) ?_
      intro j
      have hfun : (fun x : AdelicGL2 (𝓞 K) K → ℂ =>
          archDerivAt hv .H x - (((1 : ℝ) : ℂ) * Complex.I) • (archDerivAt hv .E x + archDerivAt hv .Fm x)) =
          fun x => archDerivAt hv .H x - Complex.I • (archDerivAt hv .E x + archDerivAt hv .Fm x) := by
        funext x; push_cast; rw [one_mul]
      have hidx : n - 2 * (1 : ℤ) * (j : ℤ) = n - 2 * (j : ℤ) := by ring
      rw [hfun, hidx]
      exact hGl j
  ·
    right; right
    refine ⟨?_, fun g h hh => hinv y hyV g h hh⟩
    show (lamC v hv).re = 0
    rw [hlam0]; simp

end AutomorphicForm.CoreSupply25

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
    (hreal : ∀ v : InfinitePlace K, v.IsReal)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily K)
    (y : AdelicGL2 (𝓞 K) K → ℂ)
    (hy : y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (nw : ∀ v : InfinitePlace K, v.IsReal → ℤ)
    (hyn : ∀ (v : InfinitePlace K) (hv : v.IsReal), HasArchCharacterAt₀ K v (archWeightCharAt hv (nw v hv)) y) :
    Continuous y ∧
    (∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), y (globalPoints (𝓞 K) K γ * g) = y g) ∧
    (∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      y (centralScalar (𝓞 K) K z * g) = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * y g) ∧
    (∀ (v : InfinitePlace K) (hv : v.IsReal) (l : List ArchDir),
      IsArchSmoothAt hv (l.foldr (archDerivAt hv) y) ∧ Continuous (l.foldr (archDerivAt hv) y)) ∧
    (∃ C₀ : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
      ‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
              g‖ ≤
        C₀ * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w₀ / 2)) ∧
    ∃ lam : ∀ v : InfinitePlace K, v.IsReal → ℝ,
      (∀ (v : InfinitePlace K) (hv : v.IsReal), archCasimirAt hv y = ((lam v hv : ℝ) : ℂ) • y) ∧
      ∀ (v : InfinitePlace K) (hv : v.IsReal),
        0 < lam v hv ∨
        (∃ (ε : ℝ) (k₀ M : ℕ), (ε = 1 ∨ ε = -1) ∧ 2 ≤ k₀ ∧ lam v hv = ((k₀ : ℝ) / 2) * (1 - (k₀ : ℝ) / 2) ∧
          ((nw v hv : ℤ) : ℝ) = ε * (k₀ + 2 * M) ∧ (fun z : AdelicGL2 (𝓞 K) K → ℂ =>
          archDerivAt hv .H z - ((ε : ℂ) * Complex.I) • (archDerivAt hv .E z + archDerivAt hv .Fm z))^[M + 1] y = 0 ∧
          ∃ Mgr : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
            ‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) ((fun z : AdelicGL2 (𝓞 K) K → ℂ =>
          archDerivAt hv .H z - ((ε : ℂ) * Complex.I) • (archDerivAt hv .E z + archDerivAt hv .Fm z))^[M] y) 1
              g‖ ≤
              Mgr * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w₀ / 2)) ∨
        (lam v hv = 0 ∧ ∀ (g : AdelicGL2 (𝓞 K) K) (h : GL (Fin 2) ℝ),
          Matrix.GeneralLinearGroup.det h = 1 → y (g * archRealGLAt hv h) = y g) :=
  AutomorphicForm.CoreSupply25.main K c u d₁ d₂ T hc hd₁ hd hcov ξ V hV hreal N hN tys y hy w₀ hξ nw hyn

end S_AutomorphicForm_CuspidalConstituent_coreHypotheses_of_mem_cut_of_forall_hasArchCharacterAt_of_forall_isReal
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_coreHypotheses_of_mem_cut_of_forall_hasArchCharacterAt_of_forall_isReal (solution)
