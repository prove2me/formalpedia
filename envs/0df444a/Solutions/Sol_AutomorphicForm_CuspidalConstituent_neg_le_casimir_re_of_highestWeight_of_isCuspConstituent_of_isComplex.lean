-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.neg_le_casimir_re_of_highestWeight_of_isCuspConstituent_of_isComplex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/932dbf13-3e48-5b50-aafd-787501392e4c

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_PeterssonIntegral
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_isArchSmoothAtComplex_and_continuous_foldr_archDerivAtComplex_of_mem_cut
import Theorems.Thm_AutomorphicForm_exists_measurableSet_isFundamentalDomain_subset_iUnion_centreCutSiegelSet_of_coversModCentre
import Theorems.Thm_AutomorphicForm_peterssonIntegral_self_ne_zero_of_isFundamentalDomain_of_continuous
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_setIntegral_archCasimirAtComplex_mul_conj_eq_and_archDelAt_adjoint_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_setIntegral_archDerivAtComplex_mul_conj_add_eq_zero_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_archDelAt_Fm_archDelAt_E_add_archDelBarAt_E_archDelBarAt_Fm_eq_of_archDerivAtComplex_iH_eq_smul
import Theorems.Thm_AutomorphicForm_apply_mul_archComplexGLAt_eq_of_forall_archDerivAtComplex_eq_zero
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplexAPI
import Theorems.Thm_AutomorphicForm_archKCasimirAtComplex_eq_smul_of_archDerivAtComplex_iH_eq_smul_of_compactRaise_eq_zero
import Theorems.Thm_AutomorphicForm_archCasimirAtComplex_add_archCasimirBarAtComplex_eq_of_isArchSmoothAtComplex
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_forall_norm_foldr_archDerivAtComplex_le_of_mem_cut
import Theorems.Thm_AutomorphicForm_archDerivAtComplex_iH_eq_zero_and_Fm_eq_E_and_iFm_eq_neg_iE_of_hasArchCharacterAtZero_one
import Theorems.Thm_AutomorphicForm_archDelAt_E_archDelAt_Fm_add_archDelBarAt_Fm_archDelBarAt_E_eq_of_archDerivAtComplex_iH_eq_smul
import Definitions.Def_P2M_Util
import Definitions.Def_P2M_Derive_AutomorphicForm_ArchDirComplex_DecidableEq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_neg_le_casimir_re_of_highestWeight_of_isCuspConstituent_of_isComplex
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply"
p2m_attr_erase "simp" "NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace U6C

variable (K : Type) [Field K] [NumberField K]

theorem rightTranslate_one (φ : AdelicGL2 (𝓞 K) K → ℂ) : rightTranslate K 1 φ = φ := by
  funext x; simp [rightTranslate]

theorem left_invariant_and_continuous_of_mem_cuspKFiniteSubmodule
    (D : Set (AdelicGL2 (𝓞 K) K))
    (ξ : (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z →* ℂˣ)
    {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : φ ∈ cuspKFiniteSubmodule K (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ) :
    (∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), φ (globalPoints (𝓞 K) K γ * g) = φ g) ∧ Continuous φ := by
  refine Submodule.span_induction (p := fun φ _ =>
    (∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), φ (globalPoints (𝓞 K) K γ * g) = φ g) ∧ Continuous φ)
    ?_ ?_ ?_ ?_ hφ
  · rintro φ ⟨hsat, hcont, -⟩
    have h1 := hsat 1
    rw [rightTranslate_one] at h1
    have hls := ((lsXiMemberAt_iff (𝓞 K) K _ _ ξ _ φ).mp h1.1.1).1
    exact ⟨hls.left_invariant, hcont⟩
  · exact ⟨fun _ _ => rfl, continuous_zero⟩
  · rintro u w - - ⟨hu1, hu3⟩ ⟨hw1, hw3⟩
    exact ⟨fun γ g => by simp only [Pi.add_apply, hu1, hw1], hu3.add hw3⟩
  · rintro r u - ⟨hu1, hu3⟩
    exact ⟨fun γ g => by simp only [Pi.smul_apply, hu1], hu3.const_smul r⟩

theorem setIntegral_mul_conj_self_eq (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (u : AdelicGL2 (𝓞 K) K → ℂ) :
    ∫ g in 𝓕, u g * conj (u g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = ((∫ g in 𝓕, ‖u g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  congr 1
  funext g
  rw [Complex.mul_conj']
  push_cast
  rfl

theorem setIntegral_norm_sq_nonneg (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (u : AdelicGL2 (𝓞 K) K → ℂ) :
    0 ≤ ∫ g in 𝓕, ‖u g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
  integral_nonneg fun g => sq_nonneg _

theorem setIntegral_mul_conj_smul (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (a : ℂ) (u v : AdelicGL2 (𝓞 K) K → ℂ) :
    ∫ g in 𝓕, u g * conj ((a • v) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = conj a * ∫ g in 𝓕, u g * conj (v g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  rw [← integral_const_mul]
  congr 1
  funext g
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

theorem setIntegral_smul_mul_conj (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (a : ℂ) (u v : AdelicGL2 (𝓞 K) K → ℂ) :
    ∫ g in 𝓕, (a • u) g * conj (v g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = a * ∫ g in 𝓕, u g * conj (v g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  rw [← integral_const_mul]
  congr 1
  funext g
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem setIntegral_zero_fun (𝓕 : Set (AdelicGL2 (𝓞 K) K)) :
    ∫ g in 𝓕, ‖(0 : AdelicGL2 (𝓞 K) K → ℂ) g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0 := by
  simp

theorem peterssonIntegral_zero_eq (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (u : AdelicGL2 (𝓞 K) K → ℂ) :
    peterssonIntegral K 0 𝓕 u u = ∫ g in 𝓕, u g * conj (u g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  unfold peterssonIntegral
  congr 1
  funext g
  rw [neg_zero, Real.rpow_zero]
  push_cast
  ring

theorem setIntegral_norm_sq_ne_zero
    (e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ < e₂)
    (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (h𝓕m : MeasurableSet 𝓕)
    (h𝓕s : 𝓕 ⊆ {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂})
    (h𝓕 : IsFundamentalDomain (globalPoints (𝓞 K) K).range 𝓕
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂}))
    (hfin : (adelicGLHaar (Fin 2) (𝓞 K) K) 𝓕 < ⊤)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hxc : Continuous x)
    (hxG : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x (globalPoints (𝓞 K) K γ * g) = x g)
    {B : ℝ} (hB : ∀ g : AdelicGL2 (𝓞 K) K,
      ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ → ‖x g‖ ≤ B)
    (hne : ∃ g : AdelicGL2 (𝓞 K) K, ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Ioo e₁ e₂ ∧ x g ≠ 0) :
    (∫ g in 𝓕, ‖x g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ≠ 0 := by
  have hint : IntegrableOn
      (fun g => ‖x g‖ ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-(0 : ℝ))) 𝓕 (adelicGLHaar (Fin 2) (𝓞 K) K) := by
    have hfun : (fun g : AdelicGL2 (𝓞 K) K =>
        ‖x g‖ ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-(0 : ℝ))) = fun g => ‖x g‖ ^ 2 := by
      funext g; rw [neg_zero, Real.rpow_zero, mul_one]
    rw [hfun]
    refine Measure.integrableOn_of_bounded (M := B ^ 2) hfin.ne
      ((continuous_norm.comp hxc).pow 2).aestronglyMeasurable ?_
    refine (ae_restrict_iff' h𝓕m).mpr (Filter.Eventually.of_forall fun g hg => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hB g (h𝓕s hg)) 2
  have h := AutomorphicForm.peterssonIntegral_self_ne_zero_of_isFundamentalDomain_of_continuous
    K 0 e₁ e₂ he₁ he 𝓕 h𝓕m h𝓕s h𝓕 x hxc hxG hne hint
  rw [peterssonIntegral_zero_eq, setIntegral_mul_conj_self_eq] at h
  exact fun h0 => h (by rw [h0]; simp)

scoped instance : Nonempty ArchDirComplex := ⟨.H⟩

scoped instance : Fintype ArchDirComplex :=
  ⟨{.H, .E, .Fm, .iH, .iE, .iFm}, by intro d; cases d <;> simp⟩

theorem cut_packageC (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
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
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily K)
    (w : InfinitePlace K) (hw : w.IsComplex)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hx : x ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys) :
    (∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x (globalPoints (𝓞 K) K γ * g) = x g) ∧
    Continuous x ∧
    (∀ l : List ArchDirComplex, IsArchSmoothAtComplex hw (l.foldr (archDerivAtComplex hw) x) ∧
      Continuous (l.foldr (archDerivAtComplex hw) x)) ∧
    (∀ e₁ e₂ : ℝ, 0 < e₁ → e₁ < e₂ → ∀ l : List ArchDirComplex, ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
      NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
      ‖(l.foldr (archDerivAtComplex hw) x) g‖ ≤ B) := by
  have hxV : x ∈ V := hx.1.1
  obtain ⟨hleft, hcont⟩ := left_invariant_and_continuous_of_mem_cuspKFiniteSubmodule K _ ξ (hV.1.le hxV)
  exact ⟨hleft, hcont, fun l =>
    AutomorphicForm.CuspidalConstituent.isArchSmoothAtComplex_and_continuous_foldr_archDerivAtComplex_of_mem_cut
      K c u d₁ d₂ T hc hd₁ hd hcov ξ V hV N hN tys x hx w hw l, fun e₁ e₂ he₁ he l =>
    AutomorphicForm.CuspidalConstituent.exists_forall_norm_foldr_archDerivAtComplex_le_of_mem_cut
      K c u d₁ d₂ T hc hd₁ hd hcov ξ V hV w₀ hξ N hN tys x hx w hw e₁ e₂ he₁ he l⟩

theorem u1_bounds {w : InfinitePlace K} (hw : w.IsComplex) (x : AdelicGL2 (𝓞 K) K → ℂ) {e₁ e₂ : ℝ}
    (h : ∀ l : List ArchDirComplex, ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
      NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
      ‖(l.foldr (archDerivAtComplex hw) x) g‖ ≤ B) :
    ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
      NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
      ‖x g‖ ≤ B ∧ (∀ d : ArchDirComplex, ‖archDerivAtComplex hw d x g‖ ≤ B) ∧
        (∀ d d' : ArchDirComplex, ‖archDerivAtComplex hw d (archDerivAtComplex hw d' x) g‖ ≤ B) := by
  classical
  choose B hB using h
  refine ⟨max (B []) (max (Finset.univ.sup' Finset.univ_nonempty fun d => B [d])
    (Finset.univ.sup' Finset.univ_nonempty fun p : ArchDirComplex × ArchDirComplex => B [p.1, p.2])), ?_⟩
  intro g hg
  refine ⟨(hB [] g hg).trans (le_max_left _ _), fun d => ?_, fun d d' => ?_⟩
  · have h1 : ‖archDerivAtComplex hw d x g‖ ≤ B [d] := hB [d] g hg
    have h2 : B [d] ≤ Finset.univ.sup' Finset.univ_nonempty fun d => B [d] :=
      Finset.le_sup' (fun d => B [d]) (Finset.mem_univ d)
    exact h1.trans (h2.trans ((le_max_left _ _).trans (le_max_right _ _)))
  · have h1 : ‖archDerivAtComplex hw d (archDerivAtComplex hw d' x) g‖ ≤ B [d, d'] := hB [d, d'] g hg
    have h2 : B [d, d'] ≤ Finset.univ.sup' Finset.univ_nonempty
        fun p : ArchDirComplex × ArchDirComplex => B [p.1, p.2] :=
      Finset.le_sup' (fun p : ArchDirComplex × ArchDirComplex => B [p.1, p.2]) (Finset.mem_univ (d, d'))
    exact h1.trans (h2.trans ((le_max_right _ _).trans (le_max_right _ _)))

theorem u1_bounds2 {w : InfinitePlace K} (hw : w.IsComplex) {x₁ x₂ : AdelicGL2 (𝓞 K) K → ℂ} {e₁ e₂ B₁ B₂ : ℝ}
    (h₁ : ∀ g : AdelicGL2 (𝓞 K) K, ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
      ‖x₁ g‖ ≤ B₁ ∧ (∀ d : ArchDirComplex, ‖archDerivAtComplex hw d x₁ g‖ ≤ B₁) ∧
        (∀ d d' : ArchDirComplex, ‖archDerivAtComplex hw d (archDerivAtComplex hw d' x₁) g‖ ≤ B₁))
    (h₂ : ∀ g : AdelicGL2 (𝓞 K) K, ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
      ‖x₂ g‖ ≤ B₂ ∧ (∀ d : ArchDirComplex, ‖archDerivAtComplex hw d x₂ g‖ ≤ B₂) ∧
        (∀ d d' : ArchDirComplex, ‖archDerivAtComplex hw d (archDerivAtComplex hw d' x₂) g‖ ≤ B₂)) :
    ∀ g : AdelicGL2 (𝓞 K) K, ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
      ‖x₁ g‖ ≤ max B₁ B₂ ∧ ‖x₂ g‖ ≤ max B₁ B₂ ∧
      (∀ d : ArchDirComplex, ‖archDerivAtComplex hw d x₁ g‖ ≤ max B₁ B₂ ∧ ‖archDerivAtComplex hw d x₂ g‖ ≤ max B₁ B₂) ∧
      (∀ d d' : ArchDirComplex, ‖archDerivAtComplex hw d (archDerivAtComplex hw d' x₁) g‖ ≤ max B₁ B₂ ∧
        ‖archDerivAtComplex hw d (archDerivAtComplex hw d' x₂) g‖ ≤ max B₁ B₂) := by
  intro g hg
  obtain ⟨a0, a1, a2⟩ := h₁ g hg
  obtain ⟨b0, b1, b2⟩ := h₂ g hg
  exact ⟨a0.trans (le_max_left _ _), b0.trans (le_max_right _ _),
    fun d => ⟨(a1 d).trans (le_max_left _ _), (b1 d).trans (le_max_right _ _)⟩,
    fun d d' => ⟨(a2 d d').trans (le_max_left _ _), (b2 d d').trans (le_max_right _ _)⟩⟩

theorem slab_around (g : AdelicGL2 (𝓞 K) K) :
    0 < ideleNorm K (Matrix.GeneralLinearGroup.det g) / 2 ∧
    ideleNorm K (Matrix.GeneralLinearGroup.det g) / 2 < 2 * ideleNorm K (Matrix.GeneralLinearGroup.det g) ∧
    ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈
      Set.Ioo (ideleNorm K (Matrix.GeneralLinearGroup.det g) / 2) (2 * ideleNorm K (Matrix.GeneralLinearGroup.det g)) := by
  have h := ideleNorm_pos (Matrix.GeneralLinearGroup.det g)
  exact ⟨by linarith, by linarith, by constructor <;> linarith⟩

theorem partA (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
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
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily K)
    (w : InfinitePlace K) (hw : w.IsComplex)
    (lam lam' : ℂ)
    (hlam : ∀ x ∈ V, IsArchSmoothAtComplex hw x ∧ (∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d x)) ∧
      (∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' x))) ∧
      archCasimirAtComplex hw x = lam • x ∧ archCasimirBarAtComplex hw x = lam' • x)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hx : x ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys)
    (hx0 : x ≠ 0) :
    lam' = conj lam := by
  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.mp hx0
  obtain ⟨he₁, he, hmem⟩ := slab_around K g₀
  obtain ⟨d₁', d₂', tset, 𝓕, -, h𝓕m, h𝓕s, h𝓕, -⟩ :=
    AutomorphicForm.exists_measurableSet_isFundamentalDomain_subset_iUnion_centreCutSiegelSet_of_coversModCentre
      K c u d₁ d₂ T hc hd₁ hd hcov _ _ he₁ he
  have hfin : (adelicGLHaar (Fin 2) (𝓞 K) K) 𝓕 < ⊤ := by
    have h := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
      K _ _ he₁ he 𝓕 h𝓕
    rwa [Set.inter_eq_left.mpr h𝓕s] at h
  obtain ⟨hxl, hxc, hxS, hxbdd⟩ := cut_packageC K c u d₁ d₂ T hc hd₁ hd hcov ξ V hV w₀ hξ N hN tys w hw x hx
  obtain ⟨B, hB⟩ := u1_bounds K hw x (hxbdd _ _ he₁ he)
  have hxs : IsArchSmoothAtComplex hw x := (hxS []).1
  have hxD : ∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d x) := fun d => (hxS [d]).2
  have hxDD : ∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' x)) :=
    fun d d' => (hxS [d, d']).2
  have hU1 := AutomorphicForm.setIntegral_archCasimirAtComplex_mul_conj_eq_and_archDelAt_adjoint_of_isFundamentalDomain
    K w hw _ _ he₁ he 𝓕 h𝓕m h𝓕s h𝓕 x x hxl hxl hxc hxc hxs hxs hxD hxD hxDD hxDD (max B B) (u1_bounds2 K hw hB hB)
  have hΩ : archCasimirAtComplex hw x = lam • x := (hlam x hx.1.1).2.2.2.1
  have hΩ' : archCasimirBarAtComplex hw x = lam' • x := (hlam x hx.1.1).2.2.2.2
  have hcas := hU1.2.2.1
  rw [hΩ, hΩ', setIntegral_smul_mul_conj, setIntegral_mul_conj_smul, setIntegral_mul_conj_self_eq] at hcas
  have hr0 : (∫ g in 𝓕, ‖x g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ≠ 0 :=
    setIntegral_norm_sq_ne_zero K _ _ he₁ he 𝓕 h𝓕m h𝓕s h𝓕 hfin x hxc hxl (fun g hg => (hB g hg).1) ⟨g₀, hmem, hg₀⟩
  have hr0' : (((∫ g in 𝓕, ‖x g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr0
  have := mul_right_cancel₀ hr0' hcas
  rw [this, Complex.conj_conj]

section PartB

variable {K}
variable {w : InfinitePlace K} (hw : w.IsComplex)

local notation "μK" => adelicGLHaar (Fin 2) (𝓞 K) K
local notation "Dc" => archDerivAtComplex hw

theorem apply_eq_zero_of_setIntegral_norm_sq_eq_zero
    (e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ < e₂)
    (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (h𝓕m : MeasurableSet 𝓕)
    (h𝓕s : 𝓕 ⊆ {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂})
    (h𝓕 : IsFundamentalDomain (globalPoints (𝓞 K) K).range 𝓕
      ((μK).restrict {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂}))
    (hfin : (μK) 𝓕 < ⊤)
    (y : AdelicGL2 (𝓞 K) K → ℂ) (hyc : Continuous y)
    (hyG : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), y (globalPoints (𝓞 K) K γ * g) = y g)
    {B : ℝ} (hB : ∀ g : AdelicGL2 (𝓞 K) K, ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ → ‖y g‖ ≤ B)
    (g₁ : AdelicGL2 (𝓞 K) K) (hg₁ : ideleNorm K (Matrix.GeneralLinearGroup.det g₁) ∈ Set.Ioo e₁ e₂)
    (h0 : (∫ g in 𝓕, ‖y g‖ ^ 2 ∂(μK)) = 0) : y g₁ = 0 := by
  by_contra hne
  exact setIntegral_norm_sq_ne_zero K e₁ e₂ he₁ he 𝓕 h𝓕m h𝓕s h𝓕 hfin y hyc hyG hB ⟨g₁, hg₁, hne⟩ h0

theorem integrableOn_of_bdd
    {e₁ e₂ : ℝ} (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (h𝓕m : MeasurableSet 𝓕)
    (h𝓕s : 𝓕 ⊆ {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂})
    (hfin : (μK) 𝓕 < ⊤)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) {C : ℝ}
    (hC : ∀ g : AdelicGL2 (𝓞 K) K, ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ → ‖f g‖ ≤ C) :
    IntegrableOn f 𝓕 (μK) := by
  refine Measure.integrableOn_of_bounded (M := C) hfin.ne hf.aestronglyMeasurable ?_
  exact (ae_restrict_iff' h𝓕m).mpr (Filter.Eventually.of_forall fun g hg => hC g (h𝓕s hg))

theorem setIntegral_archDerivAtComplex_mul_conj_eq_neg
    (X : ArchDirComplex) (e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ < e₂)
    (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (h𝓕m : MeasurableSet 𝓕)
    (h𝓕s : 𝓕 ⊆ {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂})
    (h𝓕 : IsFundamentalDomain (globalPoints (𝓞 K) K).range 𝓕
      ((μK).restrict {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂}))
    (hfin : (μK) 𝓕 < ⊤)
    (y x : AdelicGL2 (𝓞 K) K → ℂ)
    (hyG : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), y (globalPoints (𝓞 K) K γ * g) = y g)
    (hxG : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x (globalPoints (𝓞 K) K γ * g) = x g)
    (hyc : Continuous y) (hxc : Continuous x)
    (hys : IsArchSmoothAtComplex hw y) (hxs : IsArchSmoothAtComplex hw x)
    (hDy : Continuous (Dc X y)) (hDx : Continuous (Dc X x))
    (B : ℝ) (hB : ∀ g : AdelicGL2 (𝓞 K) K, ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
      ‖y g‖ ≤ B ∧ ‖x g‖ ≤ B ∧ ‖Dc X y g‖ ≤ B ∧ ‖Dc X x g‖ ≤ B) :
    ∫ g in 𝓕, Dc X y g * conj (x g) ∂(μK) = -∫ g in 𝓕, y g * conj (Dc X x g) ∂(μK) := by
  have h0 := AutomorphicForm.setIntegral_archDerivAtComplex_mul_conj_add_eq_zero_of_isFundamentalDomain
    K w hw X e₁ e₂ he₁ he 𝓕 h𝓕m h𝓕s h𝓕 y x hyG hxG hyc hxc hys hxs hDy hDx B hB
  have hi1 : IntegrableOn (fun g => Dc X y g * conj (x g)) 𝓕 (μK) := by
    refine integrableOn_of_bdd 𝓕 h𝓕m h𝓕s hfin _ (hDy.mul (Complex.continuous_conj.comp hxc)) (C := B * B) ?_
    intro g hg
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hB g hg).2.2.1 (hB g hg).2.1 (norm_nonneg _) ((norm_nonneg _).trans (hB g hg).2.2.1)
  have hi2 : IntegrableOn (fun g => y g * conj (Dc X x g)) 𝓕 (μK) := by
    refine integrableOn_of_bdd 𝓕 h𝓕m h𝓕s hfin _ (hyc.mul (Complex.continuous_conj.comp hDx)) (C := B * B) ?_
    intro g hg
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hB g hg).1 (hB g hg).2.2.2 (norm_nonneg _) ((norm_nonneg _).trans (hB g hg).1)
  rw [integral_add hi1 hi2] at h0
  linear_combination h0

theorem archDelBarAt_Fm_eq_archDelAt_E (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hK : archDerivAtComplex hw .iH φ = 0 ∧ archDerivAtComplex hw .Fm φ = archDerivAtComplex hw .E φ ∧
      archDerivAtComplex hw .iFm φ = -archDerivAtComplex hw .iE φ) :
    archDelBarAt hw .Fm φ = archDelAt hw .E φ := by
  unfold AutomorphicForm.archDelBarAt AutomorphicForm.archDelAt
  simp only [ArchDir.toComplex, ArchDir.toComplexI, hK.2.1, hK.2.2, smul_neg, sub_eq_add_neg]

theorem archDelBarAt_E_eq_archDelAt_Fm (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hK : archDerivAtComplex hw .iH φ = 0 ∧ archDerivAtComplex hw .Fm φ = archDerivAtComplex hw .E φ ∧
      archDerivAtComplex hw .iFm φ = -archDerivAtComplex hw .iE φ) :
    archDelBarAt hw .E φ = archDelAt hw .Fm φ := by
  unfold AutomorphicForm.archDelBarAt AutomorphicForm.archDelAt
  simp only [ArchDir.toComplex, ArchDir.toComplexI, hK.2.1, hK.2.2, smul_neg, sub_neg_eq_add]

end PartB

section PartB2

variable {K}
variable {w : InfinitePlace K} (hw : w.IsComplex)

local notation "μK" => adelicGLHaar (Fin 2) (𝓞 K) K
local notation "Dc" => archDerivAtComplex hw

theorem leftInv_archDerivAtComplex {y : AdelicGL2 (𝓞 K) K → ℂ}
    (hy : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), y (globalPoints (𝓞 K) K γ * g) = y g) (d : ArchDirComplex) :
    ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), Dc d y (globalPoints (𝓞 K) K γ * g) = Dc d y g := by
  intro γ g
  unfold AutomorphicForm.archDerivAtComplex
  simp only [mul_assoc, hy]

theorem archDerivAtComplex_lin {φ ψ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : IsArchSmoothAtComplex hw φ) (hψ : IsArchSmoothAtComplex hw ψ) (a b : ℂ) (d : ArchDirComplex) :
    Dc d (a • φ + b • ψ) = a • Dc d φ + b • Dc d ψ := by
  rw [archDerivAtComplex_add (hφ.smul a) (hψ.smul b), archDerivAtComplex_smul, archDerivAtComplex_smul]

theorem key_L2
    (a b : ArchDir) (e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ < e₂)
    (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (h𝓕m : MeasurableSet 𝓕)
    (h𝓕s : 𝓕 ⊆ {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂})
    (h𝓕 : IsFundamentalDomain (globalPoints (𝓞 K) K).range 𝓕
      ((μK).restrict {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂}))
    (hfin : (μK) 𝓕 < ⊤)
    (x u : AdelicGL2 (𝓞 K) K → ℂ)
    (hxG : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x (globalPoints (𝓞 K) K γ * g) = x g)
    (huG : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), u (globalPoints (𝓞 K) K γ * g) = u g)
    (hxc : Continuous x) (huc : Continuous u)
    (hxs : IsArchSmoothAtComplex hw x) (hus : IsArchSmoothAtComplex hw u)
    (hDx : ∀ d, Continuous (Dc d x)) (hDu : ∀ d, Continuous (Dc d u))
    (hDDx : Continuous (Dc .H (Dc .H x)))
    (B : ℝ) (hB : ∀ g : AdelicGL2 (𝓞 K) K, ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
      ‖x g‖ ≤ B ∧ ‖u g‖ ≤ B ∧ (∀ d, ‖Dc d x g‖ ≤ B) ∧ (∀ d, ‖Dc d u g‖ ≤ B) ∧ ‖Dc .H (Dc .H x) g‖ ≤ B)
    (hid : -(archDelAt hw a u + archDelBarAt hw b u) = (1 / 8 : ℂ) • Dc .H (Dc .H x))
    (hu4 : ∀ g, 4 * u g = Dc a.toComplex x g + Complex.I * Dc a.toComplexI x g
      + Dc b.toComplex x g - Complex.I * Dc b.toComplexI x g) :
    2 * (∫ g in 𝓕, ‖u g‖ ^ 2 ∂(μK)) + (1 / 8) * (∫ g in 𝓕, ‖Dc .H x g‖ ^ 2 ∂(μK)) = 0 := by

  have hU : ∀ d, ∫ g in 𝓕, Dc d u g * conj (x g) ∂(μK) = -∫ g in 𝓕, u g * conj (Dc d x g) ∂(μK) := fun d =>
    setIntegral_archDerivAtComplex_mul_conj_eq_neg hw d e₁ e₂ he₁ he 𝓕 h𝓕m h𝓕s h𝓕 hfin u x huG hxG huc hxc hus hxs
      (hDu d) (hDx d) B (fun g hg => ⟨(hB g hg).2.1, (hB g hg).1, (hB g hg).2.2.2.1 d, (hB g hg).2.2.1 d⟩)
  have hH : ∫ g in 𝓕, Dc .H (Dc .H x) g * conj (x g) ∂(μK) = -∫ g in 𝓕, Dc .H x g * conj (Dc .H x g) ∂(μK) :=
    setIntegral_archDerivAtComplex_mul_conj_eq_neg hw .H e₁ e₂ he₁ he 𝓕 h𝓕m h𝓕s h𝓕 hfin (Dc .H x) x
      (leftInv_archDerivAtComplex hw hxG .H) hxG (hDx .H) hxc (hxs.archDerivAtComplex .H) hxs hDDx (hDx .H) B
      (fun g hg => ⟨(hB g hg).2.2.1 .H, (hB g hg).1, (hB g hg).2.2.2.2, (hB g hg).2.2.1 .H⟩)

  have hI : ∀ d, IntegrableOn (fun g => Dc d u g * conj (x g)) 𝓕 (μK) := fun d => by
    refine integrableOn_of_bdd 𝓕 h𝓕m h𝓕s hfin _ ((hDu d).mul (Complex.continuous_conj.comp hxc)) (C := B * B) ?_
    intro g hg; rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul ((hB g hg).2.2.2.1 d) (hB g hg).1 (norm_nonneg _) ((norm_nonneg _).trans ((hB g hg).2.2.2.1 d))
  have hJ : ∀ d, IntegrableOn (fun g => u g * conj (Dc d x g)) 𝓕 (μK) := fun d => by
    refine integrableOn_of_bdd 𝓕 h𝓕m h𝓕s hfin _ (huc.mul (Complex.continuous_conj.comp (hDx d))) (C := B * B) ?_
    intro g hg; rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hB g hg).2.1 ((hB g hg).2.2.1 d) (norm_nonneg _) ((norm_nonneg _).trans (hB g hg).2.1)

  have hint := congrArg (fun F : AdelicGL2 (𝓞 K) K → ℂ => ∫ g in 𝓕, F g * conj (x g) ∂(μK)) hid

  have hR : (∫ g in 𝓕, ((1 / 8 : ℂ) • Dc .H (Dc .H x)) g * conj (x g) ∂(μK))
      = -(1 / 8 : ℂ) * (((∫ g in 𝓕, ‖Dc .H x g‖ ^ 2 ∂(μK)) : ℝ) : ℂ) := by
    rw [setIntegral_smul_mul_conj, hH, setIntegral_mul_conj_self_eq]; ring

  have hLpt : ∀ g, (-(archDelAt hw a u + archDelBarAt hw b u)) g * conj (x g)
      = -(1 / 2 : ℂ) * (Dc a.toComplex u g * conj (x g)) + (Complex.I / 2) * (Dc a.toComplexI u g * conj (x g))
        - (1 / 2 : ℂ) * (Dc b.toComplex u g * conj (x g)) - (Complex.I / 2) * (Dc b.toComplexI u g * conj (x g)) := by
    intro g
    simp only [AutomorphicForm.archDelAt, AutomorphicForm.archDelBarAt, Pi.neg_apply, Pi.add_apply, Pi.smul_apply,
      Pi.sub_apply, smul_eq_mul]
    ring
  have hL : (∫ g in 𝓕, (-(archDelAt hw a u + archDelBarAt hw b u)) g * conj (x g) ∂(μK))
      = (1 / 2 : ℂ) * (∫ g in 𝓕, u g * conj (Dc a.toComplex x g) ∂(μK))
        - (Complex.I / 2) * (∫ g in 𝓕, u g * conj (Dc a.toComplexI x g) ∂(μK))
        + (1 / 2 : ℂ) * (∫ g in 𝓕, u g * conj (Dc b.toComplex x g) ∂(μK))
        + (Complex.I / 2) * (∫ g in 𝓕, u g * conj (Dc b.toComplexI x g) ∂(μK)) := by
    have step : (∫ g in 𝓕, (-(archDelAt hw a u + archDelBarAt hw b u)) g * conj (x g) ∂(μK))
        = ∫ g in 𝓕, ((((fun g => -(1 / 2 : ℂ) * (Dc a.toComplex u g * conj (x g)))
            + (fun g => (Complex.I / 2) * (Dc a.toComplexI u g * conj (x g))))
            - (fun g => (1 / 2 : ℂ) * (Dc b.toComplex u g * conj (x g))))
            - (fun g => (Complex.I / 2) * (Dc b.toComplexI u g * conj (x g)))) g ∂(μK) := by
      congr 1; funext g; try simp only [Pi.add_apply, Pi.sub_apply]; exact hLpt g
    rw [step,
      integral_sub' ((((hI _).const_mul _).add ((hI _).const_mul _)).sub ((hI _).const_mul _)) ((hI _).const_mul _),
      integral_sub' (((hI _).const_mul _).add ((hI _).const_mul _)) ((hI _).const_mul _),
      integral_add' ((hI _).const_mul _) ((hI _).const_mul _)]
    rw [integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul, hU, hU, hU, hU]
    ring

  have hL' : (1 / 2 : ℂ) * (∫ g in 𝓕, u g * conj (Dc a.toComplex x g) ∂(μK))
        - (Complex.I / 2) * (∫ g in 𝓕, u g * conj (Dc a.toComplexI x g) ∂(μK))
        + (1 / 2 : ℂ) * (∫ g in 𝓕, u g * conj (Dc b.toComplex x g) ∂(μK))
        + (Complex.I / 2) * (∫ g in 𝓕, u g * conj (Dc b.toComplexI x g) ∂(μK))
      = 2 * (((∫ g in 𝓕, ‖u g‖ ^ 2 ∂(μK)) : ℝ) : ℂ) := by
    symm
    have step : (∫ g in 𝓕, 2 * (u g * conj (u g)) ∂(μK))
        = ∫ g in 𝓕, ((((fun g => (1 / 2 : ℂ) * (u g * conj (Dc a.toComplex x g)))
            - (fun g => (Complex.I / 2) * (u g * conj (Dc a.toComplexI x g))))
            + (fun g => (1 / 2 : ℂ) * (u g * conj (Dc b.toComplex x g))))
            + (fun g => (Complex.I / 2) * (u g * conj (Dc b.toComplexI x g)))) g ∂(μK) := by
      congr 1; funext g; try simp only [Pi.add_apply, Pi.sub_apply]
      have h4 := hu4 g
      have hc4 : conj (4 * u g) = conj (Dc a.toComplex x g) - Complex.I * conj (Dc a.toComplexI x g)
          + conj (Dc b.toComplex x g) + Complex.I * conj (Dc b.toComplexI x g) := by
        rw [h4]; simp only [map_add, map_sub, map_mul, Complex.conj_I]; ring
      have h2 : 2 * (u g * conj (u g)) = (1 / 2 : ℂ) * (u g * conj (4 * u g)) := by
        rw [map_mul]
        have : conj (4 : ℂ) = 4 := by apply Complex.ext <;> simp
        rw [this]; ring
      rw [h2, hc4]; ring
    rw [← setIntegral_mul_conj_self_eq, ← integral_const_mul, step,
      integral_add' ((((hJ _).const_mul _).sub ((hJ _).const_mul _)).add ((hJ _).const_mul _)) ((hJ _).const_mul _),
      integral_add' (((hJ _).const_mul _).sub ((hJ _).const_mul _)) ((hJ _).const_mul _),
      integral_sub' ((hJ _).const_mul _) ((hJ _).const_mul _)]
    rw [integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
  rw [hL, hL', hR] at hint

  have hre := congrArg Complex.re hint
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.neg_re,
    neg_mul] at hre
  norm_num at hre
  linarith

end PartB2

end U6C
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_neg_le_casimir_re_of_highestWeight_of_isCuspConstituent_of_isComplex.U6C"

namespace U6C

section U5

variable (K : Type) [Field K] [NumberField K]
variable {w : InfinitePlace K} (hw : w.IsComplex)

local notation "μK" => adelicGLHaar (Fin 2) (𝓞 K) K
local notation "Dc" => archDerivAtComplex hw

theorem pkg2 {x : AdelicGL2 (𝓞 K) K → ℂ}
    (hxl : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x (globalPoints (𝓞 K) K γ * g) = x g)
    (hxS : ∀ l : List ArchDirComplex, IsArchSmoothAtComplex hw (l.foldr (archDerivAtComplex hw) x) ∧
      Continuous (l.foldr (archDerivAtComplex hw) x))
    (a b : ArchDirComplex) (α β : ℂ) (hα : ‖α‖ ≤ 1) (hβ : ‖β‖ ≤ 1)
    (y : AdelicGL2 (𝓞 K) K → ℂ) (hy : y = α • Dc a x + β • Dc b x) :
    (∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), y (globalPoints (𝓞 K) K γ * g) = y g) ∧
    Continuous y ∧ IsArchSmoothAtComplex hw y ∧
    (∀ d, Dc d y = α • Dc d (Dc a x) + β • Dc d (Dc b x)) ∧ (∀ d, Continuous (Dc d y)) ∧
    (∀ (B : ℝ) (g : AdelicGL2 (𝓞 K) K),
      (∀ d, ‖Dc d x g‖ ≤ B) → (∀ d d', ‖Dc d (Dc d' x) g‖ ≤ B) → ‖y g‖ ≤ 2 * B ∧ ∀ d, ‖Dc d y g‖ ≤ 2 * B) := by
  have hDs : ∀ d, IsArchSmoothAtComplex hw (Dc d x) := fun d => (hxS [d]).1
  have hDc : ∀ d, Continuous (Dc d x) := fun d => (hxS [d]).2
  have hDDc : ∀ d d', Continuous (Dc d (Dc d' x)) := fun d d' => (hxS [d, d']).2
  have hD : ∀ d, Dc d y = α • Dc d (Dc a x) + β • Dc d (Dc b x) := fun d => by
    rw [hy]; exact archDerivAtComplex_lin hw (hDs a) (hDs b) α β d
  refine ⟨fun γ g => ?_, ?_, ?_, hD, fun d => ?_, fun B g h1 h2 => ⟨?_, fun d => ?_⟩⟩
  · rw [hy]; simp only [Pi.add_apply, Pi.smul_apply, leftInv_archDerivAtComplex hw hxl]
  · rw [hy]; exact ((hDc a).const_smul α).add ((hDc b).const_smul β)
  · rw [hy]; exact ((hDs a).smul α).add ((hDs b).smul β)
  · rw [hD d]; exact ((hDDc d a).const_smul α).add ((hDDc d b).const_smul β)
  · rw [hy]; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc ‖α * Dc a x g + β * Dc b x g‖ ≤ ‖α‖ * ‖Dc a x g‖ + ‖β‖ * ‖Dc b x g‖ := by
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_mul]
      _ ≤ 1 * B + 1 * B :=
          add_le_add (mul_le_mul hα (h1 _) (norm_nonneg _) (by norm_num))
            (mul_le_mul hβ (h1 _) (norm_nonneg _) (by norm_num))
      _ = 2 * B := by ring
  · rw [hD d]; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc ‖α * Dc d (Dc a x) g + β * Dc d (Dc b x) g‖
          ≤ ‖α‖ * ‖Dc d (Dc a x) g‖ + ‖β‖ * ‖Dc d (Dc b x) g‖ := by
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_mul]
      _ ≤ 1 * B + 1 * B :=
          add_le_add (mul_le_mul hα (h2 _ _) (norm_nonneg _) (by norm_num))
            (mul_le_mul hβ (h2 _ _) (norm_nonneg _) (by norm_num))
      _ = 2 * B := by ring

end U5
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_neg_le_casimir_re_of_highestWeight_of_isCuspConstituent_of_isComplex.U6C"

end U6C
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_neg_le_casimir_re_of_highestWeight_of_isCuspConstituent_of_isComplex.U6C"

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
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily K)
    (hX : V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys ≠ ⊥)
    (w : InfinitePlace K) (hw : w.IsComplex)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (lam lam' : ℂ)
    (hlam : ∀ x ∈ V, IsArchSmoothAtComplex hw x ∧ (∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d x)) ∧
      (∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' x))) ∧
      archCasimirAtComplex hw x = lam • x ∧ archCasimirBarAtComplex hw x = lam' • x)
    (n : ℕ) (N' : Ideal (𝓞 K)) (hN' : N' ≠ ⊥) (tys' : AutomorphicForm.ArchTypeFamily K)
    (F₀ : AdelicGL2 (𝓞 K) K → ℂ)
    (hF₀ : F₀ ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N' ⊓ archCutSubmodule K tys')
    (hF₀0 : F₀ ≠ 0)
    (hwt : archDerivAtComplex hw .iH F₀ = (Complex.I * (n : ℂ)) • F₀)
    (hJ : archDerivAtComplex hw .Fm F₀ - archDerivAtComplex hw .E F₀
      + Complex.I • (archDerivAtComplex hw .iE F₀ + archDerivAtComplex hw .iFm F₀) = 0) :
    -(((n:ℝ)^2 + 2*(n:ℝ))/16) ≤ lam.re := by

  have hconj : lam' = conj lam :=
    U6C.partA K c u d₁ d₂ T hc hd₁ hd hcov ξ V hV w₀ hξ N' hN' tys' w hw lam lam' hlam F₀ hF₀ hF₀0

  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.mp hF₀0
  obtain ⟨he₁, he, hmem⟩ := U6C.slab_around K g₀
  obtain ⟨d₁', d₂', tset, 𝓕, -, h𝓕m, h𝓕s, h𝓕, -⟩ :=
    AutomorphicForm.exists_measurableSet_isFundamentalDomain_subset_iUnion_centreCutSiegelSet_of_coversModCentre
      K c u d₁ d₂ T hc hd₁ hd hcov _ _ he₁ he
  have hfin : (adelicGLHaar (Fin 2) (𝓞 K) K) 𝓕 < ⊤ := by
    have h := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
      K _ _ he₁ he 𝓕 h𝓕
    rwa [Set.inter_eq_left.mpr h𝓕s] at h

  obtain ⟨hxl, hxc, hxS, hxbdd⟩ := U6C.cut_packageC K c u d₁ d₂ T hc hd₁ hd hcov ξ V hV w₀ hξ N' hN' tys' w hw F₀ hF₀
  have hxs : IsArchSmoothAtComplex hw F₀ := (hxS []).1
  have hDc : ∀ d, Continuous (archDerivAtComplex hw d F₀) := fun d => (hxS [d]).2
  have hDDc : ∀ d d', Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' F₀)) :=
    fun d d' => (hxS [d, d']).2
  obtain ⟨B, hB⟩ := U6C.u1_bounds K hw F₀ (hxbdd _ _ he₁ he)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans ((hB g₀ (Set.Ioo_subset_Icc_self hmem)).1)

  set yH : AdelicGL2 (𝓞 K) K → ℂ := archDerivAtComplex hw .H F₀ with hyH
  set yU : AdelicGL2 (𝓞 K) K → ℂ := archDerivAtComplex hw .E F₀ + archDerivAtComplex hw .Fm F₀ with hyU
  set yV : AdelicGL2 (𝓞 K) K → ℂ := archDerivAtComplex hw .iFm F₀ - archDerivAtComplex hw .iE F₀ with hyV
  have h1 : ‖(1 : ℂ)‖ ≤ 1 := by simp
  have hm1 : ‖(-1 : ℂ)‖ ≤ 1 := by simp
  have h0 : ‖(0 : ℂ)‖ ≤ 1 := by simp
  obtain ⟨hHl, hHc, hHs, -, hHD, hHb⟩ := U6C.pkg2 K hw hxl hxS .H .H 1 0 h1 h0 yH
    (by rw [hyH]; funext g; simp)
  obtain ⟨hUl, hUc, hUs, -, hUD, hUb⟩ := U6C.pkg2 K hw hxl hxS .E .Fm 1 1 h1 h1 yU
    (by rw [hyU]; funext g; simp)
  obtain ⟨hVl, hVc, hVs, -, hVD, hVb⟩ := U6C.pkg2 K hw hxl hxS .iFm .iE 1 (-1) h1 hm1 yV
    (by rw [hyV]; funext g; simp [sub_eq_add_neg])

  have hBx : ∀ g, ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc (ideleNorm K (Matrix.GeneralLinearGroup.det g₀) / 2) (2 * ideleNorm K (Matrix.GeneralLinearGroup.det g₀)) → ‖F₀ g‖ ≤ 2 * B :=
    fun g hg => (hB g hg).1.trans (by linarith)
  have hBDx : ∀ g, ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc (ideleNorm K (Matrix.GeneralLinearGroup.det g₀) / 2) (2 * ideleNorm K (Matrix.GeneralLinearGroup.det g₀)) → ∀ d,
      ‖archDerivAtComplex hw d F₀ g‖ ≤ 2 * B := fun g hg d => ((hB g hg).2.1 d).trans (by linarith)
  have skew := fun (y : AdelicGL2 (𝓞 K) K → ℂ) hyl hyc hys (hyD : ∀ d, Continuous (archDerivAtComplex hw d y))
      (hyb : ∀ g, ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc (ideleNorm K (Matrix.GeneralLinearGroup.det g₀) / 2) (2 * ideleNorm K (Matrix.GeneralLinearGroup.det g₀)) → ‖y g‖ ≤ 2 * B ∧ ∀ d, ‖archDerivAtComplex hw d y g‖ ≤ 2 * B)
      (X : ArchDirComplex) =>
    U6C.setIntegral_archDerivAtComplex_mul_conj_eq_neg hw X _ _ he₁ he 𝓕 h𝓕m h𝓕s h𝓕 hfin y F₀ hyl hxl hyc hxc hys hxs
      (hyD X) (hDc X) (2 * B) (fun g hg => ⟨(hyb g hg).1, hBx g hg, (hyb g hg).2 X, hBDx g hg X⟩)
  have sH := skew yH hHl hHc hHs hHD (fun g hg => hHb B g (hB g hg).2.1 (hB g hg).2.2) .H
  have sU1 := skew yU hUl hUc hUs hUD (fun g hg => hUb B g (hB g hg).2.1 (hB g hg).2.2) .E
  have sU2 := skew yU hUl hUc hUs hUD (fun g hg => hUb B g (hB g hg).2.1 (hB g hg).2.2) .Fm
  have sV1 := skew yV hVl hVc hVs hVD (fun g hg => hVb B g (hB g hg).2.1 (hB g hg).2.2) .iFm
  have sV2 := skew yV hVl hVc hVs hVD (fun g hg => hVb B g (hB g hg).2.1 (hB g hg).2.2) .iE

  have hΩ : archCasimirAtComplex hw F₀ = lam • F₀ := (hlam F₀ hF₀.1.1).2.2.2.1
  have hΩ' : archCasimirBarAtComplex hw F₀ = lam' • F₀ := (hlam F₀ hF₀.1.1).2.2.2.2
  have hKC := AutomorphicForm.archKCasimirAtComplex_eq_smul_of_archDerivAtComplex_iH_eq_smul_of_compactRaise_eq_zero
    K hw F₀ hxs n hwt hJ
  have hCS := AutomorphicForm.archCasimirAtComplex_add_archCasimirBarAtComplex_eq_of_isArchSmoothAtComplex K hw F₀ hxs
  rw [hΩ, hΩ', hKC] at hCS

  rw [show archDerivAtComplex hw .E F₀ + archDerivAtComplex hw .Fm F₀ = yU from rfl,
    show archDerivAtComplex hw .iFm F₀ - archDerivAtComplex hw .iE F₀ = yV from rfl] at hCS

  have hIprod : ∀ (p q : AdelicGL2 (𝓞 K) K → ℂ), Continuous p → Continuous q → ∀ (Cp Cq : ℝ),
      (∀ g, ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc (ideleNorm K (Matrix.GeneralLinearGroup.det g₀) / 2) (2 * ideleNorm K (Matrix.GeneralLinearGroup.det g₀)) → ‖p g‖ ≤ Cp) →
      (∀ g, ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc (ideleNorm K (Matrix.GeneralLinearGroup.det g₀) / 2) (2 * ideleNorm K (Matrix.GeneralLinearGroup.det g₀)) → ‖q g‖ ≤ Cq) →
      IntegrableOn (fun g => p g * conj (q g)) 𝓕 (adelicGLHaar (Fin 2) (𝓞 K) K) := by
    intro p q hp hq Cp Cq hCp hCq
    refine U6C.integrableOn_of_bdd 𝓕 h𝓕m h𝓕s hfin _ (hp.mul (Complex.continuous_conj.comp hq)) (C := Cp * Cq) ?_
    intro g hg; rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hCp g hg) (hCq g hg) (norm_nonneg _) ((norm_nonneg _).trans (hCp g hg))
  have hUb' := fun g hg => hUb B g (hB g hg).2.1 (hB g hg).2.2
  have hVb' := fun g hg => hVb B g (hB g hg).2.1 (hB g hg).2.2
  have hHb' := fun g hg => hHb B g (hB g hg).2.1 (hB g hg).2.2
  have iF := hIprod F₀ F₀ hxc hxc _ _ hBx hBx
  have iH := hIprod (archDerivAtComplex hw .H yH) F₀ (hHD .H) hxc _ _ (fun g hg => (hHb' g hg).2 .H) hBx
  have iU1 := hIprod (archDerivAtComplex hw .E yU) F₀ (hUD .E) hxc _ _ (fun g hg => (hUb' g hg).2 .E) hBx
  have iU2 := hIprod (archDerivAtComplex hw .Fm yU) F₀ (hUD .Fm) hxc _ _ (fun g hg => (hUb' g hg).2 .Fm) hBx
  have iV1 := hIprod (archDerivAtComplex hw .iFm yV) F₀ (hVD .iFm) hxc _ _ (fun g hg => (hVb' g hg).2 .iFm) hBx
  have iV2 := hIprod (archDerivAtComplex hw .iE yV) F₀ (hVD .iE) hxc _ _ (fun g hg => (hVb' g hg).2 .iE) hBx
  have jU1 := hIprod yU (archDerivAtComplex hw .E F₀) hUc (hDc .E) _ _ (fun g hg => (hUb' g hg).1) (fun g hg => hBDx g hg .E)
  have jU2 := hIprod yU (archDerivAtComplex hw .Fm F₀) hUc (hDc .Fm) _ _ (fun g hg => (hUb' g hg).1) (fun g hg => hBDx g hg .Fm)
  have jV1 := hIprod yV (archDerivAtComplex hw .iFm F₀) hVc (hDc .iFm) _ _ (fun g hg => (hVb' g hg).1) (fun g hg => hBDx g hg .iFm)
  have jV2 := hIprod yV (archDerivAtComplex hw .iE F₀) hVc (hDc .iE) _ _ (fun g hg => (hVb' g hg).1) (fun g hg => hBDx g hg .iE)

  have hint := congrArg (fun F : AdelicGL2 (𝓞 K) K → ℂ => ∫ g in 𝓕, F g * conj (F₀ g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) hCS

  set r : ℝ := ∫ g in 𝓕, ‖F₀ g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) with hr
  set rH : ℝ := ∫ g in 𝓕, ‖yH g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) with hrH
  set rU : ℝ := ∫ g in 𝓕, ‖yU g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) with hrU
  set rV : ℝ := ∫ g in 𝓕, ‖yV g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) with hrV

  have hL : (∫ g in 𝓕, (lam • F₀ + lam' • F₀) g * conj (F₀ g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) = (lam + lam') * (r : ℂ) := by
    rw [hr, ← U6C.setIntegral_mul_conj_self_eq, ← integral_const_mul]
    congr 1; funext g; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

  have qH : (∫ g in 𝓕, archDerivAtComplex hw .H yH g * conj (F₀ g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) = -(rH : ℂ) := by
    rw [sH, hrH, ← U6C.setIntegral_mul_conj_self_eq]
  have qU : (∫ g in 𝓕, archDerivAtComplex hw .E yU g * conj (F₀ g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))
      + (∫ g in 𝓕, archDerivAtComplex hw .Fm yU g * conj (F₀ g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) = -(rU : ℂ) := by
    rw [sU1, sU2, hrU, ← U6C.setIntegral_mul_conj_self_eq, ← neg_add, ← integral_add jU1 jU2]
    congr 2; funext g; rw [← mul_add, ← map_add]; rfl
  have qV : (∫ g in 𝓕, archDerivAtComplex hw .iFm yV g * conj (F₀ g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))
      - (∫ g in 𝓕, archDerivAtComplex hw .iE yV g * conj (F₀ g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) = -(rV : ℂ) := by
    rw [sV1, sV2, hrV, ← U6C.setIntegral_mul_conj_self_eq, neg_sub_neg, ← neg_sub, ← integral_sub jV1 jV2]
    congr 2; funext g; rw [← mul_sub, ← map_sub]; rfl

  set c0 : ℂ := (1 / 8 : ℂ) * (-(((n : ℂ) ^ 2 + 2 * (n : ℂ)))) with hc0
  set f1 : AdelicGL2 (𝓞 K) K → ℂ := fun g => c0 * (F₀ g * conj (F₀ g)) with hf1
  set f2 : AdelicGL2 (𝓞 K) K → ℂ := fun g => (1 / 8 : ℂ) * (archDerivAtComplex hw .H yH g * conj (F₀ g)) with hf2
  set f3 : AdelicGL2 (𝓞 K) K → ℂ := fun g => (1 / 8 : ℂ) * (archDerivAtComplex hw .E yU g * conj (F₀ g)) with hf3
  set f4 : AdelicGL2 (𝓞 K) K → ℂ := fun g => (1 / 8 : ℂ) * (archDerivAtComplex hw .Fm yU g * conj (F₀ g)) with hf4
  set f5 : AdelicGL2 (𝓞 K) K → ℂ := fun g => (1 / 8 : ℂ) * (archDerivAtComplex hw .iFm yV g * conj (F₀ g)) with hf5
  set f6 : AdelicGL2 (𝓞 K) K → ℂ := fun g => (1 / 8 : ℂ) * (archDerivAtComplex hw .iE yV g * conj (F₀ g)) with hf6
  have i1 : IntegrableOn f1 𝓕 (adelicGLHaar (Fin 2) (𝓞 K) K) := iF.const_mul _
  have i2 : IntegrableOn f2 𝓕 (adelicGLHaar (Fin 2) (𝓞 K) K) := iH.const_mul _
  have i3 : IntegrableOn f3 𝓕 (adelicGLHaar (Fin 2) (𝓞 K) K) := iU1.const_mul _
  have i4 : IntegrableOn f4 𝓕 (adelicGLHaar (Fin 2) (𝓞 K) K) := iU2.const_mul _
  have i5 : IntegrableOn f5 𝓕 (adelicGLHaar (Fin 2) (𝓞 K) K) := iV1.const_mul _
  have i6 : IntegrableOn f6 𝓕 (adelicGLHaar (Fin 2) (𝓞 K) K) := iV2.const_mul _
  have hRpt : ∀ g, ((1 / 8 : ℂ) • ((-(((n : ℂ) ^ 2 + 2 * (n : ℂ)))) • F₀) -
      (1 / 8 : ℂ) • (archDerivAtComplex hw .H yH + (archDerivAtComplex hw .E yU + archDerivAtComplex hw .Fm yU) +
        (archDerivAtComplex hw .iFm yV - archDerivAtComplex hw .iE yV))) g * conj (F₀ g)
      = (f1 - f2 - f3 - f4 - f5 + f6) g := by
    intro g
    simp only [hf1, hf2, hf3, hf4, hf5, hf6, hc0, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hR : (∫ g in 𝓕, ((1 / 8 : ℂ) • ((-(((n : ℂ) ^ 2 + 2 * (n : ℂ)))) • F₀) -
      (1 / 8 : ℂ) • (archDerivAtComplex hw .H yH + (archDerivAtComplex hw .E yU + archDerivAtComplex hw .Fm yU) +
        (archDerivAtComplex hw .iFm yV - archDerivAtComplex hw .iE yV))) g * conj (F₀ g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))
      = c0 * (r : ℂ) + (1 / 8 : ℂ) * ((rH : ℂ) + rU + rV) := by
    have step := integral_congr_ae (μ := (adelicGLHaar (Fin 2) (𝓞 K) K).restrict 𝓕) (Filter.Eventually.of_forall hRpt)
    rw [step, integral_add' ((((i1.sub i2).sub i3).sub i4).sub i5) i6, integral_sub' (((i1.sub i2).sub i3).sub i4) i5,
      integral_sub' ((i1.sub i2).sub i3) i4, integral_sub' (i1.sub i2) i3, integral_sub' i1 i2]
    simp only [hf1, hf2, hf3, hf4, hf5, hf6]
    rw [integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
      integral_const_mul, U6C.setIntegral_mul_conj_self_eq, ← hr, qH]
    linear_combination (-(1 / 8 : ℂ)) * qU - (1 / 8 : ℂ) * qV
  rw [hL, hR] at hint

  have hr0 : r ≠ 0 := U6C.setIntegral_norm_sq_ne_zero K _ _ he₁ he 𝓕 h𝓕m h𝓕s h𝓕 hfin F₀ hxc hxl
    (fun g hg => (hB g hg).1) ⟨g₀, hmem, hg₀⟩
  have hrpos : 0 < r := lt_of_le_of_ne (U6C.setIntegral_norm_sq_nonneg K 𝓕 F₀) (Ne.symm hr0)
  have hrH0 : 0 ≤ rH := U6C.setIntegral_norm_sq_nonneg K 𝓕 yH
  have hrU0 : 0 ≤ rU := U6C.setIntegral_norm_sq_nonneg K 𝓕 yU
  have hrV0 : 0 ≤ rV := U6C.setIntegral_norm_sq_nonneg K 𝓕 yV
  rw [hconj] at hint
  have hcast : c0 = ((-(((n : ℝ) ^ 2 + 2 * (n : ℝ)) / 8) : ℝ) : ℂ) := by
    rw [hc0]; push_cast; ring
  rw [hcast] at hint
  have hre := congrArg Complex.re hint
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
    mul_zero, sub_zero, Complex.add_im] at hre
  norm_num at hre

  by_contra hneg
  push_neg at hneg
  have h1 : (lam.re + ((n : ℝ) ^ 2 + 2 * (n : ℝ)) / 16) * r < 0 := mul_neg_of_neg_of_pos (by linarith) hrpos
  nlinarith [hre, hrH0, hrU0, hrV0, h1]

end
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_neg_le_casimir_re_of_highestWeight_of_isCuspConstituent_of_isComplex.U6C"

end S_AutomorphicForm_CuspidalConstituent_neg_le_casimir_re_of_highestWeight_of_isCuspConstituent_of_isComplex
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_neg_le_casimir_re_of_highestWeight_of_isCuspConstituent_of_isComplex (solution)
