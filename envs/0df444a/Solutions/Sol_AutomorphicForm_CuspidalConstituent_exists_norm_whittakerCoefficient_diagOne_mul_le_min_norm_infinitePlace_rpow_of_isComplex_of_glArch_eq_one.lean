-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.exists_norm_whittakerCoefficient_diagOne_mul_le_min_norm_infinitePlace_rpow_of_isComplex_of_glArch_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/cc1f3302-4940-5003-8715-b7c1f07c8b50

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplexAPI
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_forall_isArchSmoothAtComplex_and_archCasimirAtComplex_eq_smul_of_isCuspConstituent
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_eq_sum_su2String_highestWeight_of_mem_cut_of_isComplex
import Theorems.Thm_AutomorphicForm_exists_norm_whittakerCoefficient_diagOne_le_min_norm_rpow_of_isComplex_of_su2String
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_casimirBar_eq_conj_and_sl2Invariant_of_casimir_eq_zero_of_isCuspConstituent_of_isComplex
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_sum_smul_of_continuous
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_neg_le_casimir_re_of_highestWeight_of_isCuspConstituent_of_isComplex
import Theorems.Thm_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_exists_norm_whittakerCoefficient_diagOne_mul_le_min_norm_infinitePlace_rpow_of_isComplex_of_glArch_eq_one
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

noncomputable section

namespace C1E43

variable {K : Type} [Field K] [NumberField K]

theorem foldr_archDerivAtComplex_comp_mul_right {w : InfinitePlace K} (hw : w.IsComplex) (l : List ArchDirComplex)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) {k : AdelicGL2 (𝓞 K) K} (hk : glArch (𝓞 K) K k = 1) :
    l.foldr (archDerivAtComplex hw) (fun h => φ (h * k)) = fun h => (l.foldr (archDerivAtComplex hw) φ) (h * k) := by
  induction l with
  | nil => rfl
  | cons d l ih =>
    simp only [List.foldr_cons]
    rw [ih, archDerivAtComplex_comp_mul_right hw d _ hk]

theorem whittakerCoefficient_mul_right (pins : CarrierPins K) (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (α : K) (g k : AdelicGL2 (𝓞 K) K) :
    whittakerCoefficient K pins ψ φ α (g * k) = whittakerCoefficient K pins ψ (fun y => φ (y * k)) α g := by
  letI := pins.nS
  simp only [whittakerCoefficient, mul_assoc]

theorem prod_min_one_le {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℝ) (hf : ∀ i, 0 < f i) (i : ι) :
    ∏ j, min (f j) 1 ≤ f i := by
  calc ∏ j, min (f j) 1 = min (f i) 1 * ∏ j ∈ Finset.univ.erase i, min (f j) 1 :=
        (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
    _ ≤ min (f i) 1 * 1 := by
        refine mul_le_mul_of_nonneg_left (Finset.prod_le_one (fun j _ => ?_) fun j _ => min_le_right _ _) ?_
        · exact le_min (hf j).le zero_le_one
        · exact le_min (hf i).le zero_le_one
    _ ≤ f i := by rw [mul_one]; exact min_le_left _ _

theorem main
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (tys : AutomorphicForm.ArchTypeFamily K)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ V)
    (y : AdelicGL2 (𝓞 K) K → ℂ)
    (hy : y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (w : InfinitePlace K) (hw : w.IsComplex)
    (b : (AdeleRing (𝓞 K) K)ˣ) (hb : ((b : AdeleRing (𝓞 K) K)).2 = 1)
    (g : AdelicGL2 (𝓞 K) K) (hg : glArch (𝓞 K) K g = 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ,
      ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
        (∀ w' : InfinitePlace K, w' ≠ w → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w') →
        ‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
              (diagOne a * g)‖ ≤ C * ‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) *
            (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 w‖) ^ δ := by
  classical

  have hψc : Continuous (NumberField.StandardAddChar.stdAddChar K) :=
    (NumberField.StandardAddChar.isGlobalAddChar_stdAddChar K).continuous

  by_cases hy0 : y = 0
  · refine ⟨1, one_pos, 0, fun a _ _ => ?_⟩
    subst hy0
    have h0 : whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (0 : AdelicGL2 (𝓞 K) K → ℂ) 1 (diagOne a * g) = 0 := by
      have h := AutomorphicForm.whittakerCoefficient_sum_smul_of_continuous K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (NumberField.StandardAddChar.stdAddChar K) hψc 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) 1 (diagOne a * g)
      simp only [Finset.univ_eq_empty, Finset.sum_empty] at h
      exact h
    rw [h0, norm_zero]; positivity
  have hX : V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys ≠ ⊥ := by
    intro h
    exact hy0 ((Submodule.eq_bot_iff _).mp h y hy)

  obtain ⟨lam, lam', hlam⟩ := AutomorphicForm.CuspidalConstituent.exists_forall_isArchSmoothAtComplex_and_archCasimirAtComplex_eq_smul_of_isCuspConstituent K c u d₁ d₂ T hc hd₁ hd hcov ξ V hV N hN tys hX w hw

  obtain ⟨hU, hZ0⟩ := AutomorphicForm.CuspidalConstituent.casimirBar_eq_conj_and_sl2Invariant_of_casimir_eq_zero_of_isCuspConstituent_of_isComplex K c u d₁ d₂ T hc hd₁ hd hcov ξ V hV N hN tys hX w hw w₀ hξ lam lam' hlam

  obtain ⟨m, n, x, coef, E₁, E₂, hsum, hS⟩ :=
    AutomorphicForm.CuspidalConstituent.exists_eq_sum_su2String_highestWeight_of_mem_cut_of_isComplex K c u d₁ d₂ T hc hd₁ hd hcov ξ V hV N hN tys hX w hw y hy w₀ hξ lam lam' hlam

  have hUNIT : ∀ s : Fin m, lam' = lam → lam.im = 0 → n s = 0 ∨ -(((n s : ℝ) ^ 2 + 4 * (n s : ℝ)) / 16) < lam.re := by
    intro s _ _
    by_cases hns : n s = 0
    · exact Or.inl hns
    · right
      obtain ⟨hmem, hne, -, hHW, hJ, -⟩ := hS s
      have h5 := AutomorphicForm.CuspidalConstituent.neg_le_casimir_re_of_highestWeight_of_isCuspConstituent_of_isComplex K c u d₁ d₂ T hc hd₁ hd hcov ξ V hV N hN tys hX w hw w₀ hξ lam lam' hlam
        (n s) N hN tys (x s 0) (hmem 0) hne hHW hJ
      have hn1 : (1 : ℝ) ≤ (n s : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hns
      nlinarith [h5, hn1]

  have hstr : ∀ s : Fin m, ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ p : Fin (n s + 1),
      ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
        (∀ w' : InfinitePlace K, w' ≠ w → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w') →
        ‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (x s p) 1 (diagOne a * g)‖ ≤ C * ‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) *
            (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 w‖) ^ δ := by
    intro s
    obtain ⟨hmem, hne, hchar, hHW, hJ, hxc, hxG, hxZ, hreg, hwt, hE₁0, hE₂0, hE₁', hE₂', hK₁, hK₂, hcas, hgr⟩ := hS s

    set x' : Fin (n s + 1) → (AdelicGL2 (𝓞 K) K → ℂ) := fun p h => x s p (h * g) with hx'
    have hxc' : ∀ p, Continuous (x' p) := fun p => (hxc p).comp (continuous_mul_const g)
    have hxG' : ∀ p (γ : GL (Fin 2) K) (g' : AdelicGL2 (𝓞 K) K), x' p (globalPoints (𝓞 K) K γ * g') = x' p g' := by
      intro p γ g'; simp only [hx', mul_assoc]; exact hxG p γ (g' * g)
    have hxZ' : ∀ p (z : (AdeleRing (𝓞 K) K)ˣ) (g' : AdelicGL2 (𝓞 K) K),
        x' p (centralScalar (𝓞 K) K z * g') = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x' p g' := by
      intro p z g'; simp only [hx', mul_assoc]; exact hxZ p z (g' * g)
    have hreg' : ∀ p (l : List ArchDirComplex),
        IsArchSmoothAtComplex hw (l.foldr (archDerivAtComplex hw) (x' p)) ∧ Continuous (l.foldr (archDerivAtComplex hw) (x' p)) := by
      intro p l
      have hf : l.foldr (archDerivAtComplex hw) (x' p) = fun h => (l.foldr (archDerivAtComplex hw) (x s p)) (h * g) :=
        foldr_archDerivAtComplex_comp_mul_right hw l (x s p) hg
      rw [hf]
      exact ⟨(hreg p l).1.comp_mul_right hg, (hreg p l).2.comp (continuous_mul_const g)⟩
    have hwt' : ∀ p : Fin (n s + 1), HasCircleWeightAt hw ((n s : ℤ) - 2 * (p : ℕ)) (x' p) := fun p =>
      (hwt p).comp_mul_right hg
    have hK₁' : ∀ (p : Fin (n s + 1)) (r : ℝ) (g' : AdelicGL2 (𝓞 K) K),
        x' p (g' * archComplexLiftAt hw !![(Real.cos r : ℂ), -(Real.sin r : ℂ); (Real.sin r : ℂ), (Real.cos r : ℂ)]) =
          ∑ p' : Fin (n s + 1), E₁ s r p' p * x' p' g' := by
      intro p r g'
      simp only [hx']
      rw [mul_assoc, archComplexLiftAt_mul_comm_of_glArch_eq_one hw _ hg, ← mul_assoc]
      exact hK₁ p r (g' * g)
    have hK₂' : ∀ (p : Fin (n s + 1)) (r : ℝ) (g' : AdelicGL2 (𝓞 K) K),
        x' p (g' * archComplexLiftAt hw !![(Real.cos r : ℂ), (Real.sin r : ℂ) * Complex.I; (Real.sin r : ℂ) * Complex.I, (Real.cos r : ℂ)]) =
          ∑ p' : Fin (n s + 1), E₂ s r p' p * x' p' g' := by
      intro p r g'
      simp only [hx']
      rw [mul_assoc, archComplexLiftAt_mul_comm_of_glArch_eq_one hw _ hg, ← mul_assoc]
      exact hK₂ p r (g' * g)
    have hcas' : ∀ p, archCasimirAtComplex hw (x' p) = lam • x' p ∧ archCasimirBarAtComplex hw (x' p) = lam' • x' p := by
      intro p
      refine ⟨?_, ?_⟩
      · rw [show x' p = fun h => x s p (h * g) from rfl, archCasimirAtComplex_comp_mul_right hw _ hg, (hcas p).1]; rfl
      · rw [show x' p = fun h => x s p (h * g) from rfl, archCasimirBarAtComplex_comp_mul_right hw _ hg, (hcas p).2]; rfl
    have hgr' : ∀ p, ∃ C₀ : ℝ, ∀ g' : AdelicGL2 (𝓞 K) K,
        ‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (x' p) 1 (g')‖ ≤ C₀ * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g') ^ (w₀ / 2) := by
      intro p
      obtain ⟨C₀, hC₀⟩ := hgr p
      refine ⟨C₀ * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w₀ / 2), fun g' => ?_⟩
      rw [show x' p = fun h => x s p (h * g) from rfl, ← whittakerCoefficient_mul_right]
      refine (hC₀ (g' * g)).trans (le_of_eq ?_)
      rw [map_mul, NumberField.TateGlobal.ideleNorm_mul,
        Real.mul_rpow (NumberField.TateGlobal.ideleNorm_pos _).le (NumberField.TateGlobal.ideleNorm_pos _).le]
      ring
    have hZ' : lam = 0 → n s = 0 → ∀ (g'' : AdelicGL2 (𝓞 K) K) (h : GL (Fin 2) ℂ),
        Matrix.GeneralLinearGroup.det h = 1 → x' 0 (g'' * archComplexGLAt hw h) = x' 0 g'' := by
      intro hl hn g'' h hh
      simp only [hx']
      rw [mul_assoc, archComplexGLAt_mul_comm_of_glArch_eq_one hw h hg, ← mul_assoc]
      exact hZ0 hl N hN tys (x s 0) (hmem 0) (hchar hn) (g'' * g) h hh
    obtain ⟨δ, hδ, C, hC⟩ := AutomorphicForm.exists_norm_whittakerCoefficient_diagOne_le_min_norm_rpow_of_isComplex_of_su2String K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
      ξ w₀ hξ w hw (n s) x' hxc' hxG' hxZ' hreg' hwt' (E₁ s) (E₂ s) hE₁0 hE₂0 hE₁' hE₂' hK₁' hK₂' lam lam' hcas' hgr'
      (by rw [hU]) (hUNIT s) hZ' b hb
    refine ⟨δ, hδ, C, fun p a ha hab => ?_⟩
    have h := hC p a ha hab
    rwa [show x' p = fun h => x s p (h * g) from rfl, ← whittakerCoefficient_mul_right] at h

  choose δs hδs Cs hCs using hstr
  refine ⟨∏ s, min (δs s) 1, Finset.prod_pos fun s _ => lt_min (hδs s) one_pos,
    ∑ s : Fin m, ∑ p : Fin (n s + 1), ‖coef s p‖ * max (Cs s) 0, fun a ha hab => ?_⟩
  have hapos : 0 < ‖((a : AdeleRing (𝓞 K) K)).1 w‖ := by
    refine norm_pos_iff.mpr fun h0 => ?_
    have h1 : (((a * a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w = 1 := by rw [mul_inv_cancel]; rfl
    have h2 : (((a * a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w =
        ((a : AdeleRing (𝓞 K) K)).1 w * (((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w := rfl
    rw [h2, h0, zero_mul] at h1
    exact zero_ne_one h1

  have hlin : whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1 (diagOne a * g) =
      ∑ s : Fin m, ∑ p : Fin (n s + 1), coef s p * whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (x s p) 1 (diagOne a * g) := by
    have hin : ∀ s : Fin m, whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (fun h => ∑ p : Fin (n s + 1), coef s p * x s p h) 1 (diagOne a * g) =
        ∑ p : Fin (n s + 1), coef s p * whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (x s p) 1 (diagOne a * g) := fun s =>
      AutomorphicForm.whittakerCoefficient_sum_smul_of_continuous K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (NumberField.StandardAddChar.stdAddChar K) hψc (n s + 1) (x s) (fun p => (hS s).2.2.2.2.2.1 p) (coef s) 1 (diagOne a * g)
    have hy' : y = fun h => ∑ s : Fin m, (1 : ℂ) * (fun h => ∑ p : Fin (n s + 1), coef s p * x s p h) h := by
      funext h
      rw [hsum]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, one_mul]
    have hout := AutomorphicForm.whittakerCoefficient_sum_smul_of_continuous K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (NumberField.StandardAddChar.stdAddChar K) hψc m (fun s => fun h => ∑ p : Fin (n s + 1), coef s p * x s p h)
        (fun s => continuous_finsetSum _ fun p _ => continuous_const.mul ((hS s).2.2.2.2.2.1 p)) (fun _ => 1) 1 (diagOne a * g)
    rw [hy', hout]
    simp only [one_mul, hin]
  rw [hlin]

  have hterm : ∀ (s : Fin m) (p : Fin (n s + 1)),
      ‖coef s p * whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (x s p) 1 (diagOne a * g)‖ ≤
        ‖coef s p‖ * max (Cs s) 0 * (‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) *
          (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 w‖) ^ (∏ s, min (δs s) 1)) := by
    intro s p
    rw [norm_mul, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine (hCs s p a ha hab).trans ?_
    have hmin0 : 0 < min 1 ‖((a : AdeleRing (𝓞 K) K)).1 w‖ := lt_min one_pos hapos
    have hmin1 : min 1 ‖((a : AdeleRing (𝓞 K) K)).1 w‖ ≤ 1 := min_le_left _ _
    have hpow : (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 w‖) ^ δs s ≤ (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 w‖) ^ (∏ s, min (δs s) 1) :=
      Real.rpow_le_rpow_of_exponent_ge hmin0 hmin1 (prod_min_one_le δs hδs s)
    have hX : 0 ≤ ‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) * (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 w‖) ^ δs s := mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg hmin0.le _)
    calc Cs s * ‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) * (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 w‖) ^ δs s = Cs s * (‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) * (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 w‖) ^ δs s) := by ring
      _ ≤ max (Cs s) 0 * (‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) * (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 w‖) ^ δs s) := mul_le_mul_of_nonneg_right (le_max_left _ _) hX
      _ ≤ max (Cs s) 0 * (‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) * (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 w‖) ^ (∏ s, min (δs s) 1)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg (norm_nonneg _) _)) (le_max_right _ _)
  calc ‖∑ s : Fin m, ∑ p : Fin (n s + 1), coef s p * whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (x s p) 1 (diagOne a * g)‖
      ≤ ∑ s : Fin m, ∑ p : Fin (n s + 1), ‖coef s p * whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (x s p) 1 (diagOne a * g)‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => norm_sum_le _ _)
    _ ≤ ∑ s : Fin m, ∑ p : Fin (n s + 1), ‖coef s p‖ * max (Cs s) 0 * (‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) *
          (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 w‖) ^ (∏ s, min (δs s) 1)) :=
        Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun p _ => hterm s p
    _ = (∑ s : Fin m, ∑ p : Fin (n s + 1), ‖coef s p‖ * max (Cs s) 0) * ‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) *
            (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 w‖) ^ (∏ s, min (δs s) 1) := by
        rw [Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun p _ => ?_
        ring

end C1E43

end

theorem solution
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (tys : AutomorphicForm.ArchTypeFamily K)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ V)
    (y : AdelicGL2 (𝓞 K) K → ℂ)
    (hy : y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (w : InfinitePlace K) (hw : w.IsComplex)
    (b : (AdeleRing (𝓞 K) K)ˣ) (hb : ((b : AdeleRing (𝓞 K) K)).2 = 1)
    (g : AdelicGL2 (𝓞 K) K) (hg : glArch (𝓞 K) K g = 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ,
      ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
        (∀ w' : InfinitePlace K, w' ≠ w → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w') →
        ‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
              (diagOne a * g)‖ ≤ C * ‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) *
            (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 w‖) ^ δ :=
  C1E43.main K c u d₁ d₂ T hc hd₁ hd hcov ξ N hN tys V hV y hy w₀ hξ w hw b hb g hg

end S_AutomorphicForm_CuspidalConstituent_exists_norm_whittakerCoefficient_diagOne_mul_le_min_norm_infinitePlace_rpow_of_isComplex_of_glArch_eq_one
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_exists_norm_whittakerCoefficient_diagOne_mul_le_min_norm_infinitePlace_rpow_of_isComplex_of_glArch_eq_one (solution)
