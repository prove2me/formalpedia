-- Prove2me | solution 1 for AutomorphicForm.exists_continuous_invariant_bandSupported_eLpNorm_sub_lt_of_isSlabProfile
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/62a144dd-1c0d-56e2-a455-23d26af5243c

import Theorems.Thm_NumberField_Idele_aestronglyMeasurable_of_continuous_prod_maximalCompact
import Theorems.Thm_NumberField_AdelicHeight_adelicHeight_diagOne_mul
import Theorems.Thm_NumberField_AdelicHeight_adelicHeight_mul_of_mem_adelicMaximalCompact
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_Idele_idelicHaar_inter_setOf_ideleNorm_mem_Icc_pos_and_lt_top
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_one_of_isCompact_of_mem
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_AutomorphicForm_exists_continuous_forall_principalIdeles_eLpNorm_sub_lt_of_memLp_withDensity_ideleNorm_inv_prod_maximalCompactHaar
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_CarrierPins
import Mathlib.Analysis.Meromorphic.NormalForm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_continuous_invariant_bandSupported_eLpNorm_sub_lt_of_isSlabProfile
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm
open scoped NNReal ENNReal Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

theorem solution
    (F : Type) [Field F] [NumberField F]
    (Φ : Set (AdelicGL2 (𝓞 F) F))
    (ξ : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : AutomorphicForm.IsSlabProfile F
      (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z ξ φ)
    (a b : ℝ) (ha : 0 < a)
    (hband : ∀ g : AdelicGL2 (𝓞 F) F, φ g ≠ 0 → NumberField.AdelicHeight.adelicHeight F g ∈ Set.Icc a b)
    (a' b' : ℝ) (ha' : 0 < a') (haa' : a' < a) (hbb' : b < b')
    (D : Set (AdeleRing (𝓞 F) F)ˣ) (hDm : MeasurableSet D)
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (G : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) → ℂ) (a₁ b₁ : ℝ),
      Continuous G ∧ a' < a₁ ∧ b₁ < b' ∧
      (∀ γ ∈ M4aHerbrand.principalIdeles (𝓞 F) F, ∀ p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F), G (γ * p.1, p.2) = G p) ∧
      (∀ p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F), G p ≠ 0 → NumberField.TateGlobal.ideleNorm F p.1 ∈ Set.Icc a₁ b₁) ∧
      AEStronglyMeasurable (fun p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) =>
          φ (NumberField.AdelicLevel.diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F)) - G p)
        ((((NumberField.Idele.idelicHaar F).restrict D).withDensity
            (fun t : (AdeleRing (𝓞 F) F)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹))).prod
          (maximalCompactHaar F)) ∧
      eLpNorm (fun p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) =>
          φ (NumberField.AdelicLevel.diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F)) - G p) 2
        ((((NumberField.Idele.idelicHaar F).restrict D).withDensity
            (fun t : (AdeleRing (𝓞 F) F)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹))).prod
          (maximalCompactHaar F)) < ENNReal.ofReal δ := by
  classical

  haveI hscA : SecondCountableTopology (AdeleRing (𝓞 F) F) := NumberField.AdeleRing.secondCountableTopology F
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  haveI hscU : SecondCountableTopology (AdeleRing (𝓞 F) F)ˣ := Units.isInducing_embedProduct.secondCountableTopology

  set μD : Measure (AdeleRing (𝓞 F) F)ˣ := ((NumberField.Idele.idelicHaar F).restrict D).withDensity
      (fun t : (AdeleRing (𝓞 F) F)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹)) with hμD
  set ρ : Measure ((AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F)) := μD.prod (maximalCompactHaar F) with hρ
  obtain ⟨f, hf⟩ : ∃ f : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) → ℂ, f = fun p => φ (NumberField.AdelicLevel.diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F)) :=
    ⟨_, rfl⟩

  have hdiagc : Continuous (fun t : (AdeleRing (𝓞 F) F)ˣ => (NumberField.AdelicLevel.diagOne t : AdelicGL2 (𝓞 F) F)) := by
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · refine continuous_matrix fun i j => ?_
      fin_cases i <;> fin_cases j
      · simpa [NumberField.AdelicLevel.diagOne_coe_apply] using Units.continuous_val
      · simpa [NumberField.AdelicLevel.diagOne_coe_apply] using continuous_const
      · simpa [NumberField.AdelicLevel.diagOne_coe_apply] using continuous_const
      · simpa [NumberField.AdelicLevel.diagOne_coe_apply] using continuous_const
    · have h : (fun t : (AdeleRing (𝓞 F) F)ˣ => (((NumberField.AdelicLevel.diagOne t)⁻¹ : AdelicGL2 (𝓞 F) F) :
          Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))) =
          fun t => Matrix.diagonal ![((t⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F), 1] := by
        funext t; rw [← map_inv]; rfl
      rw [h]
      refine continuous_matrix fun i j => ?_
      fin_cases i <;> fin_cases j
      · simpa [Matrix.diagonal] using Units.continuous_coe_inv
      · simpa [Matrix.diagonal] using continuous_const
      · simpa [Matrix.diagonal] using continuous_const
      · simpa [Matrix.diagonal] using continuous_const
  have hmapc : Continuous (fun p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) => NumberField.AdelicLevel.diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F)) :=
    (hdiagc.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)

  have hfm : Measurable f := by
    rw [hf]; exact hφ.measurable.comp hmapc.measurable

  have hK1 : NumberField.AdelicHeight.adelicHeight F (1 : AdelicGL2 (𝓞 F) F) = 1 := by
    rw [NumberField.AdelicHeight.adelicHeight_eq_archHeight_of_mem (by rw [map_one]; exact one_mem _), map_one,
      AutomorphicForm.WindowedSiegel.archHeight_one]
  have hheight : ∀ p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F), NumberField.AdelicHeight.adelicHeight F
      (NumberField.AdelicLevel.diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F)) = NumberField.TateGlobal.ideleNorm F p.1 := by
    intro p
    rw [NumberField.AdelicHeight.adelicHeight_diagOne_mul,
      show ((p.2 : AdelicGL2 (𝓞 F) F)) = 1 * (p.2 : AdelicGL2 (𝓞 F) F) from (one_mul _).symm,
      NumberField.AdelicHeight.adelicHeight_mul_of_mem_adelicMaximalCompact F 1 _ p.2.2, hK1, mul_one]
  have hfsupp : ∀ p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F), f p ≠ 0 → NumberField.TateGlobal.ideleNorm F p.1 ∈ Set.Icc a b := by
    intro p hp
    rw [hf] at hp
    rw [← hheight p]
    exact hband _ hp
  have hdet : ∀ p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F), NumberField.TateGlobal.ideleNorm F
      (Matrix.GeneralLinearGroup.det (NumberField.AdelicLevel.diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F))) =
        NumberField.TateGlobal.ideleNorm F p.1 := by
    intro p
    rw [map_mul, NumberField.TateGlobal.ideleNorm_mul,
      NumberField.TateGlobal.ideleNorm_det_eq_one_of_isCompact_of_mem F (adelicMaximalCompact F)
        (AutomorphicForm.isCompact_adelicMaximalCompact F) _ p.2.2, mul_one]
    have : Matrix.GeneralLinearGroup.det (NumberField.AdelicLevel.diagOne p.1) = p.1 := by
      apply Units.ext
      simp [Matrix.GeneralLinearGroup.val_det_apply, NumberField.AdelicLevel.diagOne]
    rw [this]
  obtain ⟨C₀, hC₀⟩ := hφ.bounded_on_slab a b ha
  have hC : ∀ p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F), ‖f p‖ ≤ max C₀ 0 := by
    intro p
    by_cases hp : f p = 0
    · rw [hp, norm_zero]; exact le_max_right _ _
    · have hb := hfsupp p hp
      rw [hf]
      exact (hC₀ _ (by rw [hdet p]; exact hb)).trans (le_max_left _ _)

  have hdetdiag : ∀ t : (AdeleRing (𝓞 F) F)ˣ, Matrix.GeneralLinearGroup.det (NumberField.AdelicLevel.diagOne t) = t := by
    intro t; apply Units.ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, NumberField.AdelicLevel.diagOne]
  have hglob : ∀ γ₀ : Fˣ, NumberField.AdelicLevel.diagOne
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) γ₀) =
        AutomorphicForm.globalPoints (𝓞 F) F (NumberField.AdelicLevel.diagOne γ₀) := by
    intro γ₀
    apply Units.ext
    ext i j
    change (NumberField.AdelicLevel.diagOne (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) γ₀) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j =
      algebraMap F (AdeleRing (𝓞 F) F) ((NumberField.AdelicLevel.diagOne γ₀ : Matrix (Fin 2) (Fin 2) F) i j)
    fin_cases i <;> fin_cases j <;>
      simp [NumberField.AdelicLevel.diagOne_coe_apply, Matrix.diagonal]
  have hBorel : ∀ γ₀ : Fˣ, NumberField.AdelicLevel.diagOne γ₀ ∈ AutomorphicForm.borelSubgroup F := by
    intro γ₀
    simp [AutomorphicForm.mem_borelSubgroup_iff, NumberField.AdelicLevel.diagOne_coe_apply, Matrix.diagonal]
  have hnorm_principal : ∀ γ ∈ M4aHerbrand.principalIdeles (𝓞 F) F, NumberField.TateGlobal.ideleNorm F γ = 1 := by
    intro γ hγ
    obtain ⟨γ₀, rfl⟩ := MonoidHom.mem_range.mp hγ
    rw [← hdetdiag (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) γ₀), hglob]
    exact AutomorphicForm.ideleNorm_det_globalPoints _

  have hfinv : ∀ γ ∈ M4aHerbrand.principalIdeles (𝓞 F) F, ∀ p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F), f (γ * p.1, p.2) = f p := by
    intro γ hγ p
    obtain ⟨γ₀, rfl⟩ := MonoidHom.mem_range.mp hγ
    rw [hf]
    simp only
    rw [map_mul, mul_assoc, hglob, hφ.borel_mul _ (hBorel γ₀)]

  set Bnd : Set ((AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F)) := {p | NumberField.TateGlobal.ideleNorm F p.1 ∈ Set.Icc a b} with hBnd
  have hBndm : MeasurableSet Bnd :=
    ((NumberField.TateGlobal.continuous_ideleNorm F).comp continuous_fst).measurable measurableSet_Icc
  have hband_fin : ρ Bnd < ⊤ := by
    set S : Set (AdeleRing (𝓞 F) F)ˣ := {t | NumberField.TateGlobal.ideleNorm F t ∈ Set.Icc a b} with hS
    have hSmeas : MeasurableSet S :=
      (NumberField.TateGlobal.continuous_ideleNorm F).measurable measurableSet_Icc
    have hset : Bnd = S ×ˢ (Set.univ : Set ↥(adelicMaximalCompact F)) := by
      ext p; simp [hBnd, hS]
    rw [hset, hρ]
    refine lt_of_le_of_lt (Measure.prod_prod_le _ _) ?_
    rw [measure_univ, mul_one, hμD, withDensity_apply _ hSmeas]
    have hbound : ∫⁻ t in S, ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹)
        ∂((NumberField.Idele.idelicHaar F).restrict D) ≤
        ∫⁻ t in S, ENNReal.ofReal (a⁻¹) ∂((NumberField.Idele.idelicHaar F).restrict D) := by
      refine setLIntegral_mono' hSmeas (fun t ht => ?_)
      exact ENNReal.ofReal_le_ofReal (inv_anti₀ ha ht.1)
    refine lt_of_le_of_lt hbound ?_
    rw [setLIntegral_const, Measure.restrict_apply hSmeas]
    have hlt := (NumberField.Idele.idelicHaar_inter_setOf_ideleNorm_mem_Icc_pos_and_lt_top F D hDm hDF a
      (max b a + 1) ha (by have := le_max_right b a; linarith)).2
    have hsub : S ∩ D ⊆ D ∩ {z | NumberField.TateGlobal.ideleNorm F z ∈ Set.Icc a (max b a + 1)} := by
      rintro t ⟨ht, htD⟩
      exact ⟨htD, ht.1, le_trans ht.2 (by have := le_max_left b a; linarith)⟩
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_of_le_of_lt (measure_mono hsub) hlt)

  have hfL2 : MemLp f 2 ρ := by
    have hg : MemLp (Bnd.indicator fun _ => (max C₀ 0 : ℝ)) 2 ρ :=
      memLp_indicator_const 2 hBndm (max C₀ 0) (Or.inr hband_fin.ne)
    refine MemLp.of_le hg hfm.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    by_cases hp : p ∈ Bnd
    · rw [Set.indicator_of_mem hp, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact hC p
    · have : f p = 0 := by
        by_contra h
        exact hp (hfsupp p h)
      rw [this, norm_zero]
      exact norm_nonneg _

  obtain ⟨G₀, hG₀c, hG₀inv, hG₀close⟩ :=
    AutomorphicForm.exists_continuous_forall_principalIdeles_eLpNorm_sub_lt_of_memLp_withDensity_ideleNorm_inv_prod_maximalCompactHaar
      F D hDm hDF f hfinv (by rw [hρ, hμD] at hfL2; exact hfL2) δ hδ

  set a₁ : ℝ := (a' + a) / 2 with ha₁
  set b₁ : ℝ := (b + b') / 2 with hb₁
  have ha₁a : a₁ < a := by rw [ha₁]; linarith
  have hbb₁ : b < b₁ := by rw [hb₁]; linarith
  set θ : ℝ → ℝ := fun x => max 0 (min 1 (min ((x - a₁) / (a - a₁)) ((b₁ - x) / (b₁ - b)))) with hθ
  have hθc : Continuous θ := by
    rw [hθ]
    exact continuous_const.max (continuous_const.min
      (((continuous_id.sub continuous_const).div_const _).min ((continuous_const.sub continuous_id).div_const _)))
  have hθ01 : ∀ x, 0 ≤ θ x ∧ θ x ≤ 1 := fun x =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hθ1 : ∀ x ∈ Set.Icc a b, θ x = 1 := by
    intro x hx
    have h1 : 1 ≤ (x - a₁) / (a - a₁) := by
      rw [le_div_iff₀ (by linarith)]; linarith [hx.1]
    have h2 : 1 ≤ (b₁ - x) / (b₁ - b) := by
      rw [le_div_iff₀ (by linarith)]; linarith [hx.2]
    rw [hθ]
    simp only
    rw [min_eq_left (le_min h1 h2), max_eq_right zero_le_one]
  have hθ0 : ∀ x, x ∉ Set.Icc a₁ b₁ → θ x = 0 := by
    intro x hx
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
    rw [hθ]
    simp only
    refine max_eq_left (min_le_iff.mpr (Or.inr ?_))
    rcases hx with hx | hx
    · exact min_le_iff.mpr (Or.inl (by rw [div_nonpos_iff]; right; constructor <;> linarith))
    · exact min_le_iff.mpr (Or.inr (by rw [div_nonpos_iff]; right; constructor <;> linarith))
  have hnorm_inv : ∀ γ ∈ M4aHerbrand.principalIdeles (𝓞 F) F, ∀ t : (AdeleRing (𝓞 F) F)ˣ,
      NumberField.TateGlobal.ideleNorm F (γ * t) = NumberField.TateGlobal.ideleNorm F t := by
    intro γ hγ t
    rw [NumberField.TateGlobal.ideleNorm_mul, hnorm_principal γ hγ, one_mul]
  have hGc : Continuous (fun p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) => ((θ (NumberField.TateGlobal.ideleNorm F p.1) : ℝ) : ℂ) * G₀ p) :=
    (Complex.continuous_ofReal.comp (hθc.comp ((NumberField.TateGlobal.continuous_ideleNorm F).comp continuous_fst))).mul hG₀c
  refine ⟨fun p => ((θ (NumberField.TateGlobal.ideleNorm F p.1) : ℝ) : ℂ) * G₀ p, a₁, b₁, hGc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ha₁]; linarith
  · rw [hb₁]; linarith
  · intro γ hγ p
    simp only
    rw [hnorm_inv γ hγ, hG₀inv γ hγ]
  · intro p hp
    by_contra hmem
    apply hp
    simp only
    rw [hθ0 _ hmem, Complex.ofReal_zero, zero_mul]
  · have h1 : AEStronglyMeasurable f ρ := hfm.aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) => ((θ (NumberField.TateGlobal.ideleNorm F p.1) : ℝ) : ℂ) * G₀ p) ρ := by
      rw [hρ, hμD]
      exact NumberField.Idele.aestronglyMeasurable_of_continuous_prod_maximalCompact F D hDm _ hGc
    have h3 := h1.sub h2
    rw [hf] at h3
    exact h3
  ·
    have hpt : ∀ p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F),
        ‖φ (NumberField.AdelicLevel.diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F)) -
            ((θ (NumberField.TateGlobal.ideleNorm F p.1) : ℝ) : ℂ) * G₀ p‖ ≤ ‖f p - G₀ p‖ := by
      intro p
      have hfp : φ (NumberField.AdelicLevel.diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F)) = f p := by rw [hf]
      rw [hfp]
      by_cases hzero : f p = 0
      · rw [hzero, zero_sub, zero_sub, norm_neg, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hθ01 _).1]
        calc θ (NumberField.TateGlobal.ideleNorm F p.1) * ‖G₀ p‖ ≤ 1 * ‖G₀ p‖ :=
              mul_le_mul_of_nonneg_right (hθ01 _).2 (norm_nonneg _)
          _ = ‖G₀ p‖ := one_mul _
      · rw [hθ1 _ (hfsupp p hzero), Complex.ofReal_one, one_mul]
    calc eLpNorm (fun p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) => φ (NumberField.AdelicLevel.diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F)) -
            ((θ (NumberField.TateGlobal.ideleNorm F p.1) : ℝ) : ℂ) * G₀ p) 2 _
        ≤ eLpNorm (fun p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) => f p - G₀ p) 2 _ := eLpNorm_mono (fun p => hpt p)
      _ < ENNReal.ofReal δ := by rw [hρ, hμD]; exact hG₀close

end

end S_AutomorphicForm_exists_continuous_invariant_bandSupported_eLpNorm_sub_lt_of_isSlabProfile
end P2MW
export P2MW.S_AutomorphicForm_exists_continuous_invariant_bandSupported_eLpNorm_sub_lt_of_isSlabProfile (solution)
