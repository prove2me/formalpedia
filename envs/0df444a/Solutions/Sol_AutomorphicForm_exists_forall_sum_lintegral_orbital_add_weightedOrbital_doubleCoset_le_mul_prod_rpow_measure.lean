-- Prove2me | solution 1 for AutomorphicForm.exists_forall_sum_lintegral_orbital_add_weightedOrbital_doubleCoset_le_mul_prod_rpow_measure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/94115cf4-d1d1-51eb-a132-4fe5f7e5d3e3

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Theorems.Thm_AutomorphicForm_exists_forall_lintegral_orbital_doubleCoset_le_mul_prod_rpow_measure
import Theorems.Thm_AutomorphicForm_exists_forall_card_le_mul_prod_pow_log_measure_of_lintegral_orbital_doubleCoset_ne_zero
import Theorems.Thm_AutomorphicForm_exists_forall_lintegral_weightedOrbital_doubleCoset_le_mul_prod_pow_log_measure_mul_lintegral_orbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_sum_lintegral_orbital_add_weightedOrbital_doubleCoset_le_mul_prod_rpow_measure
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions LanglandsTunnell.CubicInduction.countable_GL2 LanglandsTunnell.CubicInduction.countable_mirabolicIndex RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO"
p2m_attr_erase "instance" "ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.coe_diagUnits2 LanglandsTunnell.RankinSelberg.mem_primeFibre LanglandsTunnell.CubicInduction.coe_diagUnitGL2 LanglandsTunnell.CubicInduction.iotaTorusLocal_zero LanglandsTunnell.CubicInduction.upperUnipotent3_zero LanglandsTunnell.CubicInduction.radicalP21_coe LanglandsTunnell.CubicInduction.coe_iotaGL LanglandsTunnell.CubicInduction.radicalP12_coe LanglandsTunnell.CubicInduction.radicalP12_zero LanglandsTunnell.CubicInduction.radicalP21_zero LanglandsTunnell.CubicInduction.upperUnipotent3_coe AutomorphicForm.adeleArchAlgHom_apply AutomorphicForm.tensorPlaceHom_tmul AutomorphicForm.tensorArchHom_tmul AutomorphicForm.adelePlaceAlgHom_apply AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.classAct_mk GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.cpowChar_apply_val ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj"
p2m_attr_erase "simp" "JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AutomorphicForm.LocalWeightedOrbital.halfWeighted_zero_fun AutomorphicForm.LocalWeightedOrbital.centralValue_zero_fun AutomorphicForm.LocalWeightedOrbital.normSplitOrbital_zero_fun AutomorphicForm.LocalWeightedOrbital.slice_zero_fun AutomorphicForm.LocalWeightedOrbital.correctionTerm_zero_fun AutomorphicForm.LocalWeightedOrbital.bTerm_zero_fun AutomorphicForm.LocalWeightedOrbital.cTerm_zero_fun AutomorphicForm.LocalWeightedOrbital.invariantPart_zero_fun AutomorphicForm.LocalWeightedOrbital.splitOrbital_zero_fun AutomorphicForm.LocalWeightedOrbital.unipotentMellin_zero_fun IsLocalRing.principalUnits_zero"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace AutomorphicForm p2m_export "AutomorphicForm" "isTopologicalGroup_tensorGL t2Space_tensorGL locallyCompactSpace_tensorGL glBorelOf borelSpace_glBorelOf semiLocalIntegralSet one_mem_semiLocalIntegralSet isCompact_semiLocalIntegralSet semiLocalHaar isHaarMeasure_semiLocalHaar semiLocalHaar_semiLocalIntegralSet semiLocalComponent IsSemiLocalFactorization AdelicGL2 globalPoints centralScalar sigmaAdelicAct adelicWeyl exists_forall_lintegral_orbital_doubleCoset_le_mul_prod_rpow_measure exists_forall_card_le_mul_prod_pow_log_measure_of_lintegral_orbital_doubleCoset_ne_zero exists_forall_lintegral_weightedOrbital_doubleCoset_le_mul_prod_pow_log_measure_mul_lintegral_orbital" namespace DoubleCosetAssembly end AutomorphicForm.DoubleCosetAssembly
p2m_open_scoped "AutomorphicForm" in
open scoped ENNReal in

theorem AutomorphicForm.DoubleCosetAssembly.sum_add_le {ι κ : Type} (T : Finset κ) (Δφ : Finset ι)
    (U W : ι → ℝ≥0∞) (m : κ → ℝ) (hm : ∀ v ∈ T, 1 ≤ m v)
    (C₁ C₂ C₃ : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃) (A₁ A₂ A₃ : ℕ)
    (h₁ : ∀ t ∈ Δφ, U t ≤ ENNReal.ofReal (C₁ * ∏ v ∈ T, (m v ^ ((1 : ℝ) / 2) * (1 + Real.log (m v)) ^ A₁)))
    (h₂ : ∀ Δ' : Finset ι, Δ' ⊆ Δφ → (∀ t ∈ Δ', U t ≠ 0) →
      (Δ'.card : ℝ) ≤ C₂ * ∏ v ∈ T, (1 + Real.log (m v)) ^ A₂)
    (h₃ : ∀ t ∈ Δφ, W t ≤ ENNReal.ofReal (C₃ * ∏ v ∈ T, (1 + Real.log (m v)) ^ A₃) * U t) :
    ∑ t ∈ Δφ, (U t + W t) ≤
      ENNReal.ofReal (C₁ * C₂ * (1 + C₃) *
        ∏ v ∈ T, (m v ^ ((1 : ℝ) / 2) * (1 + Real.log (m v)) ^ (A₁ + A₂ + A₃))) := by
  classical
  set P₁ : ℝ := ∏ v ∈ T, (m v ^ ((1 : ℝ) / 2) * (1 + Real.log (m v)) ^ A₁) with hP₁
  set P₂ : ℝ := ∏ v ∈ T, (1 + Real.log (m v)) ^ A₂ with hP₂
  set P₃ : ℝ := ∏ v ∈ T, (1 + Real.log (m v)) ^ A₃ with hP₃
  have hℓ : ∀ v ∈ T, 1 ≤ 1 + Real.log (m v) := fun v hv => by
    have := Real.log_nonneg (hm v hv); linarith
  have hP₁nn : 0 ≤ P₁ := Finset.prod_nonneg fun v hv =>
    mul_nonneg (Real.rpow_nonneg (by linarith [hm v hv]) _) (pow_nonneg (by linarith [hℓ v hv]) _)
  have hP₂one : 1 ≤ P₂ := by
    calc (1 : ℝ) = ∏ v ∈ T, (1 : ℝ) := by simp
      _ ≤ P₂ := Finset.prod_le_prod (fun _ _ => zero_le_one) fun v hv => one_le_pow₀ (hℓ v hv)
  have hP₃one : 1 ≤ P₃ := by
    calc (1 : ℝ) = ∏ v ∈ T, (1 : ℝ) := by simp
      _ ≤ P₃ := Finset.prod_le_prod (fun _ _ => zero_le_one) fun v hv => one_le_pow₀ (hℓ v hv)
  have hP₂nn : 0 ≤ P₂ := zero_le_one.trans hP₂one
  have hP₃nn : 0 ≤ P₃ := zero_le_one.trans hP₃one

  set Δ' : Finset ι := Δφ.filter fun t => U t ≠ 0 with hΔ'
  have hΔ'sub : Δ' ⊆ Δφ := Finset.filter_subset _ _
  have hsum : ∑ t ∈ Δφ, (U t + W t) = ∑ t ∈ Δ', (U t + W t) := by
    refine (Finset.sum_subset hΔ'sub fun t ht hnot => ?_).symm
    have hU : U t = 0 := by
      by_contra h; exact hnot (Finset.mem_filter.2 ⟨ht, h⟩)
    have hW : W t = 0 := by
      have := h₃ t ht; rw [hU, mul_zero] at this; exact le_antisymm this bot_le |>.symm ▸ rfl
    rw [hU, hW, add_zero]

  have hterm : ∀ t ∈ Δ', U t + W t ≤ (1 + ENNReal.ofReal (C₃ * P₃)) * ENNReal.ofReal (C₁ * P₁) := by
    intro t ht
    have ht' : t ∈ Δφ := hΔ'sub ht
    calc U t + W t ≤ U t + ENNReal.ofReal (C₃ * P₃) * U t := add_le_add le_rfl (h₃ t ht')
      _ = (1 + ENNReal.ofReal (C₃ * P₃)) * U t := by ring
      _ ≤ (1 + ENNReal.ofReal (C₃ * P₃)) * ENNReal.ofReal (C₁ * P₁) := mul_le_mul_right (h₁ t ht') _
  have hcard : (Δ'.card : ℝ≥0∞) ≤ ENNReal.ofReal (C₂ * P₂) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (h₂ Δ' hΔ'sub fun t ht => (Finset.mem_filter.1 ht).2)
  calc ∑ t ∈ Δφ, (U t + W t) = ∑ t ∈ Δ', (U t + W t) := hsum
    _ ≤ Δ'.card • ((1 + ENNReal.ofReal (C₃ * P₃)) * ENNReal.ofReal (C₁ * P₁)) :=
        Finset.sum_le_card_nsmul _ _ _ hterm
    _ = (Δ'.card : ℝ≥0∞) * ((1 + ENNReal.ofReal (C₃ * P₃)) * ENNReal.ofReal (C₁ * P₁)) := by
        rw [nsmul_eq_mul]
    _ ≤ ENNReal.ofReal (C₂ * P₂) * ((1 + ENNReal.ofReal (C₃ * P₃)) * ENNReal.ofReal (C₁ * P₁)) :=
        mul_le_mul_left hcard _
    _ = ENNReal.ofReal (C₂ * P₂ * ((1 + C₃ * P₃) * (C₁ * P₁))) := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (mul_nonneg hC₃ hP₃nn),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (C₁ * C₂ * (1 + C₃) *
          ∏ v ∈ T, (m v ^ ((1 : ℝ) / 2) * (1 + Real.log (m v)) ^ (A₁ + A₂ + A₃))) := by
        apply ENNReal.ofReal_le_ofReal
        have hsplit : ∏ v ∈ T, (m v ^ ((1 : ℝ) / 2) * (1 + Real.log (m v)) ^ (A₁ + A₂ + A₃)) =
            P₁ * P₂ * P₃ := by
          rw [hP₁, hP₂, hP₃, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun v _ => ?_
          rw [pow_add, pow_add]; ring
        rw [hsplit]
        have h13 : 1 + C₃ * P₃ ≤ (1 + C₃) * P₃ := by nlinarith
        calc C₂ * P₂ * ((1 + C₃ * P₃) * (C₁ * P₁)) = (C₁ * C₂) * (1 + C₃ * P₃) * (P₁ * P₂) := by ring
          _ ≤ (C₁ * C₂) * ((1 + C₃) * P₃) * (P₁ * P₂) := by
              apply mul_le_mul_of_nonneg_right _ (mul_nonneg hP₁nn hP₂nn)
              exact mul_le_mul_of_nonneg_left h13 (mul_nonneg hC₁ hC₂)
          _ = C₁ * C₂ * (1 + C₃) * (P₁ * P₂ * P₃) := by ring

p2m_open_scoped "AutomorphicForm" in
open scoped ENNReal TensorProduct.RightActions in

theorem AutomorphicForm.DoubleCosetAssembly.one_le_toReal_semiLocalHaar_doubleCoset
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (a : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    1 ≤ (AutomorphicForm.semiLocalHaar K L v
      (semiLocalIntegralSet K L v * {a} * semiLocalIntegralSet K L v)).toReal := by
  letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :=
    AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI := AutomorphicForm.borelSpace_glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  haveI := AutomorphicForm.t2Space_tensorGL K L (v.adicCompletion K)
  haveI := AutomorphicForm.locallyCompactSpace_tensorGL K L (v.adicCompletion K)
  haveI := AutomorphicForm.isHaarMeasure_semiLocalHaar K L v
  haveI : ContinuousMul (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := IsTopologicalGroup.toContinuousMul
  haveI : MeasurableMul (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := ContinuousMul.measurableMul
  have hK := AutomorphicForm.isCompact_semiLocalIntegralSet K L v
  have hfin : AutomorphicForm.semiLocalHaar K L v
      (semiLocalIntegralSet K L v * {a} * semiLocalIntegralSet K L v) ≠ ⊤ :=
    ((hK.mul isCompact_singleton).mul hK).measure_lt_top.ne
  have hsub : (fun h => a⁻¹ * h) ⁻¹' semiLocalIntegralSet K L v ⊆
      semiLocalIntegralSet K L v * {a} * semiLocalIntegralSet K L v := by
    intro x hx
    refine ⟨1 * a, Set.mul_mem_mul (AutomorphicForm.one_mem_semiLocalIntegralSet K L v) rfl, a⁻¹ * x, hx, ?_⟩
    simp
  have hone : AutomorphicForm.semiLocalHaar K L v ((fun h => a⁻¹ * h) ⁻¹' semiLocalIntegralSet K L v) = 1 := by
    rw [MeasureTheory.measure_preimage_mul, AutomorphicForm.semiLocalHaar_semiLocalIntegralSet]
  have hle : (1 : ℝ≥0∞) ≤ AutomorphicForm.semiLocalHaar K L v
      (semiLocalIntegralSet K L v * {a} * semiLocalIntegralSet K L v) :=
    hone ▸ MeasureTheory.measure_mono hsub
  simpa using ENNReal.toReal_mono hfin hle

open _root_.AutomorphicForm _root_.P2MW.S_AutomorphicForm_exists_forall_sum_lintegral_orbital_add_weightedOrbital_doubleCoset_le_mul_prod_rpow_measure.AutomorphicForm in
open scoped TensorProduct.RightActions in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)

    (H : Subgroup (AdelicGL2 (𝓞 L) L)) (hHc : IsClosed (H : Set (AdelicGL2 (𝓞 L) L)))
    (hH : ∀ h : AdelicGL2 (𝓞 L) L, h ∈ H ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 ∧
       (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0 ∧
       AutomorphicForm.sigmaAdelicAct K L D σ h * h⁻¹ ∈ Subgroup.center (AdelicGL2 (𝓞 L) L)))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]

    (Δ : Set (GL (Fin 2) L))
    (hΔd : ∀ t ∈ Δ, (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 ∧
      Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (hΔdisj : ∀ t ∈ Δ, ∀ t' ∈ Δ, t ≠ t' →
      Disjoint {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}
        {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          t'⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}) :
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))) (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L)),
      ∃ C : ℝ, 0 ≤ C ∧ ∃ A : ℕ,
      ∀ (ρ : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L))
        (φ : AdelicGL2 (𝓞 L) L → ℂ)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
        IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                  semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ)) x
            else φS v) →
      ∀ (Δφ : Finset (GL (Fin 2) L)), (↑Δφ ⊆ Δ) →
        (∑ t ∈ Δφ,
          ((∫⁻ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
              (∫⁻ z, ENNReal.ofReal ‖φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L))))‖ ∂νZL)
              ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH)) +
           (∫⁻ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
              ENNReal.ofReal |(-Real.log (NumberField.AdelicHeight.adelicHeight L (q.out : AdelicGL2 (𝓞 L) L))
                - Real.log (NumberField.AdelicHeight.adelicHeight L
                    (AutomorphicForm.adelicWeyl (𝓞 L) L * (q.out : AdelicGL2 (𝓞 L) L))))| *
              (∫⁻ z, ENNReal.ofReal ‖φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L))))‖ ∂νZL)
              ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH)))) ≤
        ENNReal.ofReal (C * ∏ v ∈ T,
          ((AutomorphicForm.semiLocalHaar K L v
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                semiLocalIntegralSet K L v)).toReal ^ ((1 : ℝ) / 2) *
            (1 + Real.log (AutomorphicForm.semiLocalHaar K L v
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                semiLocalIntegralSet K L v)).toReal) ^ A)) := by
  intro T ws
  obtain ⟨C₁, hC₁, A₁, h₁⟩ :=
    AutomorphicForm.exists_forall_lintegral_orbital_doubleCoset_le_mul_prod_rpow_measure K L νZL D σ hgen S φa φS
      H hHc hH μH T ws
  obtain ⟨C₂, hC₂, A₂, h₂⟩ :=
    AutomorphicForm.exists_forall_card_le_mul_prod_pow_log_measure_of_lintegral_orbital_doubleCoset_ne_zero K L νZL D
      σ hgen S φa φS H hHc hH μH Δ hΔd hΔdisj T ws
  obtain ⟨C₃, hC₃, A₃, h₃⟩ :=
    AutomorphicForm.exists_forall_lintegral_weightedOrbital_doubleCoset_le_mul_prod_pow_log_measure_mul_lintegral_orbital
      K L νZL D σ hgen S φa φS H hHc hH μH T ws
  refine ⟨C₁ * C₂ * (1 + C₃), by positivity, A₁ + A₂ + A₃, ?_⟩
  intro ρ φ φf hφ Δφ hΔφ
  have hmem : ∀ t ∈ Δφ, t ∈ Δ := fun t ht => hΔφ (Finset.mem_coe.mpr ht)
  exact AutomorphicForm.DoubleCosetAssembly.sum_add_le T Δφ _ _ _
    (fun v _ => AutomorphicForm.DoubleCosetAssembly.one_le_toReal_semiLocalHaar_doubleCoset K L v _)
    C₁ C₂ C₃ hC₁ hC₂ hC₃ A₁ A₂ A₃
    (fun t ht => h₁ ρ φ φf hφ t (hΔd t (hmem t ht)).1 (hΔd t (hmem t ht)).2.1 (hΔd t (hmem t ht)).2.2)
    (fun Δ' hΔ' hne => h₂ ρ φ φf hφ Δ' ((Finset.coe_subset.mpr hΔ').trans hΔφ) hne)
    (fun t ht => h₃ ρ φ φf hφ t (hΔd t (hmem t ht)).1 (hΔd t (hmem t ht)).2.1 (hΔd t (hmem t ht)).2.2)

end S_AutomorphicForm_exists_forall_sum_lintegral_orbital_add_weightedOrbital_doubleCoset_le_mul_prod_rpow_measure
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_sum_lintegral_orbital_add_weightedOrbital_doubleCoset_le_mul_prod_rpow_measure (solution)
