-- Prove2me | solution 1 for AutomorphicForm.exists_forall_sum_lintegral_orbital_add_weightedOrbital_le_of_isSemiLocalFactorization_indicator_translate
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/eee538de-e686-51be-b9b6-e0d51a7ec504

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
import Theorems.Thm_AutomorphicForm_sum_lintegral_orbital_add_weightedOrbital_indicator_translate_mul_prod_measure_doubleCoset_le
import Theorems.Thm_AutomorphicForm_exists_forall_sum_lintegral_orbital_add_weightedOrbital_doubleCoset_le_mul_prod_rpow_measure
import Theorems.Thm_AutomorphicForm_exists_isSemiLocalFactorization_indicator_doubleCoset_of_isSemiLocalFactorization_indicator_translate
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_sum_lintegral_orbital_add_weightedOrbital_le_of_isSemiLocalFactorization_indicator_translate
p2m_attr_erase "instance" "AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions LanglandsTunnell.CubicInduction.countable_GL2 LanglandsTunnell.CubicInduction.countable_mirabolicIndex M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO"
p2m_attr_erase "instance" "ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers"
p2m_attr_erase "simp" "NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply LanglandsTunnell.CubicInduction.coe_diagUnits2 LanglandsTunnell.RankinSelberg.mem_primeFibre LanglandsTunnell.CubicInduction.coe_diagUnitGL2 LanglandsTunnell.CubicInduction.iotaTorusLocal_zero LanglandsTunnell.CubicInduction.upperUnipotent3_zero LanglandsTunnell.CubicInduction.radicalP21_coe LanglandsTunnell.CubicInduction.coe_iotaGL LanglandsTunnell.CubicInduction.radicalP12_coe LanglandsTunnell.CubicInduction.radicalP12_zero LanglandsTunnell.CubicInduction.radicalP21_zero LanglandsTunnell.CubicInduction.upperUnipotent3_coe AutomorphicForm.adeleArchAlgHom_apply AutomorphicForm.tensorPlaceHom_tmul AutomorphicForm.tensorArchHom_tmul AutomorphicForm.adelePlaceAlgHom_apply AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.classAct_mk GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.cpowChar_apply_val ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj"
p2m_attr_erase "simp" "JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AutomorphicForm.LocalWeightedOrbital.halfWeighted_zero_fun AutomorphicForm.LocalWeightedOrbital.centralValue_zero_fun AutomorphicForm.LocalWeightedOrbital.normSplitOrbital_zero_fun AutomorphicForm.LocalWeightedOrbital.slice_zero_fun AutomorphicForm.LocalWeightedOrbital.correctionTerm_zero_fun AutomorphicForm.LocalWeightedOrbital.bTerm_zero_fun AutomorphicForm.LocalWeightedOrbital.cTerm_zero_fun AutomorphicForm.LocalWeightedOrbital.invariantPart_zero_fun AutomorphicForm.LocalWeightedOrbital.splitOrbital_zero_fun AutomorphicForm.LocalWeightedOrbital.unipotentMellin_zero_fun IsLocalRing.principalUnits_zero"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.glBorel

set_option synthInstance.maxHeartbeats 1600000

noncomputable section

namespace SingleGlue

open AutomorphicForm
open scoped TensorProduct.RightActions ENNReal

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem one_le_semiLocalHaar_doubleCoset (v : HeightOneSpectrum (𝓞 K)) (a : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    1 ≤ semiLocalHaar K L v (semiLocalIntegralSet K L v * {a} * semiLocalIntegralSet K L v) := by
  letI := glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI := borelSpace_glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI := isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  haveI := isHaarMeasure_semiLocalHaar K L v
  have hsub : a • semiLocalIntegralSet K L v ⊆ semiLocalIntegralSet K L v * {a} * semiLocalIntegralSet K L v := by
    rintro _ ⟨k, hk, rfl⟩
    refine ⟨1 * a, ⟨1, one_mem_semiLocalIntegralSet K L v, a, rfl, rfl⟩, k, hk, ?_⟩
    simp only [smul_eq_mul, one_mul]
  calc (1 : ℝ≥0∞) = semiLocalHaar K L v (semiLocalIntegralSet K L v) :=
        (semiLocalHaar_semiLocalIntegralSet K L v).symm
    _ = semiLocalHaar K L v (a • semiLocalIntegralSet K L v) := (measure_smul _ a _).symm
    _ ≤ _ := measure_mono hsub

theorem semiLocalHaar_doubleCoset_lt_top (v : HeightOneSpectrum (𝓞 K)) (a : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    semiLocalHaar K L v (semiLocalIntegralSet K L v * {a} * semiLocalIntegralSet K L v) < ∞ := by
  letI := glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI := borelSpace_glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI := isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  haveI := isHaarMeasure_semiLocalHaar K L v
  exact (((isCompact_semiLocalIntegralSet K L v).mul isCompact_singleton).mul
    (isCompact_semiLocalIntegralSet K L v)).measure_lt_top

theorem exists_bound_rpow_half_mul_log_pow (A : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, 1 ≤ x →
    x ^ ((1 : ℝ) / 2) * (1 + Real.log x) ^ A ≤ B * x := by
  rcases Nat.eq_zero_or_pos A with rfl | hA
  · refine ⟨1, zero_le_one, fun x hx => ?_⟩
    rw [pow_zero, mul_one, one_mul]
    calc x ^ ((1 : ℝ) / 2) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
      _ = x := Real.rpow_one x
  · refine ⟨(2 * A : ℝ) ^ A, by positivity, fun x hx => ?_⟩
    have hx0 : 0 < x := one_pos.trans_le hx
    have hAr : (1 : ℝ) ≤ A := by exact_mod_cast hA
    have hA0 : (A : ℝ) ≠ 0 := by positivity
    have hApos : (0 : ℝ) < 2 * A := by positivity
    set y : ℝ := x ^ ((1 : ℝ) / (2 * A)) with hy
    have hy0 : 0 < y := Real.rpow_pos_of_pos hx0 _
    have hlogy : Real.log y = Real.log x / (2 * A) := by
      rw [hy, Real.log_rpow hx0]; ring
    have hlog : 1 + Real.log x ≤ 2 * A * y := by
      have h1 := Real.log_le_sub_one_of_pos hy0
      rw [hlogy, div_le_iff₀ hApos] at h1
      nlinarith
    have hlog0 : 0 ≤ 1 + Real.log x := by
      have := Real.log_nonneg hx; linarith
    have hpow : (1 + Real.log x) ^ A ≤ (2 * A : ℝ) ^ A * x ^ ((1 : ℝ) / 2) := by
      calc (1 + Real.log x) ^ A ≤ (2 * A * y) ^ A := pow_le_pow_left₀ hlog0 hlog A
        _ = (2 * A : ℝ) ^ A * y ^ A := mul_pow _ _ _
        _ = (2 * A : ℝ) ^ A * x ^ ((1 : ℝ) / 2) := by
            congr 1
            rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
            congr 1
            field_simp
    calc x ^ ((1 : ℝ) / 2) * (1 + Real.log x) ^ A
        ≤ x ^ ((1 : ℝ) / 2) * ((2 * A : ℝ) ^ A * x ^ ((1 : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hx0.le _)
      _ = (2 * A : ℝ) ^ A * (x ^ ((1 : ℝ) / 2) * x ^ ((1 : ℝ) / 2)) := by ring
      _ = (2 * A : ℝ) ^ A * x := by rw [← Real.rpow_add hx0]; norm_num

theorem le_ofReal_div_of_mul_le {c c' M : ℝ≥0∞} {R : ℝ} (hM0 : M ≠ 0) (hMt : M ≠ ∞)
    (h1 : c * M ≤ c') (h2 : c' ≤ ENNReal.ofReal R) : c ≤ ENNReal.ofReal (R / M.toReal) := by
  have hpos : 0 < M.toReal := ENNReal.toReal_pos hM0 hMt
  rw [ENNReal.ofReal_div_of_pos hpos, ENNReal.ofReal_toReal hMt]
  exact ((ENNReal.le_div_iff_mul_le (Or.inl hM0) (Or.inl hMt)).mpr h1).trans (ENNReal.div_le_div_right h2 M)

theorem prod_bound {α : Type*} (T : Finset α) (m : α → ℝ) (hm : ∀ v ∈ T, 1 ≤ m v) (A : ℕ) (B : ℝ)
    (hB : ∀ x : ℝ, 1 ≤ x → x ^ ((1 : ℝ) / 2) * (1 + Real.log x) ^ A ≤ B * x) (C : ℝ) (hC : 0 ≤ C) :
    C * (∏ v ∈ T, m v ^ ((1 : ℝ) / 2) * (1 + Real.log (m v)) ^ A) / ∏ v ∈ T, m v ≤ C * B ^ T.card := by
  rw [mul_div_assoc, ← Finset.prod_div_distrib, ← Finset.prod_const B]
  refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun v hv => ?_) fun v hv => ?_) hC
  · have h1 : 0 ≤ 1 + Real.log (m v) := by have := Real.log_nonneg (hm v hv); linarith
    exact div_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith [hm v hv]) _) (pow_nonneg h1 _))
      (by linarith [hm v hv])
  · rw [div_le_iff₀ (by linarith [hm v hv])]
    exact hB _ (hm v hv)

end SingleGlue

end

open AutomorphicForm

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
      ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ρ : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L))
        (φ : AdelicGL2 (𝓞 L) L → ℂ)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
        IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))⁻¹ * x)
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
        ENNReal.ofReal C := by
  intro T ws
  obtain ⟨C, hC0, A, hDCB⟩ :=
    AutomorphicForm.exists_forall_sum_lintegral_orbital_add_weightedOrbital_doubleCoset_le_mul_prod_rpow_measure
      K L νZL D σ hgen S φa φS H hHc hH μH Δ hΔd hΔdisj T ws
  obtain ⟨B, hB0, hB⟩ := SingleGlue.exists_bound_rpow_half_mul_log_pow A
  refine ⟨C * B ^ T.card, by positivity, ?_⟩
  intro ρ φ φf hfact Δφ hΔφ
  obtain ⟨φ', φf', hfact'⟩ :=
    AutomorphicForm.exists_isSemiLocalFactorization_indicator_doubleCoset_of_isSemiLocalFactorization_indicator_translate
      K L S φa φS T ws ρ φ φf hfact
  have h1 :=
    AutomorphicForm.sum_lintegral_orbital_add_weightedOrbital_indicator_translate_mul_prod_measure_doubleCoset_le
      K L νZL D σ hgen S φa φS H hHc hH μH Δ hΔd hΔdisj T ws ρ φ φf hfact φ' φf' hfact' Δφ hΔφ
  have h2 := hDCB ρ φ' φf' hfact' Δφ hΔφ
  have hM1 : ∀ v ∈ T, (1 : ENNReal) ≤ AutomorphicForm.semiLocalHaar K L v
      (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                semiLocalIntegralSet K L v) :=
    fun v _ => SingleGlue.one_le_semiLocalHaar_doubleCoset K L v _
  have hMt : ∀ v ∈ T, AutomorphicForm.semiLocalHaar K L v
      (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                semiLocalIntegralSet K L v) ≠ ⊤ :=
    fun v _ => (SingleGlue.semiLocalHaar_doubleCoset_lt_top K L v _).ne
  refine (SingleGlue.le_ofReal_div_of_mul_le ?_ ?_ h1 h2).trans (ENNReal.ofReal_le_ofReal ?_)
  · exact (zero_lt_one.trans_le (Finset.one_le_prod' hM1)).ne'
  · exact ENNReal.prod_ne_top hMt
  · rw [ENNReal.toReal_prod]
    refine SingleGlue.prod_bound T (fun v => (AutomorphicForm.semiLocalHaar K L v
      (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                semiLocalIntegralSet K L v)).toReal) (fun v hv => ?_) A B hB C hC0
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono (hMt v hv) (hM1 v hv)

end S_AutomorphicForm_exists_forall_sum_lintegral_orbital_add_weightedOrbital_le_of_isSemiLocalFactorization_indicator_translate
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_sum_lintegral_orbital_add_weightedOrbital_le_of_isSemiLocalFactorization_indicator_translate (solution)
