-- Prove2me | solution 1 for AutomorphicForm.forall_exists_integral_lambdaT_twistedAdelicKernel_eq_finsum_centralElliptic_add_and_norm_le_unram
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/8ba5e699-7e65-5376-9653-be5d9776ec59

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
import Theorems.Thm_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq
import Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_AutomorphicForm_forall_exists_lambdaT_twistedAdelicKernel_eq_finsum_add_sub_indicator_constantTerm_add
import Theorems.Thm_AutomorphicForm_integrableOn_setIntegral_mul_finsum_centralElliptic_twistedAdelicKernel
import Theorems.Thm_AutomorphicForm_forall_exists_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_affine_unram
import Theorems.Thm_AutomorphicForm_forall_exists_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_affine_bound
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_forall_exists_integral_lambdaT_twistedAdelicKernel_eq_finsum_centralElliptic_add_and_norm_le_unram
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions instCountableHeightOneSpectrumRingOfIntegers_definitions instCountableHeightOneSpectrumRingOfIntegersRat_definitions FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup LanglandsTunnell.CubicInduction.countable_GL2 LanglandsTunnell.CubicInduction.countable_mirabolicIndex ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal"
p2m_attr_erase "instance" "ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent FLT.HaarFiniteOrderGates.negContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.doublingContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.invContinuousMulEquiv_apply ContinuousAddEquiv.preimage_mulLeft_smul AutomorphicForm.cpowChar_apply_val AutomorphicForm.adeleArchAlgHom_apply AutomorphicForm.tensorPlaceHom_tmul AutomorphicForm.tensorArchHom_tmul AutomorphicForm.adelePlaceAlgHom_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec AutomorphicForm.gl2Weyl_val M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk GroupCohomology.RepPi.proj_hom_apply"
p2m_attr_erase "simp" "GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk LanglandsTunnell.CubicInduction.coe_diagUnits2 LanglandsTunnell.RankinSelberg.mem_primeFibre LanglandsTunnell.CubicInduction.coe_diagUnitGL2 LanglandsTunnell.CubicInduction.iotaTorusLocal_zero LanglandsTunnell.CubicInduction.upperUnipotent3_zero LanglandsTunnell.CubicInduction.radicalP21_coe LanglandsTunnell.CubicInduction.coe_iotaGL LanglandsTunnell.CubicInduction.radicalP12_coe LanglandsTunnell.CubicInduction.radicalP12_zero LanglandsTunnell.CubicInduction.radicalP21_zero LanglandsTunnell.CubicInduction.upperUnipotent3_coe ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet"
p2m_attr_erase "simp" "ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AutomorphicForm.LocalWeightedOrbital.halfWeighted_zero_fun AutomorphicForm.LocalWeightedOrbital.centralValue_zero_fun AutomorphicForm.LocalWeightedOrbital.normSplitOrbital_zero_fun AutomorphicForm.LocalWeightedOrbital.slice_zero_fun AutomorphicForm.LocalWeightedOrbital.correctionTerm_zero_fun AutomorphicForm.LocalWeightedOrbital.bTerm_zero_fun AutomorphicForm.LocalWeightedOrbital.cTerm_zero_fun AutomorphicForm.LocalWeightedOrbital.invariantPart_zero_fun AutomorphicForm.LocalWeightedOrbital.splitOrbital_zero_fun AutomorphicForm.LocalWeightedOrbital.unipotentMellin_zero_fun IsLocalRing.principalUnits_zero"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open NumberField.TateGlobal AutomorphicForm Function in
open scoped NNReal ENNReal in

private theorem DetNormLevelSet.adelicGLHaar_setOf_ideleNorm_det_mem_Icc_eq_zero_of_not_lt
    (L : Type) [Field L] [NumberField L] (α β : ℝ) (hα : 0 < α) (hαβ : ¬ α < β) :
    NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 L) L
      {g : AdelicGL2 (𝓞 L) L | ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} = 0 := by
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 L) L
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L
  haveI := NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo L
  rcases (not_lt.mp hαβ).lt_or_eq with hlt | hba
  · have he : {g : AdelicGL2 (𝓞 L) L | ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} = ∅ := by
      ext g
      simp only [Set.mem_setOf_eq, Set.Icc_eq_empty (not_le.mpr hlt), Set.mem_empty_iff_false]
    rw [he, measure_empty]
  · rw [hba]
    set μ := NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 L) L with hμ

    set S : ℝ → Set (AdelicGL2 (𝓞 L) L) :=
      fun t => {g : AdelicGL2 (𝓞 L) L | ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc t t} with hS
    have hSm : ∀ t : ℝ, MeasurableSet (S t) := fun t => measurableSet_setOf_ideleNorm_det_mem_Icc L t t
    have hSd : Pairwise (Disjoint on S) := by
      intro t t' htt'
      refine Set.disjoint_left.mpr fun g hg hg' => htt' ?_
      simp only [hS, Set.mem_setOf_eq, Set.mem_Icc] at hg hg'
      exact le_antisymm (hg.1.trans hg'.2) (hg'.1.trans hg.2)
    have hcount : Set.Countable {t : ℝ | 0 < μ (S t)} := Measure.countable_meas_pos_of_disjoint_iUnion hSm hSd

    obtain ⟨s, -, hs, -⟩ := exists_continuous_monoidHom_ideleNorm_apply_eq L
    have heqm : ∀ t : ℝ, 0 < t → μ (S t) = μ (S α) := by
      intro t ht
      have hq : 0 < t / α := div_pos ht hα
      have hq0 : (⟨Real.sqrt (t / α), Real.sqrt_nonneg _⟩ : ℝ≥0) ≠ 0 := by
        intro h
        have h' : Real.sqrt (t / α) = 0 := congrArg (fun x : ℝ≥0 => (x : ℝ)) h
        rw [Real.sqrt_eq_zero'] at h'
        exact absurd h' (not_le.mpr hq)
      set r : ℝ≥0ˣ := Units.mk0 _ hq0 with hr
      have hr2 : ((r : ℝ≥0) : ℝ) ^ 2 * α = t := by
        show (Real.sqrt (t / α)) ^ 2 * α = t
        rw [Real.sq_sqrt hq.le, div_mul_cancel₀ t hα.ne']
      have hrne : ((r : ℝ≥0) : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (NNReal.coe_ne_zero.mpr r.ne_zero)
      have hdet : Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L (s r)) = (s r) ^ 2 := by
        show Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) (s r)) = _
        rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]
      have hN : ∀ h : AdelicGL2 (𝓞 L) L,
          ideleNorm L (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L (s r) * h)) =
            ((r : ℝ≥0) : ℝ) ^ 2 * ideleNorm L (Matrix.GeneralLinearGroup.det h) := by
        intro h
        rw [map_mul, hdet, pow_two, ideleNorm_mul, ideleNorm_mul, hs r, pow_two]
      have hpre : S α = (fun h => centralScalar (𝓞 L) L (s r) * h) ⁻¹' (S t) := by
        ext h
        simp only [hS, Set.mem_preimage, Set.mem_setOf_eq, Set.Icc_self, Set.mem_singleton_iff, hN, ← hr2]
        constructor
        · intro h1
          rw [h1]
        · intro h1
          exact mul_left_cancel₀ hrne h1
      have := measure_preimage_mul μ (centralScalar (𝓞 L) L (s r)) (S t)
      rw [← hpre] at this
      exact this.symm

    change μ (S α) = 0
    by_contra hne
    have hpos : 0 < μ (S α) := pos_iff_ne_zero.mpr hne
    have hsub : Set.Ioi (0 : ℝ) ⊆ {t : ℝ | 0 < μ (S t)} := by
      intro t ht
      show 0 < μ (S t)
      rw [heqm t ht]
      exact hpos
    have h0 : volume (Set.Ioi (0 : ℝ)) = 0 := (hcount.mono hsub).measure_zero volume
    rw [Real.volume_Ioi] at h0
    exact ENNReal.top_ne_zero h0

private theorem GeomSideAssembly.integral_eq_of_splitting {Xx : Type*} [MeasurableSpace Xx] (μx : Measure Xx)
    {Zz : Type*} [MeasurableSpace Zz] (μz : Measure Zz) (Φ₀ ΦL : Set Xx) (Ω : Set Zz) (ξ : Zz → ℂ)
    (Λ Kce uR hR : Xx → Zz → ℂ) (CEv R a b c d : ℂ)
    (hpt : ∀ x z, Λ x z = Kce x z + uR x z + hR x z)
    (htrans : (∫ x in Φ₀, (∫ z in Ω, ξ z * Kce x z ∂μz) ∂μx) =
      ∫ x in ΦL, (∫ z in Ω, ξ z * Kce x z ∂μz) ∂μx)
    (hCE : (∫ x in ΦL, (∫ z in Ω, ξ z * Kce x z ∂μz) ∂μx) = CEv)
    (hEin : ∀ x, IntegrableOn (fun z => ξ z * Kce x z) Ω μz)
    (hEout : IntegrableOn (fun x => ∫ z in Ω, ξ z * Kce x z ∂μz) Φ₀ μx)
    (hUin : ∀ x, IntegrableOn (fun z => ξ z * uR x z) Ω μz)
    (hUout : IntegrableOn (fun x => ∫ z in Ω, ξ z * uR x z ∂μz) Φ₀ μx)
    (hUeq : (∫ x in Φ₀, (∫ z in Ω, ξ z * uR x z ∂μz) ∂μx) = R * a + c)
    (hHin : ∀ x, IntegrableOn (fun z => ξ z * hR x z) Ω μz)
    (hHout : IntegrableOn (fun x => ∫ z in Ω, ξ z * hR x z ∂μz) Φ₀ μx)
    (hHeq : (∫ x in Φ₀, (∫ z in Ω, ξ z * hR x z ∂μz) ∂μx) = R * b + d) :
    (∫ x in Φ₀, (∫ z in Ω, ξ z * Λ x z ∂μz) ∂μx) = CEv + (R * (a + b) + (c + d)) := by
  have h1 : (fun x => ∫ z in Ω, ξ z * Λ x z ∂μz) =
      fun x => ((∫ z in Ω, ξ z * Kce x z ∂μz) + ∫ z in Ω, ξ z * uR x z ∂μz) +
        ∫ z in Ω, ξ z * hR x z ∂μz := by
    funext x
    have h2 : (fun z => ξ z * Λ x z) = fun z => (ξ z * Kce x z + ξ z * uR x z) + ξ z * hR x z := by
      funext z
      rw [hpt x z]
      ring
    have i1 : Integrable (fun z => ξ z * Kce x z + ξ z * uR x z) (μz.restrict Ω) :=
      (hEin x).add (hUin x)
    rw [h2, integral_add i1 (hHin x), integral_add (hEin x) (hUin x)]
  have o1 : Integrable (fun x => (∫ z in Ω, ξ z * Kce x z ∂μz) + ∫ z in Ω, ξ z * uR x z ∂μz)
      (μx.restrict Φ₀) := hEout.add hUout
  rw [h1, integral_add o1 hHout, integral_add hEout hUout, htrans, hCE, hUeq, hHeq]
  ring

open AutomorphicForm in
open scoped TensorProduct.RightActions in
private noncomputable def GeomSideAssembly.box (L : Type) [Field L] [NumberField L]
    (SL : Finset (HeightOneSpectrum (𝓞 L))) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) :
    Set (HeightOneSpectrum (𝓞 L) → ℂ × ℂ) :=
  {x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ |
        (∀ w ∈ SL, x w = 0) ∧
        ∀ w ∉ SL,
          (x w).2 = HeckeEigensystem.cNorm w *
              ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ∧
          ‖(x w).1‖ ≤ ((Ideal.absNorm w.asIdeal : ℝ) + 1) *
              Real.sqrt ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ :
                ℂˣ) : ℂ)‖ ∧
          conj (x w).1 = conj (x w).2 / ((‖(x w).2‖ : ℝ) : ℂ) * (x w).1}

open AutomorphicForm in
private noncomputable abbrev GeomSideAssembly.boxPin (L : Type) [Field L] [NumberField L]
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) (w : HeightOneSpectrum (𝓞 L)) : ℂ :=
  HeckeEigensystem.cNorm w *
    ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ : ℂˣ) : ℂ)

private noncomputable abbrev GeomSideAssembly.boxRad (L : Type) [Field L] [NumberField L]
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) (w : HeightOneSpectrum (𝓞 L)) : ℝ :=
  ((Ideal.absNorm w.asIdeal : ℝ) + 1) *
    Real.sqrt ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ : ℂˣ) : ℂ)‖

open Classical in
private noncomputable def GeomSideAssembly.boxClosedFactor (L : Type) [Field L] [NumberField L]
    (SL : Finset (HeightOneSpectrum (𝓞 L))) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (w : HeightOneSpectrum (𝓞 L)) : Set (HeightOneSpectrum (𝓞 L) → ℂ × ℂ) :=
  if w ∈ SL then {x | x w = 0} else
    ({x | (x w).2 = GeomSideAssembly.boxPin L ξL w} ∩ {x | ‖(x w).1‖ ≤ GeomSideAssembly.boxRad L ξL w}) ∩
      {x | conj (x w).1 =
        conj (GeomSideAssembly.boxPin L ξL w) / ((‖GeomSideAssembly.boxPin L ξL w‖ : ℝ) : ℂ) * (x w).1}

private theorem GeomSideAssembly.isClosed_boxClosedFactor (L : Type) [Field L] [NumberField L]
    (SL : Finset (HeightOneSpectrum (𝓞 L))) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (w : HeightOneSpectrum (𝓞 L)) : IsClosed (GeomSideAssembly.boxClosedFactor L SL ξL w) := by
  unfold GeomSideAssembly.boxClosedFactor
  split_ifs
  · exact isClosed_eq (continuous_apply w) continuous_const
  · exact ((isClosed_eq (continuous_apply w).snd continuous_const).inter
      (isClosed_le (continuous_apply w).fst.norm continuous_const)).inter
      (isClosed_eq (Complex.continuous_conj.comp (continuous_apply w).fst)
        (continuous_const.mul (continuous_apply w).fst))

open Classical in
private noncomputable def GeomSideAssembly.boxCompactFactor (L : Type) [Field L] [NumberField L]
    (SL : Finset (HeightOneSpectrum (𝓞 L))) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (w : HeightOneSpectrum (𝓞 L)) : Set (ℂ × ℂ) :=
  if w ∈ SL then {0} else
    Metric.closedBall (0 : ℂ) (GeomSideAssembly.boxRad L ξL w) ×ˢ {GeomSideAssembly.boxPin L ξL w}

private theorem GeomSideAssembly.isCompact_boxCompactFactor (L : Type) [Field L] [NumberField L]
    (SL : Finset (HeightOneSpectrum (𝓞 L))) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (w : HeightOneSpectrum (𝓞 L)) : IsCompact (GeomSideAssembly.boxCompactFactor L SL ξL w) := by
  unfold GeomSideAssembly.boxCompactFactor
  split_ifs
  · exact isCompact_singleton
  · exact (isCompact_closedBall _ _).prod isCompact_singleton

private theorem GeomSideAssembly.isCompact_box (L : Type) [Field L] [NumberField L]
    (SL : Finset (HeightOneSpectrum (𝓞 L))) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) :
    IsCompact (GeomSideAssembly.box L SL ξL) := by
  have hbox : GeomSideAssembly.box L SL ξL = ⋂ w, GeomSideAssembly.boxClosedFactor L SL ξL w := by
    ext x
    simp only [GeomSideAssembly.box, Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · rintro ⟨h0, h1⟩ w
      by_cases hw : w ∈ SL
      · simp only [GeomSideAssembly.boxClosedFactor, if_pos hw, Set.mem_setOf_eq]
        exact h0 w hw
      · simp only [GeomSideAssembly.boxClosedFactor, if_neg hw, Set.mem_inter_iff, Set.mem_setOf_eq]
        obtain ⟨h2, hb, hc⟩ := h1 w hw
        rw [h2] at hc
        exact ⟨⟨h2, hb⟩, hc⟩
    · intro h
      refine ⟨fun w hw => ?_, fun w hw => ?_⟩
      · have hw' := h w
        simp only [GeomSideAssembly.boxClosedFactor, if_pos hw, Set.mem_setOf_eq] at hw'
        exact hw'
      · have hw' := h w
        simp only [GeomSideAssembly.boxClosedFactor, if_neg hw, Set.mem_inter_iff, Set.mem_setOf_eq] at hw'
        obtain ⟨⟨h2, hb⟩, hc⟩ := hw'
        refine ⟨h2, hb, ?_⟩
        rw [h2]
        exact hc
  have hsub : GeomSideAssembly.box L SL ξL ⊆ Set.pi Set.univ (GeomSideAssembly.boxCompactFactor L SL ξL) := by
    intro x hx
    simp only [GeomSideAssembly.box, Set.mem_setOf_eq] at hx
    obtain ⟨h0, h1⟩ := hx
    rw [Set.mem_univ_pi]
    intro w
    by_cases hw : w ∈ SL
    · simp only [GeomSideAssembly.boxCompactFactor, if_pos hw, Set.mem_singleton_iff]
      exact h0 w hw
    · simp only [GeomSideAssembly.boxCompactFactor, if_neg hw, Set.mem_prod, Set.mem_singleton_iff,
        mem_closedBall_zero_iff]
      obtain ⟨h2, hb, -⟩ := h1 w hw
      exact ⟨hb, h2⟩
  refine (isCompact_univ_pi fun w => GeomSideAssembly.isCompact_boxCompactFactor L SL ξL w).of_isClosed_subset ?_ hsub
  rw [hbox]
  exact isClosed_iInter fun w => GeomSideAssembly.isClosed_boxClosedFactor L SL ξL w

private def GeomSideAssembly.wordSymbol {ι κ : Type*} (X : Set (κ → ℂ × ℂ)) (T : Finset ι)
    (w' : ι → κ) (c : ι → ℂ) (ks js : ι → ℕ) : C(X, ℂ) where
  toFun x := ∏ v ∈ T,
    ((x : κ → ℂ × ℂ) (w' v)).1 ^ ks v *
      (c v *
        ((x : κ → ℂ × ℂ) (w' v)).2) ^ js v
  continuous_toFun := by
    refine continuous_finsetProd T fun v _ => ?_
    have h : Continuous fun x : X => (x : κ → ℂ × ℂ) (w' v) :=
      (continuous_apply (w' v)).comp continuous_subtype_val
    have h2 : Continuous fun x : X => c v * ((x : κ → ℂ × ℂ) (w' v)).2 := continuous_const.mul h.snd
    exact (h.fst.pow _).mul (h2.pow _)

private theorem GeomSideAssembly.wordSymbol_apply {ι κ : Type*} (X : Set (κ → ℂ × ℂ)) (T : Finset ι)
    (w' : ι → κ) (c : ι → ℂ) (ks js : ι → ℕ) (x : X) :
    GeomSideAssembly.wordSymbol X T w' c ks js x = ∏ v ∈ T,
      ((x : κ → ℂ × ℂ) (w' v)).1 ^ ks v *
        (c v *
          ((x : κ → ℂ × ℂ) (w' v)).2) ^ js v :=
  rfl

open AutomorphicForm in
open scoped TensorProduct.RightActions in
private theorem GeomSideAssembly.norm_wordSymbol_box_le (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] (SL : Finset (HeightOneSpectrum (𝓞 L))) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (T : Finset (HeightOneSpectrum (𝓞 K))) (w' : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 L))
    (hT : ∀ v ∈ T, w' v ∉ SL) (ks js : HeightOneSpectrum (𝓞 K) → ℕ) (x : GeomSideAssembly.box L SL ξL) :
    ‖GeomSideAssembly.wordSymbol (GeomSideAssembly.box L SL ξL) T w'
        (fun v => (HeckeEigensystem.cNorm (w' v))⁻¹) ks js x‖ ≤
      ∏ v ∈ T,
        ((((Ideal.absNorm (w' v).asIdeal : ℝ) + 1) *
            Real.sqrt ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)), Subgroup.mem_top _⟩ :
              ℂˣ) : ℂ)‖) ^ ks v *
          ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)), Subgroup.mem_top _⟩ :
            ℂˣ) : ℂ)‖ ^ js v) := by
  rw [GeomSideAssembly.wordSymbol_apply, norm_prod]
  refine Finset.prod_le_prod (fun v _ => norm_nonneg _) fun v hv => ?_
  have hx : (x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) ∈ GeomSideAssembly.box L SL ξL := x.2
  obtain ⟨h2, h1, -⟩ := hx.2 (w' v) (hT v hv)
  rw [norm_mul, norm_pow, norm_pow]
  refine mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) h1 _) (pow_le_pow_left₀ (norm_nonneg _) ?_ _)
    (by positivity) (by positivity)
  rw [h2, norm_mul, norm_inv, norm_mul]
  by_cases hc : ‖HeckeEigensystem.cNorm (w' v)‖ = 0
  · simp [hc]
  · rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

open AutomorphicForm in
open scoped TensorProduct.RightActions in
private scoped instance GeomSideAssembly.instCompactSpaceBox (L : Type) [Field L] [NumberField L]
    (SL : Finset (HeightOneSpectrum (𝓞 L))) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) :
    CompactSpace (GeomSideAssembly.box L SL ξL) :=
  isCompact_iff_compactSpace.1 (GeomSideAssembly.isCompact_box L SL ξL)

p2m_reactivate "P2MW.S_AutomorphicForm_forall_exists_integral_lambdaT_twistedAdelicKernel_eq_finsum_centralElliptic_add_and_norm_le_unram.GeomSideAssembly"
open AutomorphicForm in
open scoped TensorProduct.RightActions in
private theorem GeomSideAssembly.eval_bound (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    (SL : Finset (HeightOneSpectrum (𝓞 L))) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (F : C(GeomSideAssembly.box L SL ξL, ℂ) →L[ℂ] ℂ)
    (T : Finset (HeightOneSpectrum (𝓞 K))) (w' : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 L))
    (hT : ∀ v ∈ T, w' v ∉ SL) (ks js : HeightOneSpectrum (𝓞 K) → ℕ) :
    ‖F (GeomSideAssembly.wordSymbol (GeomSideAssembly.box L SL ξL) T w'
        (fun v => (HeckeEigensystem.cNorm (w' v))⁻¹) ks js)‖ ≤
      ‖F‖ * ∏ v ∈ T,
        ((((Ideal.absNorm (w' v).asIdeal : ℝ) + 1) *
            Real.sqrt ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)), Subgroup.mem_top _⟩ :
              ℂˣ) : ℂ)‖) ^ ks v *
          ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)), Subgroup.mem_top _⟩ :
            ℂˣ) : ℂ)‖ ^ js v) := by
  refine (F.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg F))
  refine (ContinuousMap.norm_le _ (Finset.prod_nonneg fun v _ => by positivity)).2 fun x => ?_
  exact GeomSideAssembly.norm_wordSymbol_box_le K L SL ξL T w' hT ks js x

open AutomorphicForm in
open scoped TensorProduct.RightActions in
private theorem GeomSideAssembly.eval_bound_pair (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    (SL : Finset (HeightOneSpectrum (𝓞 L))) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (F G : C(GeomSideAssembly.box L SL ξL, ℂ) →L[ℂ] ℂ)
    (T : Finset (HeightOneSpectrum (𝓞 K))) (w' : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 L))
    (hT : ∀ v ∈ T, w' v ∉ SL) :
    ∀ ks js : HeightOneSpectrum (𝓞 K) → ℕ,
      ‖F (GeomSideAssembly.wordSymbol (GeomSideAssembly.box L SL ξL) T w'
          (fun v => (HeckeEigensystem.cNorm (w' v))⁻¹) ks js)‖ +
        ‖G (GeomSideAssembly.wordSymbol (GeomSideAssembly.box L SL ξL) T w'
          (fun v => (HeckeEigensystem.cNorm (w' v))⁻¹) ks js)‖ ≤
      (‖F‖ + ‖G‖) * ∏ v ∈ T,
        ((((Ideal.absNorm (w' v).asIdeal : ℝ) + 1) *
            Real.sqrt ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)), Subgroup.mem_top _⟩ :
              ℂˣ) : ℂ)‖) ^ ks v *
          ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)), Subgroup.mem_top _⟩ :
            ℂˣ) : ℂ)‖ ^ js v) := by
  intro ks js
  rw [add_mul]
  exact add_le_add (GeomSideAssembly.eval_bound K L SL ξL F T w' hT ks js)
    (GeomSideAssembly.eval_bound K L SL ξL G T w' hT ks js)

private theorem GeomSideAssembly.bound_add {ι : Type*} (B : (ι → ℕ) → (ι → ℕ) → ℝ)
    {a a' b b' : (ι → ℕ) → (ι → ℕ) → ℂ} {C₁ C₂ : ℝ}
    (h₁ : ∀ ks js, ‖a ks js‖ + ‖a' ks js‖ ≤ C₁ * B ks js)
    (h₂ : ∀ ks js, ‖b ks js‖ + ‖b' ks js‖ ≤ C₂ * B ks js) :
    ∀ ks js, ‖a ks js + b ks js‖ + ‖a' ks js + b' ks js‖ ≤ (C₁ + C₂) * B ks js := by
  intro ks js
  calc ‖a ks js + b ks js‖ + ‖a' ks js + b' ks js‖
      ≤ (‖a ks js‖ + ‖b ks js‖) + (‖a' ks js‖ + ‖b' ks js‖) := add_le_add (norm_add_le _ _) (norm_add_le _ _)
    _ = (‖a ks js‖ + ‖a' ks js‖) + (‖b ks js‖ + ‖b' ks js‖) := by ring
    _ ≤ C₁ * B ks js + C₂ * B ks js := add_le_add (h₁ ks js) (h₂ ks js)
    _ = (C₁ + C₂) * B ks js := (add_mul _ _ _).symm

private theorem GeomSideAssembly.w'_notMem_SL
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (h₁ : ∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v → w ∉ SL)
    (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
    (w' : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 L))
    (h₂ : ∀ v ∈ T, (w' v).asIdeal = σ • (ws v).1.asIdeal) :
    ∀ v ∈ T, w' v ∉ SL := by
  intro v hv
  refine h₁ v hv (w' v) ?_
  have hu : HeightOneSpectrum.under (𝓞 K) (w' v) = HeightOneSpectrum.under (𝓞 K) (ws v).1 := by
    apply HeightOneSpectrum.ext
    simp only [HeightOneSpectrum.under_asIdeal, h₂ v hv, Ideal.under_smul]
  exact hu.trans (ws v).2

open AutomorphicForm in
open scoped TensorProduct.RightActions in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α)  (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : ΦL ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSLram : ∀ w : HeightOneSpectrum (𝓞 L),
      (HeightOneSpectrum.under (𝓞 K) w).asIdeal.ramificationIdx' w.asIdeal ≠ 1 → w ∈ SL)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (c u d₁ d₂ : ℝ) (hc : 0 < c)
    (Tc : Set (AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc) (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' WindowedSiegel.centreCutSiegelSet L c u d₁ d₂)
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})) :
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))), Disjoint T S → 2 ≤ T.card →
      (∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v → w ∉ SL) →
      ∀ (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
        (w' : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 L)),
        (∀ v ∈ T, (w' v).asIdeal = σ • (ws v).1.asIdeal) →
      ∀ (ϖs : ∀ v : HeightOneSpectrum (𝓞 K), (ws v).1.adicCompletionIntegers L),
        (∀ v ∈ T, Irreducible (ϖs v)) →
      ∀ (hϖs0 : ∀ v ∈ T,
          algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) ≠ 0)
        (ns : HeightOneSpectrum (𝓞 K) → ℕ)
        (rTs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (ns v) → GL (Fin 2) ((ws v).1.adicCompletion L)),
        (∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
          HeckeIntegralSeam.IsHeckeCosetSystem
            (LocalGL2.integralSubgroup ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L))
            (LocalGL2.diagPi (ϖs v) (hϖs0 v hv)) (rTs v)) →
      ∀ (zs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L)),
        (∀ v ∈ T, (zs v : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)) =
          algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) •
            (1 : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L))) →
      ∃ μ ν : (HeightOneSpectrum (𝓞 K) → ℕ) → (HeightOneSpectrum (𝓞 K) → ℕ) → ℂ,
      (∃ C : ℝ, ∀ ks js : HeightOneSpectrum (𝓞 K) → ℕ,
        ‖μ ks js‖ + ‖ν ks js‖ ≤ C * ∏ v ∈ T,
          ((((Ideal.absNorm (w' v).asIdeal : ℝ) + 1) *
              Real.sqrt ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)), Subgroup.mem_top _⟩ :
                ℂˣ) : ℂ)‖) ^ ks v *
            ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)), Subgroup.mem_top _⟩ :
              ℂˣ) : ℂ)‖ ^ js v)) ∧
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
        (φ : AdelicGL2 (𝓞 L) L → ℂ)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
        IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (ns v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)
            else φS v) →
      ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R → (
  ∫ x in Φ₀, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      (@AutomorphicForm.lambdaT _
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
        (fun t => AutomorphicForm.unipotentGL2 t)
        (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
        (fun y => AutomorphicForm.twistedAdelicKernel L (AutomorphicForm.sigmaAdelicAct K L D σ) φ x y)
        (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL)
    ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
  (∫ x in ΦL, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      (∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
          (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
          LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
        φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
          AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ∂νZL)
    ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) +
      ((R : ℂ) * ν ks js + μ ks js) := by
  intro T _hTS hT hTSL ws w' hw' ϖs hϖ hϖs0 ns rTs hcos zs hzs
  by_cases hαβ : α < β
  ·
    obtain ⟨μU, νU, -, hU⟩ :=
      AutomorphicForm.forall_exists_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_affine_unram
        K L α β hα hαβ ΦL νZL ΩL hΩL D σ hgen SL ξL hSLram hξc hξt S φa φS
        (GeomSideAssembly.box L SL ξL) (fun x hx => hx) c u d₁ d₂ hc Tc hTc Φ₀ hΦ₀S hΦ₀s
        hΦ₀ T hT hTSL ws w' hw' ϖs hϖ hϖs0 ns rTs hcos zs hzs
    obtain ⟨μH, νH, ⟨CH, hHC⟩, hH⟩ :=
      AutomorphicForm.forall_exists_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_affine_bound
        K L α β hα hαβ ΦL νZL ΩL hΩL D σ hgen SL ξL hξc hξt S φa φS c u d₁ d₂ hc Tc hTc Φ₀ hΦ₀S hΦ₀s
        hΦ₀ T hT hTSL ws w' hw' ϖs hϖ hϖs0 ns rTs hcos zs hzs
    refine ⟨fun ks js => μU (GeomSideAssembly.wordSymbol (GeomSideAssembly.box L SL ξL) T w'
          (fun v => (HeckeEigensystem.cNorm (w' v))⁻¹) ks js) + μH ks js,
      fun ks js => νU (GeomSideAssembly.wordSymbol (GeomSideAssembly.box L SL ξL) T w'
          (fun v => (HeckeEigensystem.cNorm (w' v))⁻¹) ks js) + νH ks js,
      ⟨‖μU‖ + ‖νU‖ + CH, ?_⟩, ?_⟩
    · exact GeomSideAssembly.bound_add _
        (GeomSideAssembly.eval_bound_pair K L SL ξL μU νU T w'
          (GeomSideAssembly.w'_notMem_SL K L σ SL T hTSL ws w' hw')) hHC
    · intro ks js φ φf hfact
      obtain ⟨RA, hRA⟩ :=
        AutomorphicForm.forall_exists_lambdaT_twistedAdelicKernel_eq_finsum_add_sub_indicator_constantTerm_add
          K L α β ΦL hΦs hΦ νZL ΩL D σ hgen ξL S φa φS Φ₀ hΦ₀s hΦ₀ T ws ns rTs zs ks js φ φf hfact
      obtain ⟨hEin, hEout⟩ :=
        AutomorphicForm.integrableOn_setIntegral_mul_finsum_centralElliptic_twistedAdelicKernel
          K L α β hα hαβ νZL ΩL hΩL D σ hgen ξL hξc hξt S φa φS Φ₀ hΦ₀s hΦ₀ T ws ns rTs zs ks js φ φf hfact
      obtain ⟨RU, hRU⟩ := hU ks js φ φf hfact
      obtain ⟨RH, hRH⟩ := hH ks js φ φf hfact
      refine ⟨max RA (max RU RH), fun R hR => ?_⟩
      obtain ⟨hpt, htrans⟩ := hRA R (le_trans (le_max_left _ _) hR)
      obtain ⟨hUin, hUout, hUeq⟩ :=
        hRU R (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hR)
          (GeomSideAssembly.wordSymbol (GeomSideAssembly.box L SL ξL) T w'
            (fun v => (HeckeEigensystem.cNorm (w' v))⁻¹) ks js) (fun _ => rfl)
      obtain ⟨hHin, hHout, hHeq⟩ :=
        hRH R (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hR)
      show _ = _ + ((R : ℂ) * (νU (GeomSideAssembly.wordSymbol (GeomSideAssembly.box L SL ξL) T w'
            (fun v => (HeckeEigensystem.cNorm (w' v))⁻¹) ks js) + νH ks js) +
        (μU (GeomSideAssembly.wordSymbol (GeomSideAssembly.box L SL ξL) T w'
            (fun v => (HeckeEigensystem.cNorm (w' v))⁻¹) ks js) + μH ks js))
      exact GeomSideAssembly.integral_eq_of_splitting (adelicGLHaar (Fin 2) (𝓞 L) L) νZL Φ₀ ΦL ΩL
        (fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
        (fun x z =>
        @AutomorphicForm.lambdaT _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
            (fun y => AutomorphicForm.twistedAdelicKernel L (AutomorphicForm.sigmaAdelicAct K L D σ) φ x y)
            (AutomorphicForm.centralScalar (𝓞 L) L z * x))
        (fun x z =>
        (∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
              (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
              LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
              φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))))
        (fun x z =>
        ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
              γ ∈ AutomorphicForm.unipotentCell K ∧
              LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
              φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
          Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
          (@AutomorphicForm.constantTerm _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
              (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
                Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1},
              φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
          (AutomorphicForm.centralScalar (𝓞 L) L z * x)))
        (fun x z =>
        ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
              γ ∈ AutomorphicForm.hyperbolicCell K ∧
              LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
              φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
          Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
          (@AutomorphicForm.constantTerm _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
              (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
                Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1},
              φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
          (AutomorphicForm.centralScalar (𝓞 L) L z * x)))
        _ R (νU (GeomSideAssembly.wordSymbol (GeomSideAssembly.box L SL ξL) T w'
            (fun v => (HeckeEigensystem.cNorm (w' v))⁻¹) ks js)) (νH ks js)
          (μU (GeomSideAssembly.wordSymbol (GeomSideAssembly.box L SL ξL) T w'
            (fun v => (HeckeEigensystem.cNorm (w' v))⁻¹) ks js)) (μH ks js)
          hpt htrans rfl hEin hEout hUin hUout hUeq hHin hHout hHeq
  ·
    have hnull := DetNormLevelSet.adelicGLHaar_setOf_ideleNorm_det_mem_Icc_eq_zero_of_not_lt L α β hα hαβ
    have h0 : (adelicGLHaar (Fin 2) (𝓞 L) L).restrict Φ₀ = 0 :=
      Measure.restrict_eq_zero.2 (measure_mono_null hΦ₀s hnull)
    have hL : (adelicGLHaar (Fin 2) (𝓞 L) L).restrict ΦL = 0 :=
      Measure.restrict_eq_zero.2 (measure_mono_null hΦs hnull)
    refine ⟨fun _ _ => 0, fun _ _ => 0, ⟨0, fun _ _ => by simp⟩, ?_⟩
    intro ks js φ φf hfact
    refine ⟨0, fun R _ => ?_⟩
    rw [h0, hL]
    simp

#print axioms solution

end S_AutomorphicForm_forall_exists_integral_lambdaT_twistedAdelicKernel_eq_finsum_centralElliptic_add_and_norm_le_unram
end P2MW
export P2MW.S_AutomorphicForm_forall_exists_integral_lambdaT_twistedAdelicKernel_eq_finsum_centralElliptic_add_and_norm_le_unram (solution)
