-- Prove2me | solution 1 for AutomorphicForm.exists_continuous_forall_not_isEisenstein_noAtomicMass_twistedGeometricRemainder_unram
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/1787cb7f-c4e0-5987-b6b0-02132fda2686

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
import Definitions.Def_AutomorphicForm_TwistedGeometricRemainder
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Theorems.Thm_AutomorphicForm_exists_atomic_forall_exists_integral_lambdaT_twistedAdelicKernel_eq_twistedCutTrace_add_symm_unram
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Theorems.Thm_NumberField_TateGlobal_exists_measure_fundamentalDomain_inter_ideleNorm_Icc_eq_mul_log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.NumberTheory.RamificationInertia.Galois
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_continuous_forall_not_isEisenstein_noAtomicMass_twistedGeometricRemainder_unram
p2m_attr_erase "instance" "AutomorphicForm.GaussTwist.instFiniteLocalGaussFactorValHeightOneSpectrumRingOfIntegersMemFinsetModulusPrimes AutomorphicForm.GaussTwist.instFintypeGaussIndex AutomorphicForm.GaussTwist.instCommGroupGaussIndex AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite instCountableHeightOneSpectrumRingOfIntegers_definitions instCountableHeightOneSpectrumRingOfIntegersRat_definitions M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup LanglandsTunnell.CubicInduction.countable_GL2 LanglandsTunnell.CubicInduction.countable_mirabolicIndex ExtCitation.LocalLevel.compactGw"
p2m_attr_erase "instance" "ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply HeckePair.IsGelfandInvolution.reindex_mk HeckePair.IsGelfandInvolution.reindexInv_mk FLT.HaarFiniteOrderGates.negContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.doublingContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.invContinuousMulEquiv_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.CuspidalConstituent.rightRegular_apply AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val AutomorphicForm.iotaZsqrtdNegTwo_apply AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.cpowChar_apply_val AutomorphicForm.gl2Weyl_val AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec"
p2m_attr_erase "simp" "AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec LanglandsTunnell.Converse.ArchDatumC.mk.injEq LanglandsTunnell.Converse.ArchDatumC.mk.sizeOf_spec LanglandsTunnell.Converse.FinWhittakerDatum.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.injEq LanglandsTunnell.Converse.FinWhittakerDatum.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.sizeOf_spec LanglandsTunnell.Converse.JLData.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.injEq LanglandsTunnell.Converse.JLData.mk.sizeOf_spec UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22LocalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_right ContinuousAddEquiv.preimage_mulLeft_smul AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply"
p2m_attr_erase "simp" "GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add AutomorphicForm.adeleArchAlgHom_apply AutomorphicForm.tensorPlaceHom_tmul AutomorphicForm.tensorArchHom_tmul AutomorphicForm.adelePlaceAlgHom_apply M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk LanglandsTunnell.CubicInduction.coe_diagUnits2 LanglandsTunnell.RankinSelberg.mem_primeFibre LanglandsTunnell.CubicInduction.coe_diagUnitGL2 LanglandsTunnell.CubicInduction.iotaTorusLocal_zero LanglandsTunnell.CubicInduction.upperUnipotent3_zero LanglandsTunnell.CubicInduction.radicalP21_coe LanglandsTunnell.CubicInduction.coe_iotaGL LanglandsTunnell.CubicInduction.radicalP12_coe LanglandsTunnell.CubicInduction.radicalP12_zero LanglandsTunnell.CubicInduction.radicalP21_zero LanglandsTunnell.CubicInduction.upperUnipotent3_coe ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe"
p2m_attr_erase "simp" "ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AutomorphicForm.LocalWeightedOrbital.halfWeighted_zero_fun AutomorphicForm.LocalWeightedOrbital.centralValue_zero_fun AutomorphicForm.LocalWeightedOrbital.normSplitOrbital_zero_fun AutomorphicForm.LocalWeightedOrbital.slice_zero_fun AutomorphicForm.LocalWeightedOrbital.correctionTerm_zero_fun AutomorphicForm.LocalWeightedOrbital.bTerm_zero_fun AutomorphicForm.LocalWeightedOrbital.cTerm_zero_fun AutomorphicForm.LocalWeightedOrbital.invariantPart_zero_fun AutomorphicForm.LocalWeightedOrbital.splitOrbital_zero_fun AutomorphicForm.LocalWeightedOrbital.unipotentMellin_zero_fun IsLocalRing.principalUnits_zero"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace R2TwRem

section Band

p2m_open "AutomorphicForm~det_centralScalar NumberField.TateGlobal"

variable (K : Type) [Field K] [NumberField K]

theorem det_centralScalar (z : (AdeleRing (𝓞 K) K)ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z) = z ^ 2 := by
  show Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) z) = z ^ 2
  rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]

theorem ideleNorm_det_centralScalar (z : (AdeleRing (𝓞 K) K)ˣ) :
    ideleNorm K (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) = ideleNorm K z ^ 2 := by
  rw [det_centralScalar, sq, sq, ideleNorm_mul]

theorem band_eq (α β : ℝ) :
    {z : (AdeleRing (𝓞 K) K)ˣ | ideleNorm K (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈
        Set.Icc α β} =
      {z : (AdeleRing (𝓞 K) K)ˣ | ideleNorm K z ∈ Set.Icc (Real.sqrt α) (Real.sqrt β)} := by
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_Icc, ideleNorm_det_centralScalar]
  have hz : 0 < ideleNorm K z := ideleNorm_pos z
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨Real.sqrt_le_iff.mpr ⟨hz.le, h₁⟩, (Real.le_sqrt' hz).mpr h₂⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨(Real.sqrt_le_iff.mp h₁).2, (Real.le_sqrt' hz).mp h₂⟩

theorem bandConstant_ne_zero {α β : ℝ} (hα : 0 < α) (hαβ : α < β)
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK) :
    ((νZK (ΩK ∩ {z | ideleNorm K
          (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) ≠ 0 := by
  obtain ⟨C, hC0, hCtop, hC⟩ :=
    NumberField.TateGlobal.exists_measure_fundamentalDomain_inter_ideleNorm_Icc_eq_mul_log K νZK
  have hsa : 0 < Real.sqrt α := Real.sqrt_pos.mpr hα
  have hsab : Real.sqrt α < Real.sqrt β := Real.sqrt_lt_sqrt hα.le hαβ
  have hvol := hC ΩK hΩK (Real.sqrt α) (Real.sqrt β) hsa hsab.le
  rw [band_eq K α β, hvol]
  have hlog : 0 < Real.log (Real.sqrt β / Real.sqrt α) :=
    Real.log_pos ((one_lt_div hsa).mpr hsab)
  have hne0 : C * ENNReal.ofReal (Real.log (Real.sqrt β / Real.sqrt α)) ≠ 0 :=
    mul_ne_zero hC0 (by simpa [ENNReal.ofReal_eq_zero, not_le] using hlog)
  have hnetop : C * ENNReal.ofReal (Real.log (Real.sqrt β / Real.sqrt α)) ≠ ⊤ :=
    ENNReal.mul_ne_top hCtop ENNReal.ofReal_ne_top
  have hR : (C * ENNReal.ofReal (Real.log (Real.sqrt β / Real.sqrt α))).toReal ≠ 0 := by
    rw [Ne, ENNReal.toReal_eq_zero_iff, not_or]
    exact ⟨hne0, hnetop⟩
  exact_mod_cast hR

end Band

section Affine

theorem intercept_sub_eq_of_forall_le {A : ℝ → ℂ} {B y s a m n : ℂ} (R₀ : ℝ)
    (h : ∀ R : ℝ, R₀ ≤ R → A R = y * s + ((R : ℂ) * n + a + m)) :
    HalfLine.intercept (fun R : ℝ => A R - B) = y * s + a + m - B :=
  HalfLine.intercept_eq_of_forall_le_eq_add_mul (ν := n) ⟨R₀, fun R hle => by
    rw [h R hle]
    ring⟩

end Affine

section Retraction

variable {P Q : Type*}

noncomputable def fibRep (under : P → Q) (SL : Finset P) (T : Finset Q) (w' : Q → P) (d : P) (u : Q) : P :=
  by
  classical
  exact if h : ∃ v ∈ T, under (w' v) = u then w' h.choose
    else if h' : ∃ w₀ : P, w₀ ∉ SL ∧ under w₀ = u then h'.choose else d

noncomputable def retract (under : P → Q) (SL : Finset P) (T : Finset Q) (w' : Q → P) (d : P) (w : P) : P :=
  by
  classical
  exact if w ∈ SL then w else fibRep under SL T w' d (under w)

variable (under : P → Q) (SL : Finset P) (T : Finset Q) (w' : Q → P) (d : P)

theorem retract_of_mem {w : P} (hw : w ∈ SL) : retract under SL T w' d w = w := by
  classical
  simp [retract, hw]

theorem retract_of_not_mem {w : P} (hw : w ∉ SL) :
    retract under SL T w' d w = fibRep under SL T w' d (under w) := by
  classical
  simp [retract, hw]

theorem retract_spec (hSL : ∀ w w' : P, under w = under w' → (w ∈ SL ↔ w' ∈ SL)) {w : P} (hw : w ∉ SL) :
    retract under SL T w' d w ∉ SL ∧ under (retract under SL T w' d w) = under w := by
  classical
  rw [retract_of_not_mem under SL T w' d hw]
  unfold fibRep
  by_cases h : ∃ v ∈ T, under (w' v) = under w
  · rw [dif_pos h]
    have hs := h.choose_spec
    exact ⟨fun hm => hw ((hSL _ _ hs.2).1 hm), hs.2⟩
  · rw [dif_neg h]
    have h' : ∃ w₀ : P, w₀ ∉ SL ∧ under w₀ = under w := ⟨w, hw, rfl⟩
    rw [dif_pos h']
    exact h'.choose_spec

theorem retract_congr {w₁ w₂ : P} (h₁ : w₁ ∉ SL) (h₂ : w₂ ∉ SL) (he : under w₁ = under w₂) :
    retract under SL T w' d w₁ = retract under SL T w' d w₂ := by
  rw [retract_of_not_mem under SL T w' d h₁, retract_of_not_mem under SL T w' d h₂, he]

theorem retract_shift (hunder : ∀ v ∈ T, under (w' v) = v)
    (hT : ∀ v ∈ T, ∀ w : P, under w = v → w ∉ SL) {v : Q} (hv : v ∈ T) :
    retract under SL T w' d (w' v) = w' v := by
  classical
  have hnot : w' v ∉ SL := hT v hv _ (hunder v hv)
  rw [retract_of_not_mem under SL T w' d hnot]
  unfold fibRep
  have h : ∃ v₁ ∈ T, under (w' v₁) = under (w' v) := ⟨v, hv, rfl⟩
  rw [dif_pos h]
  obtain ⟨hv₁, he⟩ := h.choose_spec
  rw [hunder _ hv₁] at he
  exact congrArg w' (he.trans (hunder _ hv))

end Retraction

section Pullback

variable {P : Type*} (ρ : P → P) {X B : Set (P → ℂ × ℂ)}

theorem continuous_reread : Continuous fun x : P → ℂ × ℂ => x ∘ ρ :=
  continuous_pi fun w => continuous_apply (ρ w)

def rereadMap (hmap : ∀ x ∈ B, x ∘ ρ ∈ X) : C(B, X) :=
  ⟨fun y => ⟨(y : P → ℂ × ℂ) ∘ ρ, hmap y y.2⟩,
    ((continuous_reread ρ).comp continuous_subtype_val).subtype_mk _⟩

noncomputable def pullback (hmap : ∀ x ∈ B, x ∘ ρ ∈ X) : C(X, ℂ) →L[ℂ] C(B, ℂ) where
  toFun g := g.comp (rereadMap ρ hmap)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := ContinuousMap.continuous_precomp (rereadMap ρ hmap)

theorem pullback_apply (hmap : ∀ x ∈ B, x ∘ ρ ∈ X) (g : C(X, ℂ)) (y : B) :
    pullback ρ hmap g y = g ⟨(y : P → ℂ × ℂ) ∘ ρ, hmap y y.2⟩ := rfl

end Pullback

section Places

theorem smul_algebraMap_ringOfIntegers (K L : Type) [Field K] [Field L] [Algebra K L]
    (τ : L ≃ₐ[K] L) (a : 𝓞 K) :
    τ • (algebraMap (𝓞 K) (𝓞 L) a) = algebraMap (𝓞 K) (𝓞 L) a := by
  apply NumberField.RingOfIntegers.ext
  show τ (algebraMap (𝓞 K) (𝓞 L) a : L) = (algebraMap (𝓞 K) (𝓞 L) a : L)
  rw [show ((algebraMap (𝓞 K) (𝓞 L) a : 𝓞 L) : L) = algebraMap K L (a : K) from
    (IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L a).symm.trans (IsScalarTower.algebraMap_apply (𝓞 K) K L a)]
  exact τ.commutes (a : K)

theorem under_eq_of_asIdeal_eq_smul (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (τ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K))
    (w₀ : v.Extension (𝓞 L)) (w : HeightOneSpectrum (𝓞 L)) (h : w.asIdeal = τ • w₀.1.asIdeal) :
    HeightOneSpectrum.under (𝓞 K) w = v := by
  rw [← w₀.2]
  apply HeightOneSpectrum.ext
  show w.asIdeal.under (𝓞 K) = w₀.1.asIdeal.under (𝓞 K)
  ext a
  rw [Ideal.mem_comap, Ideal.mem_comap, h, Ideal.mem_pointwise_smul_iff_inv_smul_mem,
    smul_algebraMap_ringOfIntegers K L]

theorem absNorm_comap_ringEquiv (L : Type) [Field L] [NumberField L] (e : 𝓞 L ≃+* 𝓞 L) (I : Ideal (𝓞 L)) :
    Ideal.absNorm (I.comap (e : 𝓞 L →+* 𝓞 L)) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  refine Nat.card_congr (Ideal.quotientEquiv (I.comap (e : 𝓞 L →+* 𝓞 L)) I e ?_).toEquiv
  exact (Ideal.map_comap_of_surjective (e : 𝓞 L →+* 𝓞 L) e.surjective I).symm

theorem absNorm_eq_of_under_eq (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] (w w' : HeightOneSpectrum (𝓞 L))
    (h : HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w') :
    Ideal.absNorm w.asIdeal = Ideal.absNorm w'.asIdeal := by
  have h' : w.asIdeal.under (𝓞 K) = w'.asIdeal.under (𝓞 K) := by
    simpa using congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal h
  haveI : w.asIdeal.LiesOver (w.asIdeal.under (𝓞 K)) := ⟨rfl⟩
  haveI : w'.asIdeal.LiesOver (w.asIdeal.under (𝓞 K)) := ⟨h'⟩
  obtain ⟨τ, hτ⟩ := Ideal.exists_comap_galRestrict_eq (𝓞 K) K L (𝓞 L) (p := w.asIdeal.under (𝓞 K))
    ⟨w.isPrime, inferInstance⟩ ⟨w'.isPrime, inferInstance⟩
  rw [← hτ]
  exact (absNorm_comap_ringEquiv L (galRestrict (𝓞 K) K L (𝓞 L) τ).toRingEquiv w.asIdeal).symm

end Places

section Box

p2m_open "AutomorphicForm~det_centralScalar"

theorem reread_mem_box
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (SL : Finset (HeightOneSpectrum (𝓞 L))) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξσ : ∀ w w' : HeightOneSpectrum (𝓞 L), w ∉ SL → w' ∉ SL →
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' →
        ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ =
          ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w'), Subgroup.mem_top _⟩)
    (ρ : HeightOneSpectrum (𝓞 L) → HeightOneSpectrum (𝓞 L)) (hρS : ∀ w, w ∈ SL → ρ w = w)
    (hρ : ∀ w, w ∉ SL →
      ρ w ∉ SL ∧ HeightOneSpectrum.under (𝓞 K) (ρ w) = HeightOneSpectrum.under (𝓞 K) w)
    (x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ)
    (hx : x ∈ {x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ |
      (∀ w ∈ SL, x w = 0) ∧
      ∀ w ∉ SL,
        (x w).2 = HeckeEigensystem.cNorm w *
            ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ∧
        ‖(x w).1‖ ≤ ((Ideal.absNorm w.asIdeal : ℝ) + 1) *
            Real.sqrt ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ :
              ℂˣ) : ℂ)‖ ∧
        conj (x w).1 = conj (x w).2 / ((‖(x w).2‖ : ℝ) : ℂ) * (x w).1}) :
    x ∘ ρ ∈ {x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ |
      (∀ w ∈ SL, x w = 0) ∧
      ∀ w ∉ SL,
        (x w).2 = HeckeEigensystem.cNorm w *
            ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ∧
        ‖(x w).1‖ ≤ ((Ideal.absNorm w.asIdeal : ℝ) + 1) *
            Real.sqrt ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ :
              ℂˣ) : ℂ)‖ ∧
        conj (x w).1 = conj (x w).2 / ((‖(x w).2‖ : ℝ) : ℂ) * (x w).1} := by
  simp only [Set.mem_setOf_eq] at hx ⊢
  obtain ⟨hS, hoff⟩ := hx
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · simp only [Function.comp_apply, hρS w hw]
    exact hS w hw
  · obtain ⟨h₁, h₂⟩ := hρ w hw
    obtain ⟨e₂, eb, el⟩ := hoff (ρ w) h₁
    have hξ := hξσ (ρ w) w h₁ hw h₂
    have hn : Ideal.absNorm (ρ w).asIdeal = Ideal.absNorm w.asIdeal :=
      absNorm_eq_of_under_eq K L (ρ w) w h₂
    have hc : HeckeEigensystem.cNorm (ρ w) = HeckeEigensystem.cNorm w := by
      simp only [HeckeEigensystem.cNorm, hn]
    simp only [Function.comp_apply]
    refine ⟨?_, ?_, el⟩
    · rw [e₂, hc, hξ]
    · rw [hn, hξ] at eb
      exact eb

end Box

end R2TwRem

open scoped TensorProduct.RightActions in
p2m_open "AutomorphicForm~det_centralScalar" in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : ΦL ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ.symm)
    (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSL : ∀ w w' : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → (w ∈ SL ↔ w' ∈ SL))
    (hSLram : ∀ w : HeightOneSpectrum (𝓞 L),
      (HeightOneSpectrum.under (𝓞 K) w).asIdeal.ramificationIdx' w.asIdeal ≠ 1 → w ∈ SL)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (hξσ : ∀ w w' : HeightOneSpectrum (𝓞 L), w ∉ SL → w' ∉ SL →
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' →
        ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ =
          ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w'), Subgroup.mem_top _⟩)
    (N : Ideal (𝓞 L)) (hN : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N → w ∈ SL)
    (tysL : ArchTypeFamily L)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (X : Set (HeightOneSpectrum (𝓞 L) → ℂ × ℂ)) (hXc : IsCompact X)
    (hX : {x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ |
        (∀ w ∈ SL, x w = 0) ∧
        ∀ w ∉ SL,
          (x w).2 = HeckeEigensystem.cNorm w *
              ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ∧
          ‖(x w).1‖ ≤ ((Ideal.absNorm w.asIdeal : ℝ) + 1) *
              Real.sqrt ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ :
                ℂˣ) : ℂ)‖ ∧
          conj (x w).1 = conj (x w).2 / ((‖(x w).2‖ : ℝ) : ℂ) * (x w).1} ⊆ X) :
    ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
          (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) ≠ 0 ∧
    ∃ (tabs : ℕ → (HeightOneSpectrum (𝓞 L) → ℂ × ℂ)) (htabs : ∀ n, tabs n ∈ X) (cs : ℕ → ℂ),
    (Summable fun n => ‖cs n‖) ∧
    (∀ n, cs n ≠ 0 →
      (∀ w w' : HeightOneSpectrum (𝓞 L), w ∉ SL → w' ∉ SL →
          HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → tabs n w = tabs n w') ∧
      ∃ (M : Ideal (𝓞 L)) (hM : M ≠ ⊥) (χ₁ χ₂ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ),
        (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ₁ z : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 L) L)ˣ,
          z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
            χ₁ z = 1) ∧
        (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ₂ z : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 L) L)ˣ,
          z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
            χ₂ z = 1) ∧
        ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL →
          tabs n w = ((LanglandsTunnell.Converse.eisensteinTableOf L M hM χ₁ χ₂).a w,
            (LanglandsTunnell.Converse.eisensteinTableOf L M hM χ₁ χ₂).b w)) ∧
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))), Disjoint T S → 2 ≤ T.card →
      (∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v → w ∉ SL) →
      ∀ (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
        (w' : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 L)),
        (∀ v ∈ T, (w' v).asIdeal = σ.symm • (ws v).1.asIdeal) →
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
      ∃ Λ : C(X, ℂ) →L[ℂ] ℂ,
      (∀ (τ : HeightOneSpectrum (𝓞 K) → ℂ × ℂ), ∀ ε > (0 : ℝ),
        ∃ U : HeightOneSpectrum (𝓞 K) → Set (ℂ × ℂ), (∀ v ∈ T, IsOpen (U v) ∧ τ v ∈ U v) ∧
          ∀ g : C(X, ℂ),
            (∀ y : X, (∃ v ∈ T, (y : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v) ∉ U v) → g y = 0) →
            (∀ y, ‖g y‖ ≤ 1) → ‖Λ g‖ < ε) ∧
      (∀ g : C(X, ℂ),
        (∀ y : X, (∀ w₁ w₂ : HeightOneSpectrum (𝓞 L), w₁ ∉ SL → w₂ ∉ SL →
            HeightOneSpectrum.under (𝓞 K) w₁ = HeightOneSpectrum.under (𝓞 K) w₂ →
              (y : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) w₁ = (y : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) w₂) →
            g y = 0) →
        Λ g = 0) ∧
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
        (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
        IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (ns v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)
            else φS v) →
        IsBiInvariantUnder L (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) φ →
        IsArchBiFinite L tysL φ →
      ∀ g : C(X, ℂ),
        (∀ x : X, g x = ∏ v ∈ T,
          ((x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v)).1 ^ ks v *
            ((HeckeEigensystem.cNorm (w' v))⁻¹ *
              ((x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v)).2) ^ js v) → (
  ∫ x in ΦL, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      (∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
          (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
          LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) = ConjClasses.mk γ},
        φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
          AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ∂νZL)
    ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) -
          ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) *
          ∑' Ψ : {Ψ : HeckeEigensystem L ℂ //
              Ψ ∈ cuspClasses L
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL},
            twistedCutTrace K L D σ
              (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL Ψ.1 tysL φ hφ hφc =
          ((∑' n, cs n * g ⟨tabs n, htabs n⟩) + Λ g -
            AutomorphicForm.twistedGeometricRemainder K L D σ.symm hgen ΦL
              (AutomorphicForm.canonicalTruncationDomain L α β) νZL ΩL ξL φ) := by
  have _ := hXc

  obtain ⟨hc, hTc, hΦ₀S, hΦ₀s, hΦ₀⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum L α β hα hαβ

  have hgen₁ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ := by
    intro τ
    have h := hgen τ
    rwa [← AlgEquiv.aut_inv, Subgroup.zpowers_inv] at h

  obtain ⟨tabs, htabs, cs, hsum, hadm, hT1⟩ :=
    AutomorphicForm.exists_atomic_forall_exists_integral_lambdaT_twistedAdelicKernel_eq_twistedCutTrace_add_symm_unram
      K L α β hα hαβ ΦL hΦs hΦ νZL ΩL hΩL D σ hgen₁ SL hSLram ξL hSL hξc hξt N hN tysL S φa φS
      {x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ |
      (∀ w ∈ SL, x w = 0) ∧
      ∀ w ∉ SL,
        (x w).2 = HeckeEigensystem.cNorm w *
            ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ∧
        ‖(x w).1‖ ≤ ((Ideal.absNorm w.asIdeal : ℝ) + 1) *
            Real.sqrt ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ :
              ℂˣ) : ℂ)‖ ∧
        conj (x w).1 = conj (x w).2 / ((‖(x w).2‖ : ℝ) : ℂ) * (x w).1}
      (fun x hx => hx)
      (AutomorphicForm.canonicalTruncationFloor L α β)
      (AutomorphicForm.canonicalTruncationWindow L α β)
      (AutomorphicForm.canonicalTruncationLowerCut L α β)
      (AutomorphicForm.canonicalTruncationUpperCut L α β)
      hc
      (AutomorphicForm.canonicalTruncationTranslates L α β)
      hTc
      (AutomorphicForm.canonicalTruncationDomain L α β)
      hΦ₀S hΦ₀s hΦ₀
  refine ⟨R2TwRem.bandConstant_ne_zero L hα hαβ νZL ΩL hΩL, tabs, fun n => hX (htabs n), cs, hsum, hadm, ?_⟩
  intro T hTS hcard hSLT ws w' hw' ϖs hϖ hϖs0 ns rTs hrTs zs hzs

  have hunder : ∀ v ∈ T, HeightOneSpectrum.under (𝓞 K) (w' v) = v := fun v hv =>
    R2TwRem.under_eq_of_asIdeal_eq_smul K L σ.symm v (ws v) (w' v) (hw' v hv)

  obtain ⟨ρ, hρS, hρspec, hρfix, hρc⟩ : ∃ ρ : HeightOneSpectrum (𝓞 L) → HeightOneSpectrum (𝓞 L),
      (∀ w, w ∈ SL → ρ w = w) ∧
      (∀ w, w ∉ SL → ρ w ∉ SL ∧ HeightOneSpectrum.under (𝓞 K) (ρ w) = HeightOneSpectrum.under (𝓞 K) w) ∧
      (∀ v ∈ T, ρ (w' v) = w' v) ∧
      ∀ w₁ w₂, w₁ ∉ SL → w₂ ∉ SL →
        HeightOneSpectrum.under (𝓞 K) w₁ = HeightOneSpectrum.under (𝓞 K) w₂ → ρ w₁ = ρ w₂ := by
    obtain ⟨v₀, hv₀⟩ : T.Nonempty := Finset.card_pos.mp (by omega)
    exact ⟨R2TwRem.retract (HeightOneSpectrum.under (𝓞 K)) SL T w' (w' v₀),
      fun w hw => R2TwRem.retract_of_mem _ SL T w' _ hw,
      fun w hw => R2TwRem.retract_spec _ SL T w' _ hSL hw,
      fun v hv => R2TwRem.retract_shift _ SL T w' _ hunder hSLT hv,
      fun w₁ w₂ h₁ h₂ he => R2TwRem.retract_congr _ SL T w' _ h₁ h₂ he⟩

  have hmap : ∀ x ∈ {x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ |
      (∀ w ∈ SL, x w = 0) ∧
      ∀ w ∉ SL,
        (x w).2 = HeckeEigensystem.cNorm w *
            ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ∧
        ‖(x w).1‖ ≤ ((Ideal.absNorm w.asIdeal : ℝ) + 1) *
            Real.sqrt ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ :
              ℂˣ) : ℂ)‖ ∧
        conj (x w).1 = conj (x w).2 / ((‖(x w).2‖ : ℝ) : ℂ) * (x w).1}, x ∘ ρ ∈ X :=
    fun x hx => hX (R2TwRem.reread_mem_box K L SL ξL hξσ ρ hρS hρspec x hx)
  obtain ⟨μ₁, ν₁, hcyl, hmem⟩ := hT1 T hTS hcard hSLT ws w' hw' ϖs hϖ hϖs0 ns rTs hrTs zs hzs
  refine ⟨μ₁.comp (R2TwRem.pullback ρ hmap), ?_, ?_, ?_⟩
  ·
    intro τ ε hε
    obtain ⟨U, hU, hsmall⟩ := hcyl τ ε hε
    refine ⟨U, hU, fun g hg hg1 => ?_⟩
    rw [ContinuousLinearMap.comp_apply]
    refine hsmall _ (fun y hy => ?_) (fun y => by rw [R2TwRem.pullback_apply]; exact hg1 _)
    rw [R2TwRem.pullback_apply]
    refine hg _ ?_
    obtain ⟨v, hv, hyv⟩ := hy
    refine ⟨v, hv, ?_⟩
    show (y : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (ρ (w' v)) ∉ U v
    rw [hρfix v hv]
    exact hyv
  ·
    intro g hg
    rw [ContinuousLinearMap.comp_apply]
    have hzero : R2TwRem.pullback ρ hmap g = 0 := by
      ext y
      rw [R2TwRem.pullback_apply, ContinuousMap.zero_apply]
      refine hg _ fun w₁ w₂ h₁ h₂ he => ?_
      show (y : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (ρ w₁) = (y : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (ρ w₂)
      rw [hρc w₁ w₂ h₁ h₂ he]
    rw [hzero, map_zero]
  · intro ks js φ hφ hφc φf hfact hlev harch g hg
    obtain ⟨R₀, hR⟩ := hmem ks js φ hφ hφc φf hfact hlev harch

    have hg' : ∀ y, R2TwRem.pullback ρ hmap g y = ∏ v ∈ T,
        ((y : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v)).1 ^ ks v *
          ((HeckeEigensystem.cNorm (w' v))⁻¹ * ((y : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v)).2) ^ js v := by
      intro y
      rw [R2TwRem.pullback_apply, hg]
      refine Finset.prod_congr rfl fun v hv => ?_
      show ((y : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (ρ (w' v))).1 ^ ks v *
          ((HeckeEigensystem.cNorm (w' v))⁻¹ * ((y : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (ρ (w' v))).2) ^ js v = _
      rw [hρfix v hv]

    have hA : ∑' n, cs n * R2TwRem.pullback ρ hmap g ⟨tabs n, htabs n⟩ =
        ∑' n, cs n * g ⟨tabs n, hX (htabs n)⟩ := by
      refine tsum_congr fun n => ?_
      by_cases hn : cs n = 0
      · simp [hn]
      · congr 1
        rw [R2TwRem.pullback_apply]
        congr 1
        apply Subtype.ext
        funext w
        show tabs n (ρ w) = tabs n w
        by_cases hw : w ∈ SL
        · rw [hρS w hw]
        · exact (hadm n hn).1 (ρ w) w (hρspec w hw).1 hw (hρspec w hw).2

    have hrem :
        AutomorphicForm.twistedGeometricRemainder K L D σ.symm hgen ΦL
          (AutomorphicForm.canonicalTruncationDomain L α β) νZL ΩL ξL φ = _ :=
      R2TwRem.intercept_sub_eq_of_forall_le R₀ (fun R hle => hR R hle _ hg')
    rw [ContinuousLinearMap.comp_apply, ← hA, hrem]
    ring

end S_AutomorphicForm_exists_continuous_forall_not_isEisenstein_noAtomicMass_twistedGeometricRemainder_unram
end P2MW
export P2MW.S_AutomorphicForm_exists_continuous_forall_not_isEisenstein_noAtomicMass_twistedGeometricRemainder_unram (solution)
