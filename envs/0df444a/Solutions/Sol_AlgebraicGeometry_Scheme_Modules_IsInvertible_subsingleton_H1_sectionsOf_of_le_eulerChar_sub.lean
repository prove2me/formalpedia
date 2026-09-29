-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.subsingleton_H1_sectionsOf_of_le_eulerChar_sub
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/5ad8bbff-8b74-5da0-9e60-e4f0a5eda9cf

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicCurve_PlacesOf
import Theorems.Thm_AlgebraicCurve_nonempty_linearEquiv_cechH0_and_cechH1_sectionsOf
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_unit_equiv_structureSheafSections
import Theorems.Thm_AlgebraicCurve_nonempty_linearEquiv_cechH0_and_cechH1
import Theorems.Thm_AlgebraicCurve_placesOf_union_eq_univ_of_sup_eq_top
import Theorems.Thm_AlgebraicGeometry_not_isAffine_of_isProper_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicCurve_essFiniteType_functionField
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_indexOfSpecialty_eq_of_genusReached
import Theorems.Thm_AlgebraicCurve_cechRiemannRoch_of_genusReached
import Theorems.Thm_AlgebraicCurve_ell_eq_zero_of_degree_neg
import Theorems.Thm_AlgebraicCurve_exists_canonicalDivisor_genus_riemannRoch
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_subsingleton_H1_sectionsOf_of_le_eulerChar_sub
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor Divisor.degree Divisor.degree_single H1 IsCurveOver IsCurveOver.deg_eq_one_of_isAlgClosed ell ConstantsAreBase ell_zero_eq_one_of_constantsAreBase indexOfSpecialty baseToFunctionField cechH0 cechH1 placesOf nonempty_linearEquiv_cechH0_and_cechH1_sectionsOf nonempty_linearEquiv_cechH0_and_cechH1 placesOf_union_eq_univ_of_sup_eq_top isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one essFiniteType_functionField constantsAreBase_of_deg_eq_one stichtenothGenusExists_of_isCurveOver indexOfSpecialty_eq_of_genusReached cechRiemannRoch_of_genusReached ell_eq_zero_of_degree_neg exists_canonicalDivisor_genus_riemannRoch"
p2m_open "AlgebraicCurve~genus"
open CategoryTheory AlgebraicGeometry TopologicalSpace

theorem ne_top_of_isAffineOpen_e9 {C : Scheme.{u}} (hC : ¬ IsAffine C) {U : C.Opens}
    (hU : IsAffineOpen U) : U ≠ ⊤ := by
  intro h
  apply hC
  have hT : IsAffineOpen (⊤ : C.Opens) := h ▸ hU
  haveI : IsAffine (⊤ : C.Opens) := hT
  exact IsAffine.of_isIso C.topIso.inv

theorem subsingleton_H1_sectionsOf_of_le_eulerChar_sub'
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x]
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) (𝒱 : X.TwoAffineOpenCover)
    (h : 2 * (Module.finrank K (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H1 : ℤ) - 1
        ≤ ((Module.finrank K (𝒱.sectionsOf x M).H0 : ℤ) - Module.finrank K (𝒱.sectionsOf x M).H1)
          - ((Module.finrank K (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H0 : ℤ)
              - Module.finrank K (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H1)) :
    Subsingleton (𝒱.sectionsOf x M).H1 := by
  letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
  haveI hcurve : IsCurveOver K X.functionField :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one x (RingEquiv.refl _) (fun _ => rfl)
  haveI : Algebra.EssFiniteType K X.functionField := essFiniteType_functionField x
  have hNA := not_isAffine_of_isProper_of_smoothOfRelativeDimension_one x
  have hne0 : 𝒱.U0 ≠ ⊤ := ne_top_of_isAffineOpen_e9 hNA 𝒱.isAffineOpen_U0
  have hne1 : 𝒱.U1 ≠ ⊤ := ne_top_of_isAffineOpen_e9 hNA 𝒱.isAffineOpen_U1

  have h0 : Nonempty 𝒱.U0 := by
    by_contra hc
    apply hne1
    have hb : 𝒱.U0 = ⊥ := by
      ext z
      simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hz => hc ⟨⟨z, hz⟩⟩
    have := 𝒱.sup_eq_top
    rwa [hb, bot_sup_eq] at this
  have h1 : Nonempty 𝒱.U1 := by
    by_contra hc
    apply hne0
    have hb : 𝒱.U1 = ⊥ := by
      ext z
      simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hz => hc ⟨⟨z, hz⟩⟩
    have := 𝒱.sup_eq_top
    rwa [hb, sup_bot_eq] at this
  obtain ⟨hcov, hS0, hS1⟩ :=
    placesOf_union_eq_univ_of_sup_eq_top x 𝒱.U0 𝒱.U1 𝒱.sup_eq_top hne0 hne1
  obtain ⟨v₀, hv₀⟩ := hS0
  haveI : Nonempty (Place K X.functionField) := ⟨v₀⟩
  have hC : ConstantsAreBase K X.functionField :=
    constantsAreBase_of_deg_eq_one v₀ (IsCurveOver.deg_eq_one_of_isAlgClosed v₀)
  have hℓ0 : ell (0 : Divisor K X.functionField) = 1 := ell_zero_eq_one_of_constantsAreBase hC
  obtain ⟨-, hL0, γ, E₀, hγ⟩ := stichtenothGenusExists_of_isCurveOver hC
  haveI := hL0

  obtain ⟨Kc, g, hRR⟩ := exists_canonicalDivisor_genus_riemannRoch K X.functionField
  have hdeg1 : (1 : ℤ) ≤ v₀.deg := by exact_mod_cast (IsCurveOver.deg_eq_one_of_isAlgClosed v₀).ge
  have hγg : γ = g := by
    apply le_antisymm
    · have h1 := hRR E₀
      have h2 := hγ.eq
      have h3 : (0 : ℤ) ≤ ell (Kc - E₀) := by exact_mod_cast Nat.zero_le _
      omega
    · let E : Divisor K X.functionField := Kc + Finsupp.single v₀ 1
      have hKE : Divisor.degree (Kc - E) < 0 := by
        simp only [E, sub_add_cancel_left, map_neg, Divisor.degree_single, one_mul]
        omega
      have h1 := hRR E
      rw [ell_eq_zero_of_degree_neg hKE, Nat.cast_zero, sub_zero] at h1
      have h2 := hγ.isMax E
      omega
  have hKc : Divisor.degree Kc = 2 * g - 2 := by
    have h1 := hRR Kc
    have h2 := hRR 0
    simp only [sub_self, sub_zero, map_zero, hℓ0] at h1 h2
    omega

  obtain ⟨D, ⟨eM0⟩, ⟨eM1⟩⟩ := nonempty_linearEquiv_cechH0_and_cechH1_sectionsOf 𝒱 x h0 h1 M hM
  obtain ⟨hfin0, hfin1, hrk0, hrk1, hchi, -⟩ := cechRiemannRoch_of_genusReached hγ hcov ⟨v₀, hv₀⟩ hS1 D

  obtain ⟨eO0, eO1, -, -⟩ := Scheme.TwoAffineOpenCover.exists_sectionsOf_unit_equiv_structureSheafSections 𝒱 x
  obtain ⟨⟨eS0⟩, ⟨eS1⟩⟩ := nonempty_linearEquiv_cechH0_and_cechH1 𝒱 x h0 h1
  obtain ⟨-, -, hrk0', hrk1', hchi', -⟩ :=
    cechRiemannRoch_of_genusReached hγ hcov ⟨v₀, hv₀⟩ hS1 (0 : Divisor K X.functionField)

  have eqM0 : Module.finrank K (𝒱.sectionsOf x M).H0 = Module.finrank K ↥(cechH0 (placesOf x 𝒱.U0) (placesOf x 𝒱.U1) D) :=
    eM0.finrank_eq
  have eqM1 : Module.finrank K (𝒱.sectionsOf x M).H1 = Module.finrank K (cechH1 (placesOf x 𝒱.U0) (placesOf x 𝒱.U1) D) :=
    eM1.finrank_eq
  have eqO0 : Module.finrank K (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H0
      = Module.finrank K ↥(cechH0 (placesOf x 𝒱.U0) (placesOf x 𝒱.U1) (0 : Divisor K X.functionField)) :=
    (eO0.trans eS0).finrank_eq
  have eqO1 : Module.finrank K (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H1
      = Module.finrank K (cechH1 (placesOf x 𝒱.U0) (placesOf x 𝒱.U1) (0 : Divisor K X.functionField)) :=
    (eO1.trans eS1).finrank_eq
  rw [eqM0, eqM1, eqO0, eqO1] at h
  rw [hrk0', hℓ0, map_zero] at hchi'
  have hdeg : 2 * γ - 1 ≤ Divisor.degree D := by
    push_cast at h hchi hchi'
    omega

  have hKD : Divisor.degree (Kc - D) < 0 := by
    rw [map_sub, hKc]
    omega
  have hℓD : (ell D : ℤ) = Divisor.degree D + 1 - g := by
    have h1 := hRR D
    rw [ell_eq_zero_of_degree_neg hKD, Nat.cast_zero, sub_zero] at h1
    exact h1
  have hiD : indexOfSpecialty D = 0 := by
    have h1 := (indexOfSpecialty_eq_of_genusReached hγ D).2
    have : (indexOfSpecialty D : ℤ) = 0 := by rw [h1]; omega
    exact_mod_cast this
  haveI : Module.Finite K (cechH1 (placesOf x 𝒱.U0) (placesOf x 𝒱.U1) D) := hfin1
  haveI hsub : Subsingleton (cechH1 (placesOf x 𝒱.U0) (placesOf x 𝒱.U1) D) :=
    Module.finrank_zero_iff.mp (hrk1.trans hiD)
  exact eM1.toEquiv.subsingleton

end AlgebraicCurve

p2m_open "AlgebraicCurve~genus" in open _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_subsingleton_H1_sectionsOf_of_le_eulerChar_sub.AlgebraicCurve in
theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x]
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) (𝒱 : X.TwoAffineOpenCover)
    (h : 2 * (Module.finrank K (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H1 : ℤ) - 1
        ≤ ((Module.finrank K (𝒱.sectionsOf x M).H0 : ℤ) - Module.finrank K (𝒱.sectionsOf x M).H1)
          - ((Module.finrank K (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H0 : ℤ)
              - Module.finrank K (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H1)) :
    Subsingleton (𝒱.sectionsOf x M).H1 :=
  subsingleton_H1_sectionsOf_of_le_eulerChar_sub' K x M hM 𝒱 h

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_subsingleton_H1_sectionsOf_of_le_eulerChar_sub
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_subsingleton_H1_sectionsOf_of_le_eulerChar_sub (solution)
