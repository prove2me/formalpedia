-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.isPrincipal_sub_single_of_presentation_ker_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/2e68b72b-7321-5aa0-b709-fb393b919caf

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicCurve_RelCartier
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_exists_divisor_range_invModule_eq_lSpaceOn
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_exists_divisor_range_module_eq_lSpaceOn
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_ord_eq_of_ker_pow_ideal_eq_span
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_eq_mul_and_eq_add_ord_of_presentations
import Theorems.Thm_AlgebraicCurve_exists_closedPoint_range_stalk_eq
import Theorems.Thm_AlgebraicCurve_eq_of_range_stalk_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_range_moduleIota_app_and_injective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_isPrincipal_sub_single_of_presentation_ker_pow
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback SheafOfModules.isIso_ihomModelToIhom AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_isPrincipal_sub_single_of_presentation_ker_pow.AlgebraicGeometry Opposite TopologicalSpace"

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension IsProper Scheme.Hom Spec IsIntegral Scheme IsAffineOpen Scheme.Modules Scheme.IdealSheafData Scheme.IdealSheafData.IsInvertible Scheme.IdealSheafData.IsInvertible.exists_divisor_range_invModule_eq_lSpaceOn Scheme.IdealSheafData.IsInvertible.exists_divisor_range_module_eq_lSpaceOn Scheme.Hom.ord_eq_of_ker_pow_ideal_eq_span Scheme.Modules.exists_eq_mul_and_eq_add_ord_of_presentations Scheme.Hom.isInvertible_ker_of_comp_eq_id Scheme.IdealSheafData.range_moduleIota_app_and_injective" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Hom Γ functionField affineBasicOpen Modules Opens IdealSheafData IdealSheafData.IsInvertible IdealSheafData.IsInvertible.exists_divisor_range_invModule_eq_lSpaceOn IdealSheafData.IsInvertible.exists_divisor_range_module_eq_lSpaceOn Hom.ord_eq_of_ker_pow_ideal_eq_span Modules.exists_eq_mul_and_eq_add_ord_of_presentations Hom.isInvertible_ker_of_comp_eq_id IdealSheafData.range_moduleIota_app_and_injective" namespace Modules p2m_export "AlgebraicGeometry.Scheme.Modules" "presheaf Hom IsInvertible toUnitSection ofUnitSection_injective exists_eq_mul_and_eq_add_ord_of_presentations" end AlgebraicGeometry.Scheme.Modules
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules" in
open _root_.AlgebraicGeometry.Scheme.Modules AlgebraicCurve _root_.CategoryTheory.MonoidalCategory in

theorem AlgebraicGeometry.Scheme.Modules.isPrincipal_sub_single_of_presentation_ker_pow'
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x]
    (P : Spec (CommRingCat.of K) ⟶ X) (hP : P ≫ x = 𝟙 _) (n : ℕ)
    (v : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Place K X.functionField)
    (hv : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      (algebraMap (X.presheaf.stalk (P.base (IsLocalRing.closedPoint K))) X.functionField).range =
        v.toValuationSubring.toSubring)
    (D D' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Divisor K X.functionField)
    (φ : ∀ U : X.Opens, Γ((P.ker ^ n).invModule, U) →+ (X.functionField : Type u))
    (hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ((P.ker ^ n).invModule, U), φ V (((P.ker ^ n).invModule).presheaf.map (homOfLE h).op m) = φ U m)
    (hsmul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ((P.ker ^ n).invModule, U)),
      φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m)
    (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))
    (hrange : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D : Set X.functionField))
    (φ' : ∀ U : X.Opens, Γ((P.ker ^ n).module, U) →+ (X.functionField : Type u))
    (hnat' : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ((P.ker ^ n).module, U), φ' V (((P.ker ^ n).module).presheaf.map (homOfLE h).op m) = φ' U m)
    (hsmul' : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ((P.ker ^ n).module, U)),
      φ' U (a • m) = algebraMap Γ(X, U) X.functionField a * φ' U m)
    (hinj' : ∀ U : X.Opens, Nonempty U → Function.Injective (φ' U))
    (hrange' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ' U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D' : Set X.functionField)) :
    letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    AlgebraicCurve.Divisor.IsPrincipal (D - n • Finsupp.single v 1) ∧
      AlgebraicCurve.Divisor.IsPrincipal (D' + n • Finsupp.single v 1) := by
  classical
  letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
  set pt : X := P.base (IsLocalRing.closedPoint K) with hpt
  have hI : (P.ker ^ n).IsInvertible := (Scheme.Hom.isInvertible_ker_of_comp_eq_id P hP).pow n

  have hplace : ∀ (y : X) (w : Place K X.functionField),
      (algebraMap (X.presheaf.stalk y) X.functionField).range = w.toValuationSubring.toSubring →
      ((pt = y → w = v) ∧ (pt ≠ y → w ≠ v)) := by
    intro y w hw
    constructor
    · rintro rfl
      apply Place.ext
      apply ValuationSubring.toSubring_injective
      exact hw.symm.trans hv
    · intro hne heq
      apply hne
      subst heq
      exact (eq_of_range_stalk_eq x pt y (hv.trans hw.symm))

  have hcoef : ∀ (U : X.Opens) (hU : IsAffineOpen U) (g : Γ(X, U)) (y : X) (hyU : y ∈ U), IsClosed ({y} : Set X) →
      (P.ker ^ n).ideal ⟨U, hU⟩ = Ideal.span {g} →
      ∀ w : Place K X.functionField,
        (algebraMap (X.presheaf.stalk y) X.functionField).range = w.toValuationSubring.toSubring →
        haveI : Nonempty U := ⟨⟨y, hyU⟩⟩
        ((n • Finsupp.single v (1 : ℤ) : Divisor K X.functionField) w : ℤ) =
          w.ord (algebraMap Γ(X, U) X.functionField g) := by
    intro U hU g y hyU hy hg w hw
    haveI : Nonempty U := ⟨⟨y, hyU⟩⟩
    have hord := Scheme.Hom.ord_eq_of_ker_pow_ideal_eq_span x P hP n U hU g hg y hyU hy w hw
    obtain ⟨h1, h2⟩ := hplace y w hw
    simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, nsmul_eq_mul]
    by_cases hyp : pt = y
    · rw [hord.1 hyp, if_pos (h1 hyp).symm, mul_one]
    · rw [hord.2 hyp, if_neg (fun h => h2 hyp h.symm), mul_zero]
  constructor
  ·
    obtain ⟨D₀, φ₀, ⟨h1, h2, h3, h4, h5⟩, hf, hpin⟩ :=
      Scheme.IdealSheafData.IsInvertible.exists_divisor_range_invModule_eq_lSpaceOn x hI
    have hsec : ∃ (U : X.Opens) (m : Γ((P.ker ^ n).invModule, U)), m ≠ 0 :=
      ⟨⊤, (P.ker ^ n).invModuleSection.app ⊤ (toUnitSection ⊤ 1), fun h => hf (by rw [h, map_zero])⟩
    obtain ⟨g₁, hg₁, -, hDw, -⟩ := Scheme.Modules.exists_eq_mul_and_eq_add_ord_of_presentations x _ D D₀ φ φ₀
      hnat h1 hsmul h2 hinj h3 hrange h4 hsec
    refine ⟨g₁ * (φ₀ ⊤ ((P.ker ^ n).invModuleSection.app ⊤ (toUnitSection ⊤ 1)))⁻¹,
      mul_ne_zero hg₁ (inv_ne_zero hf), fun w => ?_⟩
    obtain ⟨y, hy, hw⟩ := exists_closedPoint_range_stalk_eq x w
    obtain ⟨U, r, hyr, g, -, hIg⟩ := hI y
    have hc := hcoef (X.affineBasicOpen r) (X.affineBasicOpen r).2 g y hyr hy hIg w hw
    have hp := hpin (X.affineBasicOpen r) (X.affineBasicOpen r).2 g y hyr hy hIg w hw
    simp only [Finsupp.coe_sub, Pi.sub_apply]
    rw [hc, hDw w, Place.ord_mul _ hg₁ (inv_ne_zero hf), Place.ord_inv]
    haveI : Nonempty (X.affineBasicOpen r : X.Opens) := ⟨⟨y, hyr⟩⟩
    have hp' : D₀ w + w.ord (φ₀ ⊤ ((P.ker ^ n).invModuleSection.app ⊤ (toUnitSection ⊤ 1))) =
        w.ord (algebraMap Γ(X, X.affineBasicOpen r) X.functionField g) := hp
    change D₀ w + w.ord g₁ - _ = _
    omega
  ·
    obtain ⟨D₀, φ₀, ⟨h1, h2, h3, h4, h5⟩, c, hc0, hcφ, hpin⟩ :=
      Scheme.IdealSheafData.IsInvertible.exists_divisor_range_module_eq_lSpaceOn x hI

    have hsec : ∃ (U : X.Opens) (m : Γ((P.ker ^ n).module, U)), m ≠ 0 := by
      obtain ⟨U, r, hηr, g, hgnz, hIg⟩ := hI (genericPoint X)
      haveI : Nonempty (X.affineBasicOpen r : X.Opens) := ⟨⟨genericPoint X, hηr⟩⟩
      have hrg := (Scheme.IdealSheafData.range_moduleIota_app_and_injective (P.ker ^ n) (X.affineBasicOpen r)).1
      have hgmem : (toUnitSection (X.affineBasicOpen r) g) ∈ Set.range ((P.ker ^ n).moduleι.app (X.affineBasicOpen r)) := by
        rw [hrg, hIg]
        exact Ideal.mem_span_singleton_self g
      obtain ⟨m, hm⟩ := hgmem
      refine ⟨X.affineBasicOpen r, m, fun h0 => ?_⟩
      rw [h0, map_zero] at hm
      have : g = 0 := (ofUnitSection_injective _ hm).symm
      exact nonZeroDivisors.ne_zero hgnz this
    obtain ⟨g₂, hg₂, -, hDw, -⟩ := Scheme.Modules.exists_eq_mul_and_eq_add_ord_of_presentations x _ D' D₀ φ' φ₀
      hnat' h1 hsmul' h2 hinj' h3 hrange' h4 hsec
    refine ⟨g₂ * c⁻¹, mul_ne_zero hg₂ (inv_ne_zero hc0), fun w => ?_⟩
    obtain ⟨y, hy, hw⟩ := exists_closedPoint_range_stalk_eq x w
    obtain ⟨U, r, hyr, g, -, hIg⟩ := hI y
    have hc := hcoef (X.affineBasicOpen r) (X.affineBasicOpen r).2 g y hyr hy hIg w hw
    have hp := hpin (X.affineBasicOpen r) (X.affineBasicOpen r).2 g y hyr hy hIg w hw
    simp only [Finsupp.coe_add, Pi.add_apply]
    rw [hc, hDw w, Place.ord_mul _ hg₂ (inv_ne_zero hc0), Place.ord_inv]
    haveI : Nonempty (X.affineBasicOpen r : X.Opens) := ⟨⟨y, hyr⟩⟩
    change D₀ w + w.ord g₂ + _ = _
    have hp' : D₀ w + w.ord c + w.ord (algebraMap Γ(X, X.affineBasicOpen r) X.functionField g) = 0 := hp
    omega

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_isPrincipal_sub_single_of_presentation_ker_pow.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory in
theorem solution
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x]
    (P : Spec (CommRingCat.of K) ⟶ X) (hP : P ≫ x = 𝟙 _) (n : ℕ)
    (v : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Place K X.functionField)
    (hv : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      (algebraMap (X.presheaf.stalk (P.base (IsLocalRing.closedPoint K))) X.functionField).range =
        v.toValuationSubring.toSubring)
    (D D' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Divisor K X.functionField)
    (φ : ∀ U : X.Opens, Γ((P.ker ^ n).invModule, U) →+ (X.functionField : Type u))
    (hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ((P.ker ^ n).invModule, U), φ V (((P.ker ^ n).invModule).presheaf.map (homOfLE h).op m) = φ U m)
    (hsmul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ((P.ker ^ n).invModule, U)),
      φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m)
    (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))
    (hrange : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D : Set X.functionField))
    (φ' : ∀ U : X.Opens, Γ((P.ker ^ n).module, U) →+ (X.functionField : Type u))
    (hnat' : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ((P.ker ^ n).module, U), φ' V (((P.ker ^ n).module).presheaf.map (homOfLE h).op m) = φ' U m)
    (hsmul' : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ((P.ker ^ n).module, U)),
      φ' U (a • m) = algebraMap Γ(X, U) X.functionField a * φ' U m)
    (hinj' : ∀ U : X.Opens, Nonempty U → Function.Injective (φ' U))
    (hrange' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ' U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D' : Set X.functionField)) :
    letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    AlgebraicCurve.Divisor.IsPrincipal (D - n • Finsupp.single v 1) ∧
      AlgebraicCurve.Divisor.IsPrincipal (D' + n • Finsupp.single v 1) :=
  AlgebraicGeometry.Scheme.Modules.isPrincipal_sub_single_of_presentation_ker_pow' x P hP n v hv D D' φ hnat hsmul hinj
    hrange φ' hnat' hsmul' hinj' hrange'

end S_AlgebraicGeometry_Scheme_Modules_isPrincipal_sub_single_of_presentation_ker_pow
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_isPrincipal_sub_single_of_presentation_ker_pow (solution)
