-- Prove2me | solution 1 for AlgebraicCurve.exists_transcendental_mem_range_stalk_iff_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/b57086e8-4cc3-5dfa-9f78-2aab281d13d9

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicCurve_essFiniteType_functionField
import Theorems.Thm_AlgebraicCurve_exists_place_range_stalk_eq
import Theorems.Thm_AlgebraicCurve_eq_of_range_stalk_eq
import Theorems.Thm_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_AlgebraicCurve_Place_exists_not_mem_and_forall_ne_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_transcendental_mem_range_stalk_iff_ne
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

open CategoryTheory AlgebraicGeometry AlgebraicCurve

universe u

theorem solution
    {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (Q : C) (hQ : IsClosed ({Q} : Set C)) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    ∃ f : C.functionField, Transcendental K f ∧
      ∀ x : C, f ∈ (algebraMap (C.presheaf.stalk x) C.functionField).range ↔ x ≠ Q := by
  letI hKF : Algebra K C.functionField := (AlgebraicCurve.baseToFunctionField c).toAlgebra

  haveI : IsCurveOver K C.functionField :=
    AlgebraicCurve.isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one c
      (RingEquiv.refl _) (fun _ => rfl)
  haveI := SmoothOfRelativeDimension.smooth 1 c
  haveI : LocallyOfFiniteType c := inferInstance
  haveI : Algebra.EssFiniteType K C.functionField := AlgebraicCurve.essFiniteType_functionField c

  obtain ⟨vQ, hvQ⟩ := AlgebraicCurve.exists_place_range_stalk_eq c Q hQ
  have hC : ConstantsAreBase K C.functionField :=
    AlgebraicCurve.constantsAreBase_of_deg_eq_one vQ (IsCurveOver.deg_eq_one_of_isAlgClosed vQ)

  obtain ⟨f, hfQ, hfw⟩ := AlgebraicCurve.Place.exists_not_mem_and_forall_ne_mem hC vQ
  refine ⟨f, ?_, ?_⟩
  ·
    intro halg
    apply hfQ
    obtain ⟨a, ha⟩ := minpoly.mem_range_of_degree_eq_one K f
      (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible halg.isIntegral))
    rw [← ha]
    exact vQ.algebraMap_mem' a
  · intro x
    constructor
    · rintro hx rfl
      rw [hvQ] at hx
      exact hfQ hx
    · intro hx
      by_cases hxc : IsClosed ({x} : Set C)
      ·
        obtain ⟨vx, hvx⟩ := AlgebraicCurve.exists_place_range_stalk_eq c x hxc
        have hne : vx ≠ vQ := by
          intro h
          exact hx (AlgebraicCurve.eq_of_range_stalk_eq c x Q (by rw [hvx, hvQ, h]))
        show f ∈ (algebraMap (C.presheaf.stalk x) C.functionField).range
        rw [hvx]
        exact hfw vx hne
      ·
        have hxg : x = genericPoint C := by
          by_contra h
          exact hxc (AlgebraicCurve.isClosed_singleton_of_ne_genericPoint c x h)
        subst hxg
        refine ⟨f, ?_⟩
        change (C.presheaf.stalkSpecializes (genericPoint_specializes (genericPoint C))).hom f = f
        have : C.presheaf.stalkSpecializes (genericPoint_specializes (genericPoint C)) = 𝟙 _ :=
          TopCat.Presheaf.stalkSpecializes_refl _ _
        rw [this]
        rfl

end S_AlgebraicCurve_exists_transcendental_mem_range_stalk_iff_ne
end P2MW
export P2MW.S_AlgebraicCurve_exists_transcendental_mem_range_stalk_iff_ne (solution)
