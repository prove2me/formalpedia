-- Prove2me | solution 1 for AlgebraicCurve.exists_curveModel_iso_of_algEquiv_functionField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/46833b96-b8a4-555b-bbaa-b56d5b802157

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_curveModel_iso_germToFunctionField_eq_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_CurveModel_exists_curveModel_iso_ffEquiv_symm_germToFunctionField_eq_of_algEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_curveModel_iso_of_algEquiv_functionField
p2m_attr_erase "instance" "AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply"
p2m_attr_erase "simp" "ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry AlgebraicCurve P2MW.S_AlgebraicCurve_exists_curveModel_iso_of_algEquiv_functionField.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "baseToFunctionField CurveModel CurveModel.exists_curveModel_iso_ffEquiv_symm_germToFunctionField_eq_of_algEquiv"
namespace ModelIso
p2m_open "AlgebraicCurve"

theorem nonempty_preimage_of_iso {X Y : Scheme.{0}} (e : X ≅ Y) (U : Y.Opens) [h : Nonempty (Scheme.Opens.toScheme U)] :
    Nonempty (Scheme.Opens.toScheme (e.hom ⁻¹ᵁ U)) := by
  obtain ⟨⟨y, hy⟩⟩ := h
  refine ⟨⟨e.inv.base y, ?_⟩⟩
  show (e.inv ≫ e.hom).base y ∈ (U : Set Y)
  rw [e.inv_hom_id]
  exact hy

end AlgebraicCurve.ModelIso

open AlgebraicCurve.ModelIso

theorem solution
    (k : Type) [Field k] [IsAlgClosed k] (Y : Scheme.{0}) (πY : Y ⟶ Spec (CommRingCat.of k))
    [IsIntegral Y] [IsProper πY] [SmoothOfRelativeDimension 1 πY]
    (L : Type) [Field L] [Algebra k L]
    (ι : L ≃+* Y.functionField) (hι : ∀ a : k, ι (algebraMap k L a) = baseToFunctionField πY a) :
    ∃ (M : CurveModel k L) (e : M.C ≅ Y), e.hom ≫ πY = M.toBase ∧
      ∀ (U : Y.Opens) [Nonempty (Scheme.Opens.toScheme U)] [Nonempty (Scheme.Opens.toScheme (e.hom ⁻¹ᵁ U))]
        (t : Γ(Y, U)),
        M.ffEquiv.symm (M.C.germToFunctionField (e.hom ⁻¹ᵁ U) ((e.hom.app U).hom t)) = ι.symm (Y.germToFunctionField U t) := by
  letI alg : Algebra k Y.functionField := (baseToFunctionField πY).toAlgebra
  obtain ⟨-, -, M₀, e₀, he₀, hgerm₀⟩ :=
    AlgebraicGeometry.SmoothProperCurve.exists_curveModel_iso_germToFunctionField_eq_of_isAlgClosed k Y πY
  let ιA : Y.functionField ≃ₐ[k] L :=
    AlgEquiv.ofRingEquiv (f := ι.symm) (fun a => by rw [RingEquiv.symm_apply_eq]; exact (hι a).symm)
  obtain ⟨M, f, hf, hgermf⟩ :=
    AlgebraicCurve.CurveModel.exists_curveModel_iso_ffEquiv_symm_germToFunctionField_eq_of_algEquiv ιA M₀
  refine ⟨M, f ≪≫ e₀, ?_, ?_⟩
  · rw [Iso.trans_hom, Category.assoc, he₀, hf]
  · intro U hU hU' t
    haveI : Nonempty (Scheme.Opens.toScheme (e₀.hom ⁻¹ᵁ U)) := nonempty_preimage_of_iso e₀ U
    haveI : Nonempty (Scheme.Opens.toScheme (f.hom ⁻¹ᵁ (e₀.hom ⁻¹ᵁ U))) := nonempty_preimage_of_iso f _
    have h1 := hgermf (e₀.hom ⁻¹ᵁ U) ((e₀.hom.app U).hom t)
    have h2 := hgerm₀ U t
    rw [h2] at h1
    convert h1 using 2 <;> first | rfl | simp [ιA]

end S_AlgebraicCurve_exists_curveModel_iso_of_algEquiv_functionField
end P2MW
export P2MW.S_AlgebraicCurve_exists_curveModel_iso_of_algEquiv_functionField (solution)
