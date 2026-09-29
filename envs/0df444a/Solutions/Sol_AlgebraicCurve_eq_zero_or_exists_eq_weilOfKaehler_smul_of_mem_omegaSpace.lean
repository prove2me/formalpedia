-- Prove2me | solution 1 for AlgebraicCurve.eq_zero_or_exists_eq_weilOfKaehler_smul_of_mem_omegaSpace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/05b33101-8b69-522f-ae06-225c1c84d961

import Mathlib
import Definitions.Def_AlgebraicCurve_WeilOfKaehler
import Definitions.Def_AlgebraicCurve_SerrePairing
import Definitions.Def_AlgebraicCurve_RiemannRochRows
import Theorems.Thm_AlgebraicCurve_exists_weilSmul_eq_of_riemannIndexFormula
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_eq_zero_or_exists_eq_weilOfKaehler_smul_of_mem_omegaSpace
p2m_attr_erase "instance" "AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul"
p2m_attr_erase "simp" "ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option autoImplicit false
set_option maxHeartbeats 3200000

open AlgebraicCurve

namespace ModularCurve
namespace OmegaSide
namespace A

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem kaehlerResidueTerm_smulF_left [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    [HasCanonicalLocalResidueKStar K F]
    (f : F) (ω : Ω[F⁄K]) (α : Place K F → F) (v : Place K F) :
    kaehlerResidueTerm (f • ω) α v = kaehlerResidueTerm ω (mulAdele K f α) v := by
  unfold kaehlerResidueTerm
  rw [v.differentialCoeff_smul, mulAdele_apply]
  ring_nf

theorem weilOfKaehler_smulF [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    [HasCanonicalLocalResidueKStar K F] [HasPrincipalDivisors K F] [HasCanonicalDivisor (K := K) (F := F)]
    {f : F} {ω : Ω[F⁄K]} (hω : ω ≠ 0) (hf : f ≠ 0) :
    weilOfKaehler K F (ω := f • ω) (smul_ne_zero hf hω) = weilSmul K F f (weilOfKaehler K F hω) := by
  apply LinearMap.ext
  intro α
  rw [weilSmul_apply, weilOfKaehler_apply, weilOfKaehler_apply]
  refine finsum_congr fun v => ?_
  rw [kaehlerResidueTerm_smulF_left, adeleSpaceMul_coe]

theorem eq_zero_or_exists_eq_weilOfKaehler_smul'
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)] [Nonempty (Place K F)]
    [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]] [HasCanonicalLocalResidueKStar K F]
    (hRI : RiemannIndexFormula K F) (hagree : WeilKaehlerAgree K F)
    {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) (D : Divisor K F)
    (μ : Module.Dual K (adeleSpace K F)) (hμ : μ ∈ omegaSpace (K := K) (F := F) D) :
    μ = 0 ∨ ∃ (f : F) (hf : f ≠ 0), μ = weilOfKaehler K F (ω := f • ω₀) (smul_ne_zero hf hω₀) := by
  classical
  haveI : HasPrincipalDivisors K F := IsCurveOver.hasPrincipalDivisors
  obtain ⟨hl0, hlmem, hlmax⟩ := hagree hω₀
  set W₀ := canonicalDivisorOf hω₀

  have h1 : omegaSpace (K := K) (F := F) W₀ ≤ omegaSpace (W₀ ⊓ D) := omegaSpace_antitone inf_le_left
  have h2 : omegaSpace (K := K) (F := F) D ≤ omegaSpace (W₀ ⊓ D) := omegaSpace_antitone inf_le_right
  obtain ⟨f, hf⟩ := exists_weilSmul_eq_of_riemannIndexFormula hRI (h1 hlmem) (h2 hμ) hl0
  by_cases hf0 : f = 0
  · left
    rw [hf, hf0]
    apply LinearMap.ext; intro α
    rw [weilSmul_apply, LinearMap.zero_apply]
    have : adeleSpaceMul K F (0 : F) α = 0 := by
      apply Subtype.ext; rw [adeleSpaceMul_coe]; funext v; simp [mulAdele_apply]
    rw [this, map_zero]
  · right
    exact ⟨f, hf0, by rw [weilOfKaehler_smulF hω₀ hf0, hf]⟩

end ModularCurve.OmegaSide.A

open ModularCurve.OmegaSide.A in
theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)] [Nonempty (Place K F)]
    [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]] [HasCanonicalLocalResidueKStar K F]
    (hRI : RiemannIndexFormula K F) (hagree : WeilKaehlerAgree K F)
    {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) (D : Divisor K F)
    (μ : Module.Dual K (adeleSpace K F)) (hμ : μ ∈ omegaSpace (K := K) (F := F) D) :
    μ = 0 ∨ ∃ (f : F) (hf : f ≠ 0), μ = weilOfKaehler K F (ω := f • ω₀) (smul_ne_zero hf hω₀) :=
  eq_zero_or_exists_eq_weilOfKaehler_smul' hRI hagree hω₀ D μ hμ

end S_AlgebraicCurve_eq_zero_or_exists_eq_weilOfKaehler_smul_of_mem_omegaSpace
end P2MW
export P2MW.S_AlgebraicCurve_eq_zero_or_exists_eq_weilOfKaehler_smul_of_mem_omegaSpace (solution)
