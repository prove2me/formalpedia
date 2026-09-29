-- Prove2me | solution 1 for AlgebraicCurve.regularDiffs_eq_regularDifferentials_of_perfectField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/b104584e-12c3-5979-879c-1e38ea15b914

import Mathlib
import Definitions.Def_AlgebraicCurve_Differentials
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_AlgebraicCurve_Place_ordDiff_eq_ordDifferential_of_perfectField
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_regularDiffs_eq_regularDifferentials_of_perfectField
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

open AlgebraicCurve

namespace S33PF

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mem_iff_ord_nonneg (w : Place K F) {x : F} (hx : x ≠ 0) :
    x ∈ w.toValuationSubring ↔ 0 ≤ w.ord x := by
  rw [Place.mem_iff_adicValuation_le_one, Place.ord, neg_nonneg,
    WithZero.log_le_iff_le_exp (w.adicValuation_ne_zero hx), WithZero.exp_zero]

theorem mem_of_ord_nonneg (w : Place K F) {x : F} (h : 0 ≤ w.ord x) : x ∈ w.toValuationSubring := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_mem _
  · exact (mem_iff_ord_nonneg w hx).mpr h

theorem ord_nonneg_of_mem (w : Place K F) {x : F} (h : x ∈ w.toValuationSubring) : 0 ≤ w.ord x := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [Place.ord_zero]
  · exact (mem_iff_ord_nonneg w hx).mp h

theorem regularDiffs_eq [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F] :
    regularDiffs K F = regularDifferentials K F := by
  haveI hgen : ∀ v : Place K F, v.DCoordGenerates := AlgebraicCurve.dCoordGenerates_of_isCurveOver

  have key : ∀ (ω : Ω[F⁄K]) (v : Place K F),
      0 ≤ v.ordDiff ω ↔ ∃ f ∈ v.toValuationSubring, ω = f • v.dCoord := by
    intro ω v
    rw [AlgebraicCurve.Place.ordDiff_eq_ordDifferential_of_perfectField v ω]
    constructor
    · intro h
      exact ⟨v.differentialCoeff ω, mem_of_ord_nonneg v h, (v.differentialCoeff_smul_dCoord ω).symm⟩
    · rintro ⟨f, hf, rfl⟩
      show 0 ≤ v.ord (v.differentialCoeff (f • v.dCoord))
      rw [v.differentialCoeff_unique (rfl : f • v.dCoord = f • v.dCoord)]
      exact ord_nonneg_of_mem v hf
  apply le_antisymm
  · rw [regularDiffs_eq_span]
    refine Submodule.span_le.mpr (fun ω hω => ?_)
    rw [SetLike.mem_coe, mem_regularDifferentials_iff]
    exact fun v => (key ω v).mp (hω v)
  · intro ω hω
    rw [mem_regularDifferentials_iff] at hω
    exact mem_regularDiffs_of_isRegularDiff (fun v => (key ω v).mpr (hω v))

end S33PF

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F]
    [PerfectField K] [Algebra.EssFiniteType K F] [AlgebraicCurve.IsCurveOver K F] :
    AlgebraicCurve.regularDiffs K F = AlgebraicCurve.regularDifferentials K F := by
  exact S33PF.regularDiffs_eq

end S_AlgebraicCurve_regularDiffs_eq_regularDifferentials_of_perfectField
end P2MW
export P2MW.S_AlgebraicCurve_regularDiffs_eq_regularDifferentials_of_perfectField (solution)
