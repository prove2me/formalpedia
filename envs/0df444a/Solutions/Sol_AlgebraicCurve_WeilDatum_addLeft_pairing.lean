-- Prove2me | solution 1 for AlgebraicCurve.WeilDatum.addLeft_pairing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/9d7fb20b-3a8e-5b44-94de-04f7100f38fb

import Definitions.Def_AlgebraicCurve_WeilDatum
import Theorems.Thm_AlgebraicCurve_Place_evalAt_ne_zero
import Theorems.Thm_AlgebraicCurve_Divisor_evalFun_ne_zero
import Theorems.Thm_AlgebraicCurve_Divisor_evalFun_mul
import Theorems.Thm_AlgebraicCurve_Divisor_evalFun_add
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_of_ord_nonneg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_WeilDatum_addLeft_pairing
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_WeilDatum_addLeft_pairing.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "WeilDatum WeilDatum.pairing Divisor.evalFun Place Divisor Place.evalAt_ne_zero Divisor.evalFun_ne_zero Divisor.evalFun_mul Divisor.evalFun_add"
namespace WeilDatum
p2m_export "AlgebraicCurve.WeilDatum" "pairing addLeft f₁ ord_f₁ D₁ f₁_ne_zero disjoint ord_f₂ D₂ f₂_ne_zero f₂ rational"
p2m_open "AlgebraicCurve.WeilDatum AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ} (d : WeilDatum K F n)

private theorem _root_.AlgebraicCurve.WeilDatum.ord_f₁_eq_zero_of_mem_support' {v : Place K F} (hv : v ∈ d.D₂.support) :
    v.ord d.f₁ = 0 := by
  rw [d.ord_f₁ v, (d.disjoint v).resolve_right (Finsupp.mem_support_iff.mp hv), mul_zero]

p2m_export "AlgebraicCurve.WeilDatum" "ord_f₁_eq_zero_of_mem_support'"
private theorem _root_.AlgebraicCurve.WeilDatum.ord_f₂_eq_zero_of_mem_support' {v : Place K F} (hv : v ∈ d.D₁.support) :
    v.ord d.f₂ = 0 := by
  rw [d.ord_f₂ v, (d.disjoint v).resolve_left (Finsupp.mem_support_iff.mp hv), mul_zero]

p2m_export "AlgebraicCurve.WeilDatum" "ord_f₂_eq_zero_of_mem_support'"
private theorem _root_.AlgebraicCurve.WeilDatum.rational_of_mem_support_left' {v : Place K F} (hv : v ∈ d.D₁.support) :
    v.IsRational :=
  d.rational v (Or.inl (Finsupp.mem_support_iff.mp hv))

p2m_export "AlgebraicCurve.WeilDatum" "rational_of_mem_support_left'"
private theorem _root_.AlgebraicCurve.WeilDatum.rational_of_mem_support_right' {v : Place K F} (hv : v ∈ d.D₂.support) :
    v.IsRational :=
  d.rational v (Or.inr (Finsupp.mem_support_iff.mp hv))

p2m_export "AlgebraicCurve.WeilDatum" "rational_of_mem_support_right'"
private theorem _root_.AlgebraicCurve.WeilDatum.evalAt_f₁_ne_zero' {v : Place K F} (hv : v ∈ d.D₂.support) :
    v.evalAt d.f₁ ≠ 0 :=
  AlgebraicCurve.Place.evalAt_ne_zero v (d.rational_of_mem_support_right' hv) d.f₁_ne_zero
    (d.ord_f₁_eq_zero_of_mem_support' hv)

p2m_export "AlgebraicCurve.WeilDatum" "evalAt_f₁_ne_zero'"
private theorem _root_.AlgebraicCurve.WeilDatum.evalAt_f₂_ne_zero' {v : Place K F} (hv : v ∈ d.D₁.support) :
    v.evalAt d.f₂ ≠ 0 :=
  AlgebraicCurve.Place.evalAt_ne_zero v (d.rational_of_mem_support_left' hv) d.f₂_ne_zero
    (d.ord_f₂_eq_zero_of_mem_support' hv)

p2m_export "AlgebraicCurve.WeilDatum" "evalAt_f₂_ne_zero'"
private theorem evalFun_f₁_ne_zero' : Divisor.evalFun d.f₁ d.D₂ ≠ 0 :=
  AlgebraicCurve.Divisor.evalFun_ne_zero fun _ hv => d.evalAt_f₁_ne_zero' hv

private theorem evalFun_f₂_ne_zero' : Divisor.evalFun d.f₂ d.D₁ ≠ 0 :=
  AlgebraicCurve.Divisor.evalFun_ne_zero fun _ hv => d.evalAt_f₂_ne_zero' hv

end AlgebraicCurve.WeilDatum

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_WeilDatum_addLeft_pairing.AlgebraicCurve in
theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ} (d d' : WeilDatum K F n) (hD : d.D₂ = d'.D₂) (hf : d.f₂ = d'.f₂) : (d.addLeft d' hD hf).pairing = d.pairing * d'.pairing := by
  have hnum : Divisor.evalFun (d.f₁ * d'.f₁) d.D₂
      = Divisor.evalFun d.f₁ d.D₂ * Divisor.evalFun d'.f₁ d.D₂ := by
    refine AlgebraicCurve.Divisor.evalFun_mul (fun v hv => d.rational_of_mem_support_right' hv)
      (fun v hv => ?_) (fun v hv => ?_)
    · exact v.mem_of_ord_nonneg d.f₁_ne_zero (d.ord_f₁_eq_zero_of_mem_support' hv).ge
    · exact v.mem_of_ord_nonneg d'.f₁_ne_zero
        (d'.ord_f₁_eq_zero_of_mem_support' (hD ▸ hv)).ge
  have hden : Divisor.evalFun d.f₂ (d.D₁ + d'.D₁)
      = Divisor.evalFun d.f₂ d.D₁ * Divisor.evalFun d.f₂ d'.D₁ := by
    refine AlgebraicCurve.Divisor.evalFun_add d.f₂ (fun v hv => d.evalAt_f₂_ne_zero' hv) (fun v hv => ?_)
    exact hf ▸ d'.evalAt_f₂_ne_zero' hv
  show Divisor.evalFun (d.f₁ * d'.f₁) d.D₂ / Divisor.evalFun d.f₂ (d.D₁ + d'.D₁)
      = d.pairing * d'.pairing
  simp only [WeilDatum.pairing]
  rw [hnum, hden, div_mul_div_comm, hD, hf]

end S_AlgebraicCurve_WeilDatum_addLeft_pairing
end P2MW
export P2MW.S_AlgebraicCurve_WeilDatum_addLeft_pairing (solution)
