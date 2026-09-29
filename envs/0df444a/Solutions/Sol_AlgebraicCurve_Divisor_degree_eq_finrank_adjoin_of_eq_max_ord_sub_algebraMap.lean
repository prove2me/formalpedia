-- Prove2me | solution 1 for AlgebraicCurve.Divisor.degree_eq_finrank_adjoin_of_eq_max_ord_sub_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/c90ac65a-83dd-5dcf-b598-ad7f9519bc1f

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex

import Theorems.Thm_AlgebraicCurve_Divisor_degree_eq_finrank_adjoin_of_eq_max_neg_ord
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Divisor_degree_eq_finrank_adjoin_of_eq_max_ord_sub_algebraMap
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

open AlgebraicCurve

namespace FibreDegE96

open AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem adicValuation_eq_exp (v : Place K F) {f : F} (hf : f ≠ 0) :
    v.adicValuation f = WithZero.exp (-v.ord f) := by
  rw [Place.ord, neg_neg, WithZero.exp_log (v.adicValuation_ne_zero hf)]

theorem ord_sub_algebraMap_of_neg (v : Place K F) {x : F} (hx : x ≠ 0) (a : K) (hxa : x - algebraMap K F a ≠ 0)
    (h : v.ord x < 0) : v.ord (x - algebraMap K F a) = v.ord x := by
  have hc : v.adicValuation (algebraMap K F a) ≤ 1 := v.adicValuation_algebraMap_le_one a
  have hxv : 1 < v.adicValuation x := by
    rw [adicValuation_eq_exp v hx, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have hlt : v.adicValuation (-algebraMap K F a) < v.adicValuation x := by
    rw [Valuation.map_neg]; exact lt_of_le_of_lt hc hxv
  have heq : v.adicValuation (x - algebraMap K F a) = v.adicValuation x := by
    rw [sub_eq_add_neg, Valuation.map_add_eq_of_lt_left _ hlt]
  rw [adicValuation_eq_exp v hxa, adicValuation_eq_exp v hx] at heq
  have := WithZero.exp_injective heq
  omega

theorem ord_sub_algebraMap_nonneg (v : Place K F) {x : F} (hx : x ≠ 0) (a : K) (hxa : x - algebraMap K F a ≠ 0)
    (h : 0 ≤ v.ord x) : 0 ≤ v.ord (x - algebraMap K F a) := by
  have hc : v.adicValuation (algebraMap K F a) ≤ 1 := v.adicValuation_algebraMap_le_one a
  have hxv : v.adicValuation x ≤ 1 := by
    rw [adicValuation_eq_exp v hx, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega
  have hle : v.adicValuation (x - algebraMap K F a) ≤ 1 :=
    (Valuation.map_sub _ _ _).trans (max_le hxv hc)
  rw [adicValuation_eq_exp v hxa, ← WithZero.exp_zero, WithZero.exp_le_exp] at hle
  omega

end FibreDegE96

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (a : K) (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (v.ord (x - algebraMap K F a))) :
    Divisor.degree D = (Module.finrank (IntermediateField.adjoin K ({x} : Set F)) F : ℤ) := by
  classical

  have hxa : x - algebraMap K F a ≠ 0 := by
    intro h
    apply hx
    rw [sub_eq_zero] at h
    rw [h]
    exact isAlgebraic_algebraMap a
  have hx0 : x ≠ 0 := by
    intro h; apply hx; rw [h]; exact isAlgebraic_zero

  obtain ⟨P, hP, hP0⟩ := (IsCurveOver.hasPrincipalDivisors (K := K) (F := F)).exists_divisor _ hxa

  let Dinf : Divisor K F := P.mapRange (fun n => max 0 (-n)) (by simp)
  have hDinf : ∀ v : Place K F, Dinf v = max 0 (-v.ord x) := by
    intro v
    show max 0 (-P v) = _
    rw [hP v]
    rcases lt_or_ge (v.ord x) 0 with h | h
    · rw [FibreDegE96.ord_sub_algebraMap_of_neg v hx0 a hxa h]
    · have h' := FibreDegE96.ord_sub_algebraMap_nonneg v hx0 a hxa h
      rw [max_eq_left (by omega : -v.ord (x - algebraMap K F a) ≤ 0), max_eq_left (by omega : -v.ord x ≤ 0)]

  have hsplit : D - Dinf = P := by
    ext v
    rw [Finsupp.sub_apply, hD v]
    show max 0 (v.ord (x - algebraMap K F a)) - max 0 (-P v) = P v
    rw [hP v]
    omega
  have hdeg : Divisor.degree D = Divisor.degree Dinf := by
    have := congrArg Divisor.degree hsplit
    rw [map_sub, hP0] at this
    omega
  rw [hdeg]
  exact AlgebraicCurve.Divisor.degree_eq_finrank_adjoin_of_eq_max_neg_ord x hx Dinf hDinf

end S_AlgebraicCurve_Divisor_degree_eq_finrank_adjoin_of_eq_max_ord_sub_algebraMap
end P2MW
export P2MW.S_AlgebraicCurve_Divisor_degree_eq_finrank_adjoin_of_eq_max_ord_sub_algebraMap (solution)
