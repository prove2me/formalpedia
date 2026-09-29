-- Prove2me | solution 1 for AlgebraicCurve.exists_divisor_eq_floor_and_mul_degree_le_of_min_ord_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/203be9ee-26df-5238-a638-c400800319e0

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_divisor_eq_floor_and_mul_degree_le_of_min_ord_le
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

open AlgebraicCurve
open scoped IntermediateField

namespace DegEBody

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

theorem degree_eq_sum_support (hdeg1 : ∀ v : Place k F, v.deg = 1) (D : Divisor k F) :
    D.degree = ∑ v ∈ D.support, D v := by
  rw [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum]
  exact Finset.sum_congr rfl fun v _ => by rw [AddMonoidHom.mulRight_apply, hdeg1 v, Nat.cast_one, mul_one]

end DegEBody

open DegEBody in
theorem solution
    (k : Type*) [Field k] [IsAlgClosed k] {F : Type*} [Field F] [Algebra k F]
    (x : F) (hx : Transcendental k x)
    (hfin : FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F)
    (f : F) (hf : f ≠ 0) (hfx : ∀ v : Place k F, min 0 (v.ord x) ≤ v.ord f)
    (m d : ℕ) (hd : 0 < d) :
    ∃ E : Divisor k F,
      (∀ v : Place k F, E v = ((m : ℤ) * (v.ord f - min 0 (v.ord x))) / (d : ℤ)) ∧
      (d : ℤ) * E.degree ≤ (m : ℤ) * (Module.finrank (IntermediateField.adjoin k ({x} : Set F)) F : ℤ) := by
  classical
  haveI := hfin
  haveI : IsCurveOver k F := AlgebraicCurve.isCurveOver_of_isAlgClosed_of_transcendental x hx
  have hdeg1 : ∀ v : Place k F, v.deg = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed
  obtain ⟨Df, hDf, hDf0⟩ := HasPrincipalDivisors.exists_divisor (K := k) (F := F) f hf
  obtain ⟨S, hS, hSsum⟩ := AlgebraicCurve.exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed k x hx hfin
  set g : Place k F → ℤ := fun v => ((m : ℤ) * (v.ord f - min 0 (v.ord x))) / (d : ℤ) with hg
  set T : Finset (Place k F) := Df.support ∪ S with hT
  have hzero : ∀ v, v ∉ T → v.ord f = 0 ∧ 0 ≤ v.ord x := by
    intro v hv
    rw [hT, Finset.mem_union, not_or, Finsupp.mem_support_iff, not_not, hS, not_lt] at hv
    exact ⟨by rw [← hDf v]; exact hv.1, hv.2⟩
  have hgT : ∀ v, g v ≠ 0 → v ∈ T := by
    intro v hv
    by_contra hvT
    obtain ⟨h1, h2⟩ := hzero v hvT
    apply hv
    simp only [hg, h1, min_eq_left h2, sub_zero, mul_zero, Int.zero_ediv]
  let E : Divisor k F := Finsupp.onFinset T g (fun v hv => hgT v hv)
  have hE : ∀ v, E v = g v := fun v => Finsupp.onFinset_apply
  refine ⟨E, fun v => hE v, ?_⟩

  have hdegE : E.degree = ∑ v ∈ T, g v := by
    rw [degree_eq_sum_support hdeg1]
    rw [Finset.sum_congr rfl (fun v (_ : v ∈ E.support) => hE v)]
    exact Finset.sum_subset Finsupp.support_onFinset_subset (fun v _ hv => by
      rw [Finsupp.mem_support_iff, not_not] at hv
      exact (hE v).symm.trans hv)

  have hpt : ∀ v, (d : ℤ) * g v ≤ (m : ℤ) * (v.ord f - min 0 (v.ord x)) := fun v => by
    rw [hg, mul_comm]
    exact Int.ediv_mul_le _ (by exact_mod_cast hd.ne')

  have hsumf : ∑ v ∈ T, v.ord f = 0 := by
    have h1 : ∑ v ∈ Df.support, v.ord f = ∑ v ∈ T, v.ord f :=
      Finset.sum_subset Finset.subset_union_left (fun v _ hv => by
        rw [Finsupp.mem_support_iff, not_not] at hv
        rw [← hDf, hv])
    have h2 : Df.degree = ∑ v ∈ Df.support, v.ord f := by
      rw [degree_eq_sum_support hdeg1]
      exact Finset.sum_congr rfl fun v _ => hDf v
    rw [← h1, ← h2, hDf0]

  have hsumx : ∑ v ∈ T, (-min 0 (v.ord x)) =
      (Module.finrank (IntermediateField.adjoin k ({x} : Set F)) F : ℤ) := by
    rw [← hSsum]
    have h1 : ∀ v ∈ S, -v.ord x = -min 0 (v.ord x) := fun v hv => by
      rw [min_eq_right ((hS v).mp hv).le]
    rw [Finset.sum_congr rfl h1]
    symm
    exact Finset.sum_subset Finset.subset_union_right (fun v _ hv => by
      rw [hS, not_lt] at hv
      rw [min_eq_left hv, neg_zero])

  calc (d : ℤ) * E.degree = ∑ v ∈ T, (d : ℤ) * g v := by rw [hdegE, Finset.mul_sum]
    _ ≤ ∑ v ∈ T, (m : ℤ) * (v.ord f - min 0 (v.ord x)) := Finset.sum_le_sum fun v _ => hpt v
    _ = (m : ℤ) * (∑ v ∈ T, v.ord f + ∑ v ∈ T, (-min 0 (v.ord x))) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        exact Finset.sum_congr rfl fun v _ => by ring
    _ = (m : ℤ) * (Module.finrank (IntermediateField.adjoin k ({x} : Set F)) F : ℤ) := by
        rw [hsumf, hsumx, zero_add]

end S_AlgebraicCurve_exists_divisor_eq_floor_and_mul_degree_le_of_min_ord_le
end P2MW
export P2MW.S_AlgebraicCurve_exists_divisor_eq_floor_and_mul_degree_le_of_min_ord_le (solution)
