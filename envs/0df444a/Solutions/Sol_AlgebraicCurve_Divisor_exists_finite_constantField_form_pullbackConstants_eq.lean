-- Prove2me | solution 1 for AlgebraicCurve.Divisor.exists_finite_constantField_form_pullbackConstants_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/a8e44b9f-a7ec-5b5b-96df-a88ca4e09236

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_ConstantFieldPullback
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_AlgebraicCurve_Place_exists_finite_constantField_form_fiberConstants_eq_singleton
import Theorems.Thm_AlgebraicCurve_Place_ramificationIndex_forgetConstants_eq_one_of_isConstantFieldExtension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Divisor_exists_finite_constantField_form_pullbackConstants_eq
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Divisor_exists_finite_constantField_form_pullbackConstants_eq.AlgebraicCurve"

universe u v

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor Divisor.degree Divisor.degree_single IsCurveOver Place.forgetConstants Place.restrictConstants Place.fiberConstants Place.mem_fiberConstants Divisor.pullbackConstants Divisor.pullbackConstants_apply LSpace ConstantsAreBase Place.exists_finite_constantField_form_fiberConstants_eq_singleton Place.ramificationIndex_forgetConstants_eq_one_of_isConstantFieldExtension"
namespace Divisor
p2m_export "AlgebraicCurve.Divisor" "degree degree_single pullbackConstants pullbackConstants_apply pullback"
namespace ExistsFiniteConstantFieldFormAux
p2m_open "AlgebraicCurve.Divisor AlgebraicCurve"

theorem isAlgebraic_of_forall_pow_pow_eq (K K' : Type*) [Field K] [Field K'] [Algebra K K']
    (ℓ : ℕ) [Fact ℓ.Prime] (halg : ∀ a : K', ∃ n : ℕ, 0 < n ∧ a ^ ℓ ^ n = a) :
    Algebra.IsAlgebraic K K' := by
  refine ⟨fun a => ?_⟩
  obtain ⟨n, hn, ha⟩ := halg a
  refine ⟨Polynomial.X ^ ℓ ^ n - Polynomial.X, ?_, ?_⟩
  · exact FiniteField.X_pow_card_pow_sub_X_ne_zero K hn.ne' (Fact.out : ℓ.Prime).one_lt
  · simp only [map_sub, map_pow, Polynomial.aeval_X, ha, sub_self]

theorem mem_range_of_isAlgebraic_of_constantsAreBase {K F : Type*} [Field K] [Field F] [Algebra K F]
    (hC : ConstantsAreBase K F) (y : F) (hy : IsAlgebraic K y) : y ∈ (algebraMap K F).range := by
  have hint : IsIntegral K y := hy.isIntegral
  have hmem : y ∈ LSpace (0 : Divisor K F) := by
    intro v
    rw [Finsupp.coe_zero, Pi.zero_apply, WithZero.exp_zero]
    refine v.adicValuation_le_one_of_mem ?_
    have hint' : IsIntegral v.toValuationSubring y := hint.tower_top
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint'
    rw [← hz]
    exact z.2
  have hC' : LSpace (0 : Divisor K F) = LinearMap.range (Algebra.linearMap K F) := hC
  rw [hC'] at hmem
  obtain ⟨c, hc⟩ := LinearMap.mem_range.mp hmem
  exact ⟨c, hc⟩

end AlgebraicCurve.Divisor.ExistsFiniteConstantFieldFormAux

open AlgebraicCurve.Divisor.ExistsFiniteConstantFieldFormAux in

theorem solution
    (K' : Type u) (F' : Type v) [Field K'] [Field F'] [Algebra K' F']
    (ℓ : ℕ) [Fact ℓ.Prime] [CharP K' ℓ]
    (halg : ∀ a : K', ∃ n : ℕ, 0 < n ∧ a ^ ℓ ^ n = a)
    (hfg : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K' F'] (hC : ConstantsAreBase K' F') (c : Divisor K' F') :
    ∃ (K : Type u) (F : Type v) (_ : Field K) (_ : Finite K) (_ : Field F)
      (_ : Algebra K K') (_ : Algebra K F) (_ : Algebra F F') (_ : Algebra K F')
      (_ : IsScalarTower K K' F') (_ : IsScalarTower K F F') (_ : Algebra.IsIntegral F F')
      (_ : IsCurveOver K F) (_ : Algebra.EssFiniteType K F)
      (D : Divisor K F),
        Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤ ∧
        ConstantsAreBase K F ∧
        Divisor.pullbackConstants K' F' D = c ∧ Divisor.degree D = Divisor.degree c := by

  obtain ⟨K, F, iFK, iFinK, iFF, iAKK', iAKF, iAFF', iAKF', iST1, iST2, iInt, iCurve, iEFT,
      hgen, hconst, hW⟩ :=
    Place.exists_finite_constantField_form_fiberConstants_eq_singleton K' F' ℓ halg hfg hC c.support

  haveI : Algebra.IsAlgebraic K K' := isAlgebraic_of_forall_pow_pow_eq K K' ℓ halg
  haveI : PerfectField K := inferInstance
  haveI : Algebra.IsSeparable K K' := inferInstance
  have hconstK : ∀ y : F, IsAlgebraic K y → y ∈ (algebraMap K F).range :=
    fun y hy => mem_range_of_isAlgebraic_of_constantsAreBase hconst y hy

  have he : ∀ w : Place K' F', (Place.forgetConstants (K := K) w).ramificationIndex F = 1 :=
    fun w => Place.ramificationIndex_forgetConstants_eq_one_of_isConstantFieldExtension hgen hconstK w

  have hfib : ∀ w ∈ c.support, ∀ w' : Place K' F',
      Place.restrictConstants F (K := K) w' = Place.restrictConstants F (K := K) w → w' = w := by
    intro w hw w' h
    have hmem : w' ∈ Place.fiberConstants K' F' (Place.restrictConstants F (K := K) w) :=
      Place.mem_fiberConstants.mpr h
    rw [(hW w hw).1] at hmem
    exact Finset.mem_singleton.mp hmem

  set D : Divisor K F :=
    ∑ w ∈ c.support, Finsupp.single (Place.restrictConstants F (K := K) w) (c w) with hD

  have hDapply : ∀ w' : Place K' F', D (Place.restrictConstants F (K := K) w') = c w' := by
    intro w'
    rw [hD, Finsupp.finsetSum_apply]
    by_cases hw' : w' ∈ c.support
    · rw [Finset.sum_eq_single_of_mem
        (f := fun w => Finsupp.single (Place.restrictConstants F (K := K) w) (c w)
          (Place.restrictConstants F (K := K) w')) w' hw' ?_]
      · exact Finsupp.single_eq_same
      · intro w hw hne
        refine Finsupp.single_apply_eq_zero.mpr fun h => ?_
        have hww : w' = w := hfib w hw w' (h ▸ rfl)
        exact absurd hww.symm hne
    · rw [Finsupp.notMem_support_iff.mp hw']
      refine Finset.sum_eq_zero fun w hw => Finsupp.single_apply_eq_zero.mpr fun h => ?_
      have hww : w' = w := hfib w hw w' (h ▸ rfl)
      subst hww
      exact absurd hw hw'

  have hpull : Divisor.pullbackConstants K' F' D = c := by
    ext w'
    rw [Divisor.pullbackConstants_apply, he w', hDapply w', Nat.cast_one, one_mul]

  have hdeg : Divisor.degree D = Divisor.degree c := by
    have hc : (∑ w ∈ c.support, Finsupp.single w (c w)) = c := by
      simpa only [Finsupp.sum] using Finsupp.sum_single c
    conv_rhs => rw [← hc]
    rw [hD, map_sum, map_sum]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [Divisor.degree_single, Divisor.degree_single, (hW w hw).2]
  exact ⟨K, F, iFK, iFinK, iFF, iAKK', iAKF, iAFF', iAKF', iST1, iST2, iInt, iCurve, iEFT, D,
    hgen, hconst, hpull, hdeg⟩

end S_AlgebraicCurve_Divisor_exists_finite_constantField_form_pullbackConstants_eq
end P2MW
export P2MW.S_AlgebraicCurve_Divisor_exists_finite_constantField_form_pullbackConstants_eq (solution)
