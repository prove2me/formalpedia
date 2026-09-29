-- Prove2me | solution 1 for AlgebraicCurve.Place.exists_integralClosureAt_of_ord_fiber_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/94e2b3b3-e594-5105-9e35-b8795e8586c7

import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_AlgebraicCurve_Place_count_normalizedFactors_span_singleton
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_exists_integralClosureAt_of_ord_fiber_nonneg
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

open IsDedekindDomain WithZero IsLocalRing UniqueFactorizationMonoid AlgebraicCurve AlgebraicCurve.Place

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] {v : Place K F} [HasPrincipalDivisors K F'] {f : F'} (hf : f ≠ 0)
    (hord : ∀ w ∈ v.fiber F', 0 ≤ w.ord f) :
    ∃ c : integralClosureAt F' v, algebraMap (integralClosureAt F' v) F' c = f := by
  classical

  obtain ⟨⟨c₀, s₀⟩, hcs⟩ := IsLocalization.surj
    (nonZeroDivisors (integralClosureAt F' v)) f
  have hs0 : (s₀ : integralClosureAt F' v) ≠ 0 := nonZeroDivisors.coe_ne_zero s₀
  have hsF : algebraMap (integralClosureAt F' v) F' (s₀ : integralClosureAt F' v) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (integralClosureAt F' v) F')).mpr hs0
  have hcF : algebraMap (integralClosureAt F' v) F' c₀ ≠ 0 := by
    rw [← hcs]; exact mul_ne_zero hf hsF
  have hc0 : c₀ ≠ 0 := fun h => hcF (by rw [h, map_zero])

  have hdom : ∀ (w : Place K F') (hw : w.restrict F = v),
      w.ord (algebraMap (integralClosureAt F' v) F' (s₀ : integralClosureAt F' v))
        ≤ w.ord (algebraMap (integralClosureAt F' v) F' c₀) := by
    intro w hw
    have h1 : w.ord (algebraMap (integralClosureAt F' v) F' c₀)
        = w.ord f + w.ord (algebraMap (integralClosureAt F' v) F' (s₀ :
            integralClosureAt F' v)) := by
      rw [← hcs]; exact w.ord_mul hf hsF
    have h2 := hord w (mem_fiber.mpr hw)
    omega

  have hle : Ideal.span {c₀} ≤ Ideal.span {(s₀ : integralClosureAt F' v)} := by
    have hspan_c : (Ideal.span {c₀} : Ideal (integralClosureAt F' v)) ≠ ⊥ := fun h =>
      hc0 (Ideal.span_singleton_eq_bot.mp h)
    have hspan_s : (Ideal.span {(s₀ : integralClosureAt F' v)} :
        Ideal (integralClosureAt F' v)) ≠ ⊥ := fun h => hs0 (Ideal.span_singleton_eq_bot.mp h)
    rw [← Ideal.dvd_iff_le, dvd_iff_normalizedFactors_le_normalizedFactors hspan_s hspan_c,
      Multiset.le_iff_count]
    intro P
    by_cases hP : P ∈ normalizedFactors
      (Ideal.span {(s₀ : integralClosureAt F' v)} : Ideal (integralClosureAt F' v))
    ·
      have hPprime : Prime P := prime_of_normalized_factor P hP
      haveI : P.IsPrime := Ideal.isPrime_of_prime hPprime
      have hres := restrict_placeOfPrime
        (⟨P, inferInstance, hPprime.ne_zero⟩ : HeightOneSpectrum (integralClosureAt F' v))
      have hPeq : (fiberCenter F' v hres).asIdeal = P := congrArg HeightOneSpectrum.asIdeal
        (fiberCenter_placeOfPrime
          (⟨P, inferInstance, hPprime.ne_zero⟩ : HeightOneSpectrum (integralClosureAt F' v)))
      rw [← hPeq, AlgebraicCurve.Place.count_normalizedFactors_span_singleton hres hs0,
        AlgebraicCurve.Place.count_normalizedFactors_span_singleton hres hc0]
      exact Int.toNat_le_toNat (hdom _ hres)
    · rw [Multiset.count_eq_zero_of_notMem hP]
      exact Nat.zero_le _

  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp (hle (Ideal.mem_span_singleton_self c₀))
  refine ⟨d, ?_⟩
  have hmapped := congrArg (algebraMap (integralClosureAt F' v) F') hd
  rw [map_mul] at hmapped
  refine mul_left_cancel₀ hsF ?_
  rw [← hmapped, ← hcs]
  ring

end S_AlgebraicCurve_Place_exists_integralClosureAt_of_ord_fiber_nonneg
end P2MW
export P2MW.S_AlgebraicCurve_Place_exists_integralClosureAt_of_ord_fiber_nonneg (solution)
