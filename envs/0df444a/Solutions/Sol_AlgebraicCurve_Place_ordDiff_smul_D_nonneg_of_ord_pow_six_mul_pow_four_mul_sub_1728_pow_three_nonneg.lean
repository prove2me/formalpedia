-- Prove2me | solution 1 for AlgebraicCurve.Place.ordDiff_smul_D_nonneg_of_ord_pow_six_mul_pow_four_mul_sub_1728_pow_three_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/52ed728b-934d-5c99-8c40-838b4bbcdc56

import Definitions.Def_AlgebraicCurve_Differentials
import Theorems.Thm_AlgebraicCurve_Place_ord_add_eq_of_lt
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_neg
import Theorems.Thm_AlgebraicCurve_Place_ordDiff_zero_of_perfectField
import Theorems.Thm_AlgebraicCurve_Place_ordDiff_smul_of_perfectField
import Theorems.Thm_AlgebraicCurve_Place_ord_sub_one_le_ordDiff_D_of_perfectField
import Theorems.Thm_AlgebraicCurve_Place_ord_diffCoeff_D_nonneg_of_perfectField
import Theorems.Thm_AlgebraicCurve_Place_exists_ord_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_ordDiff_smul_D_nonneg_of_ord_pow_six_mul_pow_four_mul_sub_1728_pow_three_nonneg
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Place_ordDiff_smul_D_nonneg_of_ord_pow_six_mul_pow_four_mul_sub_1728_pow_three_nonneg.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord_neg"
namespace Place
p2m_export "AlgebraicCurve.Place" "diffCoeff ordDiff ordDiff_def ord_uniformizer_alt uniformizer_alt ord ord_mul ord_add_eq_of_lt ord_algebraMap ord_neg ordDiff_zero_of_perfectField ordDiff_smul_of_perfectField ord_sub_one_le_ordDiff_D_of_perfectField ord_diffCoeff_D_nonneg_of_perfectField exists_ord_eq_one"
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

section Ceil

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.ord_pow_of_ne_zero {f : F} (hf : f ≠ 0) (n : ℕ) : v.ord (f ^ n) = n * v.ord f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, v.ord_mul (pow_ne_zero _ hf) hf, ih]
    push_cast
    ring

p2m_export "AlgebraicCurve.Place" "ord_pow_of_ne_zero"

private theorem _root_.AlgebraicCurve.Place.ordDiff_D_nonneg_pf_bridge [PerfectField K] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    {f : F} (hf : 0 ≤ v.ord f) :
    0 ≤ v.ordDiff (KaehlerDifferential.D K F f) := by
  rw [ordDiff_def]
  exact v.ord_diffCoeff_D_nonneg_of_perfectField x (v.ord_uniformizer_alt v.exists_ord_eq_one) hf

p2m_export "AlgebraicCurve.Place" "ordDiff_D_nonneg_pf_bridge"

private theorem ordDiff_smul_D_nonneg_of_ord_nonneg [PerfectField K] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (g J : F) (h1728 : (1728 : K) ≠ 0)
    (hu : 0 ≤ v.ord (g ^ 6 * J ^ 4 * (J - algebraMap K F 1728) ^ 3)) :
    0 ≤ v.ordDiff (g • KaehlerDifferential.D K F J) := by

  by_cases hg : g = 0
  · subst hg; rw [zero_smul]; exact (v.ordDiff_zero_of_perfectField x).ge
  by_cases hD : KaehlerDifferential.D K F J = 0
  · rw [hD, smul_zero]; exact (v.ordDiff_zero_of_perfectField x).ge

  set c : F := algebraMap K F 1728 with hc_def
  have hc : c ≠ 0 := fun h => h1728 ((map_eq_zero_iff _ (algebraMap K F).injective).mp h)
  have hJ0 : J ≠ 0 := by rintro rfl; exact hD (map_zero _)
  have hDc : KaehlerDifferential.D K F (J - c) = KaehlerDifferential.D K F J := by
    rw [map_sub, hc_def, (KaehlerDifferential.D K F).map_algebraMap, sub_zero]
  have hJc : J - c ≠ 0 := by
    intro h0
    apply hD
    rw [← hDc, h0, map_zero]

  have hexp : 0 ≤ 6 * v.ord g + 4 * v.ord J + 3 * v.ord (J - c) := by
    have h := hu
    rw [v.ord_mul (mul_ne_zero (pow_ne_zero _ hg) (pow_ne_zero _ hJ0)) (pow_ne_zero _ hJc),
      v.ord_mul (pow_ne_zero _ hg) (pow_ne_zero _ hJ0), v.ord_pow_of_ne_zero hg, v.ord_pow_of_ne_zero hJ0,
      v.ord_pow_of_ne_zero hJc] at h
    push_cast at h
    linarith
  rw [v.ordDiff_smul_of_perfectField x hg hD]
  have hc0 : v.ord c = 0 := v.ord_algebraMap 1728
  have hnc0 : v.ord (-c) = 0 := by rw [v.ord_neg, hc0]

  have hA5 : v.ord J - 1 ≤ v.ordDiff (KaehlerDifferential.D K F J) := v.ord_sub_one_le_ordDiff_D_of_perfectField x hD
  have hA5c : v.ord (J - c) - 1 ≤ v.ordDiff (KaehlerDifferential.D K F J) := by
    have h := v.ord_sub_one_le_ordDiff_D_of_perfectField x (f := J - c) (by rw [hDc]; exact hD)
    rwa [hDc] at h
  rcases lt_trichotomy (v.ord J) 0 with hneg | hzero | hpos
  ·
    have h2 : v.ord (J - c) = v.ord J := by
      rw [sub_eq_add_neg, v.ord_add_eq_of_lt hJ0 (neg_ne_zero.mpr hc) (by rw [hnc0]; exact hneg)]
    omega
  ·
    have hA4 : 0 ≤ v.ordDiff (KaehlerDifferential.D K F J) := v.ordDiff_D_nonneg_pf_bridge x hzero.ge
    rcases lt_or_ge (v.ord (J - c)) 0 with hneg' | hnn'
    · exfalso
      have h3 : v.ord (J - c + c) = v.ord (J - c) :=
        v.ord_add_eq_of_lt hJc hc (by rw [hc0]; exact hneg')
      rw [sub_add_cancel] at h3
      omega
    · omega
  ·
    have h2 : v.ord (J - c) = 0 := by
      rw [sub_eq_add_neg, add_comm, v.ord_add_eq_of_lt (neg_ne_zero.mpr hc) hJ0 (by rw [hnc0]; exact hpos), hnc0]
    omega

end Ceil

end AlgebraicCurve.Place

theorem solution {K F : Type*} [Field K] [Field F]
    [Algebra K F] (v : AlgebraicCurve.Place K F) [PerfectField K] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (g J : F) (h1728 : (1728 : K) ≠ 0)
    (hu : 0 ≤ v.ord (g ^ 6 * J ^ 4 * (J - algebraMap K F 1728) ^ 3)) :
    0 ≤ v.ordDiff (g • KaehlerDifferential.D K F J) :=
  AlgebraicCurve.Place.ordDiff_smul_D_nonneg_of_ord_nonneg v x g J h1728 hu

end S_AlgebraicCurve_Place_ordDiff_smul_D_nonneg_of_ord_pow_six_mul_pow_four_mul_sub_1728_pow_three_nonneg
end P2MW
export P2MW.S_AlgebraicCurve_Place_ordDiff_smul_D_nonneg_of_ord_pow_six_mul_pow_four_mul_sub_1728_pow_three_nonneg (solution)
