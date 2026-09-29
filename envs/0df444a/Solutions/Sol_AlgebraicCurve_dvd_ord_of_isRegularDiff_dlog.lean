-- Prove2me | solution 1 for AlgebraicCurve.dvd_ord_of_isRegularDiff_dlog
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/ed4e8865-c66b-5027-9418-8fe39cd17033

import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Differentials
import Theorems.Thm_AlgebraicCurve_Place_ord_diffCoeff_D_nonneg_of_perfectField
import Theorems.Thm_AlgebraicCurve_Place_D_ne_zero_of_ord_eq_one
import Theorems.Thm_AlgebraicCurve_Place_diffCoeff_smul_D_of_ord_eq_one
import Theorems.Thm_AlgebraicCurve_Place_diffCoeff_smul_D_eq_of_ord_eq_one
import Theorems.Thm_AlgebraicCurve_Place_ord_add_eq_of_lt
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_dvd_ord_of_isRegularDiff_dlog
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

universe u v

open KaehlerDifferential

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "IsCurveOver Place Place.ord_zero Place.ord_one Place.diffCoeff Place.ordDiff_def IsRegularDiff Place.ord_diffCoeff_D_nonneg_of_perfectField Place.D_ne_zero_of_ord_eq_one Place.diffCoeff_smul_D_of_ord_eq_one Place.diffCoeff_smul_D_eq_of_ord_eq_one Place.ord_add_eq_of_lt Place.ord_algebraMap"
namespace DlogResidue
p2m_open "AlgebraicCurve"

section Helpers

variable {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]

theorem dlog_mul {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b)⁻¹ • D K F (a * b) = a⁻¹ • D K F a + b⁻¹ • D K F b := by
  rw [Derivation.leibniz, mul_inv, smul_add, smul_smul, smul_smul, add_comm]
  congr 1
  · rw [mul_assoc, inv_mul_cancel₀ hb, mul_one]
  · rw [mul_comm a⁻¹ b⁻¹, mul_assoc, inv_mul_cancel₀ ha, mul_one]

theorem dlog_pow {a : F} (ha : a ≠ 0) (m : ℕ) :
    (a ^ m)⁻¹ • D K F (a ^ m) = (m : F) • (a⁻¹ • D K F a) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, dlog_mul (pow_ne_zero m ha) ha, ih, Nat.cast_succ, add_smul, one_smul]

theorem dlog_inv {a : F} (ha : a ≠ 0) :
    (a⁻¹)⁻¹ • D K F a⁻¹ = -(a⁻¹ • D K F a) := by
  have h := dlog_mul (K := K) ha (inv_ne_zero ha)
  rw [mul_inv_cancel₀ ha, inv_one, Derivation.map_one_eq_zero, smul_zero] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem dlog_zpow {a : F} (ha : a ≠ 0) (n : ℤ) :
    (a ^ n)⁻¹ • D K F (a ^ n) = (n : F) • (a⁻¹ • D K F a) := by
  cases n with
  | ofNat m => rw [Int.ofNat_eq_natCast, zpow_natCast, dlog_pow ha, Int.cast_natCast]
  | negSucc m =>
    rw [zpow_negSucc, dlog_inv (pow_ne_zero _ ha), dlog_pow ha, Int.cast_negSucc, neg_smul]

end Helpers

theorem main
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]
    [AlgebraicCurve.IsCurveOver K F] (p : ℕ) [Fact p.Prime]
    [CharP K p] [PerfectField K]
    (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    {g : F} (hreg : AlgebraicCurve.IsRegularDiff K F (g⁻¹ • D K F g))
    (v : AlgebraicCurve.Place K F) : (p : ℤ) ∣ v.ord g := by
  haveI hKx : Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F :=
    Algebra.IsAlgebraic.of_finite _ F
  haveI : CharP F p := charP_of_injective_algebraMap (algebraMap K F).injective p

  rcases eq_or_ne g 0 with rfl | hg
  · simp

  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hπF : (π : F) ≠ 0 := by
    simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  have hordπ : v.ord (π : F) = 1 := v.ord_coe_irreducible hπ
  have hordt : v.ord v.uniformizer_alt = 1 := v.ord_uniformizer_alt ⟨(π : F), hordπ⟩
  set t₀ : F := v.uniformizer_alt with ht₀
  have hDπ : D K F (π : F) ≠ 0 := Place.D_ne_zero_of_ord_eq_one x v hordπ
  have hDt : D K F t₀ ≠ 0 := Place.D_ne_zero_of_ord_eq_one x v hordt

  obtain ⟨w, hw⟩ := v.exists_unit_mul_zpow hg hπ
  set n : ℤ := v.ord g with hn
  set uF : F := ((w : v.toValuationSubring) : F) with huF
  have huF0 : uF ≠ 0 := by simp [huF, ne_eq, ZeroMemClass.coe_eq_zero]
  have horduF : v.ord uF = 0 := by rw [huF]; exact v.ord_coe_unit w

  by_contra hndvd
  have hnF : ((n : ℤ) : F) ≠ 0 := by
    intro h0
    exact hndvd ((CharP.intCast_eq_zero_iff F p n).mp h0)

  have hdlog : g⁻¹ • D K F g = uF⁻¹ • D K F uF + ((n : ℤ) : F) • ((π : F)⁻¹ • D K F (π : F)) := by
    conv_lhs => rw [hw]
    rw [dlog_mul huF0 (zpow_ne_zero _ hπF), dlog_zpow hπF]

  set a : F := Place.diffCoeff (π : F) (D K F uF) with ha
  have haD : a • D K F (π : F) = D K F uF := Place.diffCoeff_smul_D_of_ord_eq_one x v hordπ _
  have horda : 0 ≤ v.ord a := Place.ord_diffCoeff_D_nonneg_of_perfectField x v hordπ (f := uF)
    (by rw [horduF])

  set c : F := uF⁻¹ * a + ((n : ℤ) : F) * (π : F)⁻¹ with hc
  have hdlog' : g⁻¹ • D K F g = c • D K F (π : F) := by
    rw [hdlog, ← haD, smul_smul, smul_smul, hc, add_smul]
  have hordn : v.ord (((n : ℤ) : F)) = 0 := by
    rw [show (((n : ℤ) : F)) = algebraMap K F (n : K) from (map_intCast (algebraMap K F) n).symm]
    exact Place.ord_algebraMap v _
  have hord2 : v.ord (((n : ℤ) : F) * (π : F)⁻¹) = -1 := by
    rw [v.ord_mul hnF (inv_ne_zero hπF), hordn, v.ord_inv, hordπ]; norm_num
  have h2ne : ((n : ℤ) : F) * (π : F)⁻¹ ≠ 0 := mul_ne_zero hnF (inv_ne_zero hπF)
  have hordc : v.ord c = -1 := by
    rcases eq_or_ne a 0 with ha0 | ha0
    · rw [hc, ha0, mul_zero, zero_add, hord2]
    · have h1ne : uF⁻¹ * a ≠ 0 := mul_ne_zero (inv_ne_zero huF0) ha0
      have hord1 : 0 ≤ v.ord (uF⁻¹ * a) := by
        rw [v.ord_mul (inv_ne_zero huF0) ha0, v.ord_inv, horduF, neg_zero, zero_add]; exact horda
      rw [hc, add_comm, Place.ord_add_eq_of_lt v h2ne h1ne (by rw [hord2]; omega), hord2]
  have hc0 : c ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at hordc; exact absurd hordc (by norm_num)

  set b : F := Place.diffCoeff t₀ (D K F (π : F)) with hb
  set b' : F := Place.diffCoeff (π : F) (D K F t₀) with hb'
  have hbD : b • D K F t₀ = D K F (π : F) := Place.diffCoeff_smul_D_of_ord_eq_one x v hordt _
  have hb'D : b' • D K F (π : F) = D K F t₀ := Place.diffCoeff_smul_D_of_ord_eq_one x v hordπ _
  have hordb : 0 ≤ v.ord b := Place.ord_diffCoeff_D_nonneg_of_perfectField x v hordt
    (f := (π : F)) (by rw [hordπ]; norm_num)
  have hordb' : 0 ≤ v.ord b' := Place.ord_diffCoeff_D_nonneg_of_perfectField x v hordπ
    (f := t₀) (by rw [hordt]; norm_num)
  have hbb' : b * b' = 1 := by
    have h1 : (b * b') • D K F (π : F) = D K F (π : F) := by rw [← smul_smul, hb'D, hbD]
    have h2 : (b * b' - 1) • D K F (π : F) = 0 := by rw [sub_smul, one_smul, h1, sub_self]
    rcases smul_eq_zero.mp h2 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hDπ
  have hb0 : b ≠ 0 := left_ne_zero_of_mul_eq_one hbb'
  have hb'0 : b' ≠ 0 := right_ne_zero_of_mul_eq_one hbb'
  have hordb0 : v.ord b = 0 := by
    have := v.ord_mul hb0 hb'0
    rw [hbb', Place.ord_one] at this
    omega

  have hcoeff : Place.diffCoeff t₀ (g⁻¹ • D K F g) = c * b := by
    rw [hdlog', ← hbD, smul_smul]
    exact Place.diffCoeff_smul_D_eq_of_ord_eq_one x v hordt _
  have hv := hreg v
  rw [Place.ordDiff_def, ← ht₀, hcoeff, v.ord_mul hc0 hb0, hordc, hordb0] at hv
  exact absurd hv (by norm_num)

end AlgebraicCurve.DlogResidue

theorem solution
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]
    [AlgebraicCurve.IsCurveOver K F] (p : ℕ) [Fact p.Prime]
    [CharP K p] [PerfectField K]
    (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    {g : F} (hreg : AlgebraicCurve.IsRegularDiff K F (g⁻¹ • D K F g)) :
    ∀ v : AlgebraicCurve.Place K F, (p : ℤ) ∣ v.ord g :=
  AlgebraicCurve.DlogResidue.main p x hreg

end S_AlgebraicCurve_dvd_ord_of_isRegularDiff_dlog
end P2MW
export P2MW.S_AlgebraicCurve_dvd_ord_of_isRegularDiff_dlog (solution)
