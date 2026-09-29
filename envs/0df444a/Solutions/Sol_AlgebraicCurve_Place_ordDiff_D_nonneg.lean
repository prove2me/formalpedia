-- Prove2me | solution 1 for AlgebraicCurve.Place.ordDiff_D_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/3cc70789-af01-5fb1-b8f8-500929d9c7d0

import Definitions.Def_AlgebraicCurve_Differentials
import Theorems.Thm_AlgebraicCurve_Place_D_ne_zero_of_ord_ne_zero
import Theorems.Thm_AlgebraicCurve_Place_diffCoeff_smul_D_of_ord_ne_zero
import Theorems.Thm_AlgebraicCurve_Place_diffCoeff_smul_D_eq
import Theorems.Thm_AlgebraicCurve_Place_exists_ord_eq_one
import Theorems.Thm_AlgebraicCurve_Place_ord_diffCoeff_D_nonneg
import Theorems.Thm_AlgebraicCurve_Place_ord_add_eq_of_lt
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_neg
import Theorems.Thm_AlgebraicCurve_Place_ord_natCast
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_ordDiff_D_nonneg
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

noncomputable section
open KaehlerDifferential

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place.diffCoeff Place.ordDiff_def Place Place.D_ne_zero_of_ord_ne_zero Place.diffCoeff_smul_D_of_ord_ne_zero Place.diffCoeff_smul_D_eq Place.ord_diffCoeff_D_nonneg Place.ord_add_eq_of_lt"
namespace FF2R4A
p2m_open "AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

section R3grade
variable [CharZero K] (x : F) [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F]

include x in
theorem ordDiff_smul (v : Place K F) {g : F} (hg : g ≠ 0) {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    v.ordDiff (g • ω) = v.ord g + v.ordDiff ω := by
  have h1 : v.ord v.uniformizer_alt ≠ 0 := by
    rw [v.ord_uniformizer_alt v.exists_ord_eq_one]; exact one_ne_zero
  set a := Place.diffCoeff v.uniformizer_alt ω with ha
  have hωa : a • D K F v.uniformizer_alt = ω := Place.diffCoeff_smul_D_of_ord_ne_zero x v h1 ω
  have ha0 : a ≠ 0 := by
    intro h0; rw [h0, zero_smul] at hωa; exact hω hωa.symm
  rw [Place.ordDiff_def, Place.ordDiff_def, ← ha, ← hωa, smul_smul,
    Place.diffCoeff_smul_D_eq x v h1, v.ord_mul hg ha0]

end R3grade

section R4grade
variable [CharZero K] (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]

include x in

theorem ord_diffCoeff_D_eq_zero (v : Place K F) {t t' : F} (ht : v.ord t = 1) (ht' : v.ord t' = 1) :
    v.ord (Place.diffCoeff t (D K F t')) = 0 := by
  have ht0 : v.ord t ≠ 0 := by rw [ht]; exact one_ne_zero
  have ht0' : v.ord t' ≠ 0 := by rw [ht']; exact one_ne_zero
  set c := Place.diffCoeff t (D K F t') with hc
  set c' := Place.diffCoeff t' (D K F t) with hc'
  have h1 : c • D K F t = D K F t' := Place.diffCoeff_smul_D_of_ord_ne_zero x v ht0 _
  have h2 : c' • D K F t' = D K F t := Place.diffCoeff_smul_D_of_ord_ne_zero x v ht0' _
  have hcc : c * c' = 1 := by
    have h3 : (c * c') • D K F t' = (1 : F) • D K F t' := by
      rw [one_smul, ← smul_smul, h2, h1]
    exact smul_left_injective F (Place.D_ne_zero_of_ord_ne_zero x v ht0') h3
  have hc0 : c ≠ 0 := left_ne_zero_of_mul_eq_one hcc
  have hc0' : c' ≠ 0 := right_ne_zero_of_mul_eq_one hcc
  have hsum : v.ord c + v.ord c' = 0 := by rw [← v.ord_mul hc0 hc0', hcc, v.ord_one]
  have hge : 0 ≤ v.ord c := Place.ord_diffCoeff_D_nonneg x v ht (by rw [ht']; exact zero_le_one)
  have hge' : 0 ≤ v.ord c' := Place.ord_diffCoeff_D_nonneg x v ht' (by rw [ht]; exact zero_le_one)
  omega

include x in

theorem ordDiff_eq_ord_diffCoeff (v : Place K F) {t : F} (ht : v.ord t = 1) (ω : Ω[F⁄K]) :
    v.ordDiff ω = v.ord (Place.diffCoeff t ω) := by
  have ht0 : v.ord t ≠ 0 := by rw [ht]; exact one_ne_zero
  have hu : v.ord v.uniformizer_alt = 1 := v.ord_uniformizer_alt v.exists_ord_eq_one
  have hu0 : v.ord v.uniformizer_alt ≠ 0 := by rw [hu]; exact one_ne_zero
  set a := Place.diffCoeff t ω with ha
  set c := Place.diffCoeff v.uniformizer_alt (D K F t) with hc
  have hω : a • D K F t = ω := Place.diffCoeff_smul_D_of_ord_ne_zero x v ht0 ω
  have hDt : c • D K F v.uniformizer_alt = D K F t := Place.diffCoeff_smul_D_of_ord_ne_zero x v hu0 _
  have hc0 : c ≠ 0 := by
    rintro h; rw [h, zero_smul] at hDt; exact Place.D_ne_zero_of_ord_ne_zero x v ht0 hDt.symm
  have hcord : v.ord c = 0 := ord_diffCoeff_D_eq_zero x v hu ht
  rw [Place.ordDiff_def, ← hω, ← hDt, smul_smul, Place.diffCoeff_smul_D_eq x v hu0]
  rcases eq_or_ne a 0 with h0 | ha0
  · rw [h0, zero_mul]
  · rw [v.ord_mul ha0 hc0, hcord, add_zero]

include x in

theorem ordDiff_D_nonneg (v : Place K F) {f : F} (hf : 0 ≤ v.ord f) : 0 ≤ v.ordDiff (D K F f) := by
  obtain ⟨t, ht⟩ := v.exists_ord_eq_one
  rw [ordDiff_eq_ord_diffCoeff x v ht]
  exact Place.ord_diffCoeff_D_nonneg x v ht hf

include x in

theorem ordDiff_D_of_ord_pos (v : Place K F) {f : F} (hf : 0 < v.ord f) :
    v.ordDiff (D K F f) = v.ord f - 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hπord : v.ord (π : F) = 1 := v.ord_coe_irreducible hπ
  have hπ0 : v.ord (π : F) ≠ 0 := by rw [hπord]; exact one_ne_zero
  have hf0 : f ≠ 0 := by rintro rfl; simp at hf
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf0 hπ
  obtain ⟨n, hn⟩ : ∃ n : ℕ, v.ord f = n := ⟨(v.ord f).toNat, (Int.toNat_of_nonneg hf.le).symm⟩
  have hn0 : n ≠ 0 := by rintro rfl; simp [hn] at hf
  rw [hn, zpow_natCast] at hu
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  set uF : F := ((u : v.toValuationSubring) : F) with huF
  have huF0 : uF ≠ 0 := by
    intro h; apply hf0; rw [hu, h, zero_mul]
  have hπF : (π : F) ≠ 0 := by
    intro h; rw [h, v.ord_zero] at hπord; exact zero_ne_one hπord
  have hnF : (n : F) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  have huord : v.ord uF = 0 := v.ord_coe_unit u

  set cu := Place.diffCoeff (π : F) (D K F uF) with hcu
  have hcu_ge : 0 ≤ v.ord cu := Place.ord_diffCoeff_D_nonneg x v hπord huord.ge
  have hDu : cu • D K F (π : F) = D K F uF := Place.diffCoeff_smul_D_of_ord_ne_zero x v hπ0 _

  have hDf : D K F f = (uF * (n * (π : F) ^ (n - 1)) + (π : F) ^ n * cu) • D K F (π : F) := by
    rw [hu, Derivation.leibniz, Derivation.leibniz_pow, ← hDu, ← Nat.cast_smul_eq_nsmul F]
    simp only [smul_smul]
    rw [← add_smul]
  rw [ordDiff_eq_ord_diffCoeff x v hπord, hDf, Place.diffCoeff_smul_D_eq x v hπ0, hn]

  have hπn1 : v.ord ((π : F) ^ (n - 1)) = ((n - 1 : ℕ) : ℤ) := by
    rw [← zpow_natCast, v.ord_zpow, hπord, mul_one]
  have hA0 : uF * (n * (π : F) ^ (n - 1)) ≠ 0 :=
    mul_ne_zero huF0 (mul_ne_zero hnF (pow_ne_zero _ hπF))
  have hA : v.ord (uF * (n * (π : F) ^ (n - 1))) = ((n - 1 : ℕ) : ℤ) := by
    rw [v.ord_mul huF0 (mul_ne_zero hnF (pow_ne_zero _ hπF)), huord, zero_add,
      v.ord_mul hnF (pow_ne_zero _ hπF), v.ord_natCast n, zero_add, hπn1]
  have hsub : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn0)]; simp
  rcases eq_or_ne cu 0 with hcu0 | hcu0
  · rw [hcu0, mul_zero, add_zero, hA, hsub]
  · have hB : v.ord ((π : F) ^ n * cu) = (n : ℤ) + v.ord cu := by
      rw [v.ord_mul (pow_ne_zero _ hπF) hcu0, ← zpow_natCast, v.ord_zpow, hπord, mul_one]
    rw [Place.ord_add_eq_of_lt v hA0 (mul_ne_zero (pow_ne_zero _ hπF) hcu0) (by rw [hA, hB, hsub]; omega), hA, hsub]

include x in

theorem ordDiff_D_eq_ord_sub_one (v : Place K F) {f : F} (hf : v.ord f ≠ 0) :
    v.ordDiff (D K F f) = v.ord f - 1 := by
  rcases lt_or_gt_of_ne hf with hneg | hpos
  ·
    have hf0 : f ≠ 0 := by rintro rfl; simp at hneg
    have hinv : 0 < v.ord f⁻¹ := by rw [v.ord_inv]; omega
    have hinv0 : v.ord f⁻¹ ≠ 0 := hinv.ne'
    have hDf : D K F f = (-(f ^ 2)) • D K F f⁻¹ := by
      rw [Derivation.leibniz_inv, smul_smul]
      have : -(f ^ 2) * -(f⁻¹ ^ 2) = 1 := by field_simp
      rw [this, one_smul]
    rw [hDf, ordDiff_smul x v (neg_ne_zero.mpr (pow_ne_zero 2 hf0))
      (Place.D_ne_zero_of_ord_ne_zero x v hinv0), ordDiff_D_of_ord_pos x v hinv, v.ord_neg,
      ← zpow_natCast, v.ord_zpow, v.ord_inv]
    push_cast
    ring
  · exact ordDiff_D_of_ord_pos x v hpos

include x in

theorem ordDiff_D_eq_ord_sub_algebraMap_sub_one (v : Place K F) {f : F} {c : K}
    (hfc : v.ord (f - algebraMap K F c) ≠ 0) :
    v.ordDiff (D K F f) = v.ord (f - algebraMap K F c) - 1 := by
  have : D K F f = D K F (f - algebraMap K F c) := by
    rw [map_sub, Derivation.map_algebraMap, sub_zero]
  rw [this, ordDiff_D_eq_ord_sub_one x v hfc]

end R4grade

end AlgebraicCurve.FF2R4A

end

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K F) {f : F} (hf : 0 ≤ v.ord f) :
    0 ≤ v.ordDiff (KaehlerDifferential.D K F f) :=
  AlgebraicCurve.FF2R4A.ordDiff_D_nonneg x v hf

end S_AlgebraicCurve_Place_ordDiff_D_nonneg
end P2MW
export P2MW.S_AlgebraicCurve_Place_ordDiff_D_nonneg (solution)
