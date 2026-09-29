-- Prove2me | solution 1 for AlgebraicCurve.Place.ord_sub_one_le_ordDiff_D_of_perfectField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/024f34bb-0e9b-507a-a512-678f85b797e7

import Definitions.Def_AlgebraicCurve_Differentials
import Theorems.Thm_AlgebraicCurve_Place_diffCoeff_smul_D_of_ord_eq_one
import Theorems.Thm_AlgebraicCurve_Place_diffCoeff_smul_D_eq_of_ord_eq_one
import Theorems.Thm_AlgebraicCurve_Place_ord_diffCoeff_D_nonneg_of_perfectField
import Theorems.Thm_AlgebraicCurve_Place_exists_ord_eq_one
import Theorems.Thm_AlgebraicCurve_Place_min_ord_le_ord_add
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_ord_sub_one_le_ordDiff_D_of_perfectField
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place"
namespace Place
p2m_export "AlgebraicCurve.Place" "diffCoeff ordDiff ordDiff_def ord_uniformizer_alt uniformizer_alt ord ord_zero ord_mul ord_inv ord_zpow diffCoeff_smul_D_of_ord_eq_one diffCoeff_smul_D_eq_of_ord_eq_one ord_diffCoeff_D_nonneg_of_perfectField exists_ord_eq_one min_ord_le_ord_add ord_algebraMap"
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem _root_.AlgebraicCurve.Place.ordDiff_smul_impl [PerfectField K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K F)
    {g : F} (hg : g ≠ 0) {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    v.ordDiff (g • ω) = v.ord g + v.ordDiff ω := by
  have ht : v.ord v.uniformizer_alt = 1 := v.ord_uniformizer_alt v.exists_ord_eq_one
  have hrep : diffCoeff v.uniformizer_alt ω • KaehlerDifferential.D K F v.uniformizer_alt = ω :=
    v.diffCoeff_smul_D_of_ord_eq_one x ht ω
  have hgo : g • ω = (g * diffCoeff v.uniformizer_alt ω) • KaehlerDifferential.D K F v.uniformizer_alt := by
    conv_lhs => rw [← hrep]
    rw [smul_smul]
  have hco : diffCoeff v.uniformizer_alt (g • ω) = g * diffCoeff v.uniformizer_alt ω := by
    rw [hgo]
    exact v.diffCoeff_smul_D_eq_of_ord_eq_one x ht _
  have hc0 : diffCoeff v.uniformizer_alt ω ≠ 0 := by
    intro h0
    apply hω
    rw [← hrep, h0, zero_smul]
  rw [ordDiff_def, ordDiff_def, hco, v.ord_mul hg hc0]

p2m_export "AlgebraicCurve.Place" "ordDiff_smul_impl"
private theorem ord_pow_nat (v : AlgebraicCurve.Place K F) (t : F) (m : ℕ) :
    v.ord (t ^ m) = (m : ℤ) * v.ord t := by
  rw [← zpow_natCast t m, v.ord_zpow]

private theorem _root_.AlgebraicCurve.Place.H2_pos [PerfectField K] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K F)
    {f : F} (hD : KaehlerDifferential.D K F f ≠ 0) (hn : 0 ≤ v.ord f) :
    v.ord f - 1 ≤ v.ordDiff (KaehlerDifferential.D K F f) := by
  have ht : v.ord v.uniformizer_alt = 1 := v.ord_uniformizer_alt v.exists_ord_eq_one
  set t := v.uniformizer_alt with htdef
  have ht0 : t ≠ 0 := by
    intro h0
    rw [h0, v.ord_zero] at ht
    omega
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [map_zero] at hD
    exact hD rfl
  set m : ℕ := (v.ord f).toNat with hmdef
  have hm : (m : ℤ) = v.ord f := Int.toNat_of_nonneg hn
  have htm0 : t ^ m ≠ 0 := pow_ne_zero m ht0
  set u : F := f * (t ^ m)⁻¹ with hudef
  have hu0 : u ≠ 0 := mul_ne_zero hf0 (inv_ne_zero htm0)
  have hordu : v.ord u = 0 := by
    rw [hudef, v.ord_mul hf0 (inv_ne_zero htm0), v.ord_inv, ord_pow_nat, ht, hm]
    ring
  have hfeq : f = u * t ^ m := by
    rw [hudef, mul_assoc, inv_mul_cancel₀ htm0, mul_one]

  set cu : F := diffCoeff t (KaehlerDifferential.D K F u) with hcudef
  have hcu_nonneg : 0 ≤ v.ord cu :=
    v.ord_diffCoeff_D_nonneg_of_perfectField x ht (le_of_eq hordu.symm)
  have hrepu : cu • KaehlerDifferential.D K F t = KaehlerDifferential.D K F u :=
    v.diffCoeff_smul_D_of_ord_eq_one x ht _
  have hDtm : KaehlerDifferential.D K F (t ^ m) =
      ((m : F) * t ^ (m - 1)) • KaehlerDifferential.D K F t := by
    rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul F m, smul_smul]
  have hdecomp : KaehlerDifferential.D K F f =
      (u * ((m : F) * t ^ (m - 1)) + t ^ m * cu) • KaehlerDifferential.D K F t := by
    conv_lhs => rw [hfeq]
    rw [Derivation.leibniz, hDtm, ← hrepu, smul_smul, smul_smul, add_smul]
  have hcoeff : diffCoeff t (KaehlerDifferential.D K F f) =
      u * ((m : F) * t ^ (m - 1)) + t ^ m * cu := by
    rw [hdecomp]
    exact v.diffCoeff_smul_D_eq_of_ord_eq_one x ht _
  have hsum0 : u * ((m : F) * t ^ (m - 1)) + t ^ m * cu ≠ 0 := by
    intro h0
    apply hD
    rw [hdecomp, h0, zero_smul]
  rw [ordDiff_def, ← htdef, hcoeff]
  rcases eq_or_ne (u * ((m : F) * t ^ (m - 1))) 0 with ha | ha
  ·
    rw [ha, zero_add] at hsum0 ⊢
    have hcu0 : cu ≠ 0 := fun h => hsum0 (by rw [h, mul_zero])
    rw [v.ord_mul htm0 hcu0, ord_pow_nat, ht]
    omega
  · have hmF : (m : F) ≠ 0 := by
      intro h
      exact ha (by rw [h, zero_mul, mul_zero])
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · exact absurd (by rw [h, Nat.cast_zero] : (m : F) = 0) hmF
      · exact h
    have hordm : v.ord ((m : F)) = 0 := by
      have hcast : ((m : F)) = algebraMap K F ((m : K)) := by
        rw [map_natCast]
      rw [hcast, v.ord_algebraMap]
    have horda : v.ord (u * ((m : F) * t ^ (m - 1))) = (m : ℤ) - 1 := by
      have h1 : (m : F) * t ^ (m - 1) ≠ 0 := mul_ne_zero hmF (pow_ne_zero _ ht0)
      rw [v.ord_mul hu0 h1, v.ord_mul hmF (pow_ne_zero _ ht0), ord_pow_nat, ht, hordu, hordm]
      have : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by
        omega
      rw [this]
      ring
    rcases eq_or_ne cu 0 with hcu0 | hcu0
    ·
      rw [hcu0, mul_zero, add_zero, horda]
      omega
    · have hordb : v.ord (t ^ m * cu) = (m : ℤ) + v.ord cu := by
        rw [v.ord_mul htm0 hcu0, ord_pow_nat, ht]
        ring
      have hmin := v.min_ord_le_ord_add ha (by exact mul_ne_zero htm0 hcu0) hsum0
      rw [horda, hordb] at hmin
      have : min ((m : ℤ) - 1) ((m : ℤ) + v.ord cu) = (m : ℤ) - 1 := by
        omega
      rw [this] at hmin
      omega

p2m_export "AlgebraicCurve.Place" "H2_pos"
private theorem H2_impl [PerfectField K] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K F)
    {f : F} (hD : KaehlerDifferential.D K F f ≠ 0) :
    v.ord f - 1 ≤ v.ordDiff (KaehlerDifferential.D K F f) := by
  rcases le_or_gt 0 (v.ord f) with hn | hn
  · exact v.H2_pos x hD hn
  ·
    have hf0 : f ≠ 0 := by
      rintro rfl
      rw [map_zero] at hD
      exact hD rfl
    have hDinv : KaehlerDifferential.D K F f⁻¹ ≠ 0 := by
      intro h0
      apply hD
      have hleib := Derivation.leibniz_inv (KaehlerDifferential.D K F) f
      rw [h0] at hleib
      have hne : (-f⁻¹ ^ 2 : F) ≠ 0 := by
        simpa using hf0
      rcases smul_eq_zero.mp hleib.symm with h | h
      · exact absurd h hne
      · exact h
    have hpos := v.H2_pos x hDinv (by rw [v.ord_inv]; omega)
    have hleib := Derivation.leibniz_inv (KaehlerDifferential.D K F) f
    have hsmul : v.ordDiff (KaehlerDifferential.D K F f⁻¹) =
        v.ord (-f⁻¹ ^ 2) + v.ordDiff (KaehlerDifferential.D K F f) := by
      rw [hleib]
      exact v.ordDiff_smul_impl x (by simpa using hf0) hD
    have hordneg : v.ord (-f⁻¹ ^ 2 : F) = -2 * v.ord f := by
      have hneg1 : (-f⁻¹ ^ 2 : F) = algebraMap K F (-1) * f⁻¹ ^ 2 := by
        rw [map_neg, map_one]
        ring
      have h2 : (f⁻¹ ^ 2 : F) ≠ 0 := by
        simpa using hf0
      have hneg1ne : algebraMap K F (-1) ≠ 0 := by
        rw [map_neg, map_one]
        exact neg_ne_zero.mpr one_ne_zero
      rw [hneg1, v.ord_mul hneg1ne h2,
        v.ord_algebraMap, ← zpow_natCast (f⁻¹) 2, v.ord_zpow, v.ord_inv]
      ring
    rw [v.ord_inv] at hpos
    rw [hsmul, hordneg] at hpos
    omega

end AlgebraicCurve.Place

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K F) {f : F}
    (hD : KaehlerDifferential.D K F f ≠ 0) :
    v.ord f - 1 ≤ v.ordDiff (KaehlerDifferential.D K F f) :=
  AlgebraicCurve.Place.H2_impl x v hD

end S_AlgebraicCurve_Place_ord_sub_one_le_ordDiff_D_of_perfectField
end P2MW
export P2MW.S_AlgebraicCurve_Place_ord_sub_one_le_ordDiff_D_of_perfectField (solution)
