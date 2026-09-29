-- Prove2me | solution 1 for AlgebraicCurve.Place.ordDiff_D_eq_ord_sub_algebraMap_sub_one_of_cast_natAbs_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/111c6372-3030-57ad-a767-f758c77998ea

import Mathlib
import Definitions.Def_AlgebraicCurve_Differentials
import Theorems.Thm_AlgebraicCurve_Place_ordDiff_smul_of_perfectField
import Theorems.Thm_AlgebraicCurve_Place_exists_ord_eq_one
import Theorems.Thm_AlgebraicCurve_Place_transcendental_of_ord_ne_zero
import Theorems.Thm_AlgebraicCurve_Place_isSeparable_adjoin_of_ord_eq_one
import Theorems.Thm_KaehlerDifferential_exists_unique_smul_D_of_transcendental
import Theorems.Thm_KaehlerDifferential_D_ne_zero_of_transcendental
import Theorems.Thm_AlgebraicCurve_Place_ord_diffCoeff_D_nonneg_of_isSeparable
import Theorems.Thm_AlgebraicCurve_Place_ord_add_eq_of_lt
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_nonneg_of_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_ordDiff_D_eq_ord_sub_algebraMap_sub_one_of_cast_natAbs_ne_zero
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open AlgebraicCurve KaehlerDifferential

namespace CDivJ
namespace TameOrder

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_algebraMap_eq_zero (w : Place K F) {c : K} (hc : c ≠ 0) :
    w.ord (algebraMap K F c) = 0 := by
  have hne : algebraMap K F c ≠ 0 := (map_ne_zero _).mpr hc
  have h1 : 0 ≤ w.ord (algebraMap K F c) :=
    (Place.mem_iff_ord_nonneg _ hne).mp (w.algebraMap_mem' c)
  have h2 : 0 ≤ w.ord (algebraMap K F c)⁻¹ := by
    rw [show (algebraMap K F c)⁻¹ = algebraMap K F c⁻¹ from (map_inv₀ _ c).symm]
    exact (Place.mem_iff_ord_nonneg _ ((map_ne_zero _).mpr (inv_ne_zero hc))).mp
      (w.algebraMap_mem' c⁻¹)
  rw [Place.ord_inv] at h2
  omega

theorem diffCoeff_eq_of_eq_smul {t : F} (hDt : D K F t ≠ 0) {ω : Ω[F⁄K]} {g : F}
    (h : ω = g • D K F t) : Place.diffCoeff t ω = g := by
  have h1 : Place.diffCoeff t ω • D K F t = ω := Place.diffCoeff_smul_D ⟨g, h⟩
  have h2 : (Place.diffCoeff t ω - g) • D K F t = 0 := by
    rw [sub_smul, h1, h, sub_self]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact sub_eq_zero.mp h3
  · exact absurd h3 hDt

variable [PerfectField K]

theorem exists_good_coeff (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (w : Place K F) {s : F} {e : ℕ} (hepos : 0 < e) (hords : w.ord s = (e : ℤ))
    (he : ((e : ℕ) : K) ≠ 0) :
    ∃ g₀ : F, g₀ ≠ 0 ∧ D K F s = g₀ • D K F w.uniformizer_alt ∧ w.ord g₀ = (e : ℤ) - 1 := by
  classical
  have hsne : s ≠ 0 := by
    intro h0
    rw [h0, Place.ord_zero] at hords
    omega
  set u := w.uniformizer_alt with hudef
  have hu1 : w.ord u = 1 := w.ord_uniformizer_alt w.exists_ord_eq_one
  have hune : u ≠ 0 := by
    intro h0
    rw [h0, Place.ord_zero] at hu1
    exact one_ne_zero hu1.symm
  have hupow : u ^ (e : ℕ) ≠ 0 := pow_ne_zero _ hune
  have hordupow : w.ord (u ^ (e : ℕ)) = (e : ℤ) := by
    rw [show u ^ (e : ℕ) = u ^ ((e : ℕ) : ℤ) from (zpow_natCast u e).symm,
      Place.ord_zpow, hu1, mul_one]
  set c : F := s / u ^ (e : ℕ) with hcdef
  have hcne : c ≠ 0 := div_ne_zero hsne hupow
  have hordc : w.ord c = 0 := by
    rw [hcdef, div_eq_mul_inv, w.ord_mul hsne (inv_ne_zero hupow), Place.ord_inv,
      hordupow, hords]
    ring
  have hs_eq : s = c * u ^ (e : ℕ) := (div_mul_cancel₀ s hupow).symm
  have heF : ((e : ℕ) : F) ≠ 0 := by
    rw [show ((e : ℕ) : F) = algebraMap K F ((e : ℕ) : K) from (map_natCast _ e).symm]
    exact (map_ne_zero _).mpr he
  have hordeF : w.ord ((e : ℕ) : F) = 0 := by
    rw [show ((e : ℕ) : F) = algebraMap K F ((e : ℕ) : K) from (map_natCast _ e).symm]
    exact ord_algebraMap_eq_zero w he
  have htr : Transcendental K u := w.transcendental_of_ord_ne_zero (by rw [hu1]; exact one_ne_zero)
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F :=
    Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsSeparable (IntermediateField.adjoin K ({u} : Set F)) F :=
    Place.isSeparable_adjoin_of_ord_eq_one x w hu1
  have hDu : D K F u ≠ 0 := KaehlerDifferential.D_ne_zero_of_transcendental K u htr
  set cv := Place.diffCoeff u (D K F c) with hcvdef
  have hDc : D K F c = cv • D K F u :=
    (Place.diffCoeff_smul_D
      ((KaehlerDifferential.exists_unique_smul_D_of_transcendental K u htr (D K F c)).exists)).symm
  have hcv0 : 0 ≤ w.ord cv :=
    Place.ord_diffCoeff_D_nonneg_of_isSeparable x w hu1 (le_of_eq hordc.symm)
  have hD : D K F s = (c * ((e : ℕ) : F) * u ^ ((e : ℕ) - 1) + u ^ (e : ℕ) * cv) • D K F u := by
    conv_lhs => rw [hs_eq]
    rw [Derivation.leibniz, Derivation.leibniz_pow, hDc]
    rw [← Nat.cast_smul_eq_nsmul F e (u ^ ((e : ℕ) - 1) • D K F u)]
    rw [smul_smul, smul_smul, smul_smul, ← add_smul]
  have hmne : c * ((e : ℕ) : F) * u ^ ((e : ℕ) - 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hcne heF) (pow_ne_zero _ hune)
  have hordmain : w.ord (c * ((e : ℕ) : F) * u ^ ((e : ℕ) - 1)) = (e : ℤ) - 1 := by
    rw [w.ord_mul (mul_ne_zero hcne heF) (pow_ne_zero _ hune),
      w.ord_mul hcne heF, hordc, hordeF,
      show u ^ ((e : ℕ) - 1) = u ^ (((e : ℕ) - 1 : ℕ) : ℤ) from (zpow_natCast u _).symm,
      Place.ord_zpow, hu1, mul_one]
    have : (((e : ℕ) - 1 : ℕ) : ℤ) = (e : ℤ) - 1 := by omega
    omega
  refine ⟨c * ((e : ℕ) : F) * u ^ ((e : ℕ) - 1) + u ^ (e : ℕ) * cv, ?_, hD, ?_⟩
  · by_cases hcv : cv = 0
    · rw [hcv, mul_zero, add_zero]
      exact hmne
    · intro h0
      have h1 : c * ((e : ℕ) : F) * u ^ ((e : ℕ) - 1) = -(u ^ (e : ℕ) * cv) := by
        linear_combination h0
      have h2 : w.ord (c * ((e : ℕ) : F) * u ^ ((e : ℕ) - 1))
          = w.ord (u ^ (e : ℕ) * cv) := by
        rw [h1, show -(u ^ (e : ℕ) * cv) = (-1 : F) * (u ^ (e : ℕ) * cv) by ring,
          w.ord_mul (by norm_num) (mul_ne_zero hupow hcv),
          show w.ord (-1 : F) = 0 from by
            rw [show (-1 : F) = algebraMap K F (-1) from by rw [map_neg, map_one]]
            exact ord_algebraMap_eq_zero w (by norm_num), zero_add]
      rw [hordmain, w.ord_mul hupow hcv, hordupow] at h2
      omega
  · by_cases hcv : cv = 0
    · rw [hcv, mul_zero, add_zero, hordmain]
    · have hord2 : w.ord (u ^ (e : ℕ) * cv) = (e : ℤ) + w.ord cv := by
        rw [w.ord_mul hupow hcv, hordupow]
      have hlt : w.ord (c * ((e : ℕ) : F) * u ^ ((e : ℕ) - 1))
          < w.ord (u ^ (e : ℕ) * cv) := by
        rw [hordmain, hord2]
        omega
      rw [Place.ord_add_eq_of_lt w hmne (mul_ne_zero hupow hcv) hlt, hordmain]

theorem ordDiff_D_of_pos (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (w : Place K F) {s : F} {e : ℕ} (hepos : 0 < e) (hords : w.ord s = (e : ℤ))
    (he : ((e : ℕ) : K) ≠ 0) :
    D K F s ≠ 0 ∧ w.ordDiff (D K F s) = (e : ℤ) - 1 := by
  obtain ⟨g₀, hg₀, hDeq, hord⟩ := exists_good_coeff x w hepos hords he
  have hu1 : w.ord w.uniformizer_alt = 1 := w.ord_uniformizer_alt w.exists_ord_eq_one
  have htr : Transcendental K w.uniformizer_alt :=
    w.transcendental_of_ord_ne_zero (by rw [hu1]; exact one_ne_zero)
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F :=
    Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsSeparable (IntermediateField.adjoin K ({w.uniformizer_alt} : Set F)) F :=
    Place.isSeparable_adjoin_of_ord_eq_one x w hu1
  have hDu : D K F w.uniformizer_alt ≠ 0 := KaehlerDifferential.D_ne_zero_of_transcendental K _ htr
  refine ⟨?_, ?_⟩
  · rw [hDeq]; exact smul_ne_zero hg₀ hDu
  · rw [Place.ordDiff_def, diffCoeff_eq_of_eq_smul hDu hDeq, hord]

theorem ordDiff_D_of_ne_zero (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (w : Place K F) {f : F} (hf : w.ord f ≠ 0) (ht : (((w.ord f).natAbs : ℕ) : K) ≠ 0) :
    w.ordDiff (D K F f) = w.ord f - 1 := by
  have hf0 : f ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at hf; exact hf rfl
  rcases lt_or_gt_of_ne hf with hneg | hpos
  ·
    have hordinv : w.ord f⁻¹ = ((w.ord f).natAbs : ℤ) := by
      rw [Place.ord_inv]; omega
    have hepos : 0 < (w.ord f).natAbs := Int.natAbs_pos.mpr hf
    obtain ⟨hDinv, hordD⟩ := ordDiff_D_of_pos x w hepos hordinv ht

    have hrel : D K F f = (-(f ^ 2)) • D K F f⁻¹ := by
      have h1 : D K F (f * f⁻¹) = 0 := by rw [mul_inv_cancel₀ hf0, Derivation.map_one_eq_zero]
      rw [Derivation.leibniz] at h1

      have h2 : f⁻¹ • D K F f = -(f • D K F f⁻¹) := eq_neg_of_add_eq_zero_right h1
      have h3 : D K F f = f • (f⁻¹ • D K F f) := by rw [smul_smul, mul_inv_cancel₀ hf0, one_smul]
      rw [h3, h2, smul_neg, smul_smul, ← neg_smul, pow_two]
    haveI : Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F :=
      Algebra.IsAlgebraic.of_finite _ _
    rw [hrel, Place.ordDiff_smul_of_perfectField x w (neg_ne_zero.mpr (pow_ne_zero 2 hf0)) hDinv, hordD,
      show -(f ^ 2) = (-1 : F) * f ^ 2 by ring, w.ord_mul (by norm_num) (pow_ne_zero 2 hf0),
      show w.ord (-1 : F) = 0 from by
        rw [show (-1 : F) = algebraMap K F (-1) from by rw [map_neg, map_one]]
        exact ord_algebraMap_eq_zero w (by norm_num),
      show f ^ 2 = f ^ ((2 : ℕ) : ℤ) from (zpow_natCast f 2).symm, Place.ord_zpow]
    omega
  · have hords : w.ord f = (((w.ord f).natAbs : ℕ) : ℤ) := by omega
    have hepos : 0 < (w.ord f).natAbs := Int.natAbs_pos.mpr hf
    obtain ⟨-, hordD⟩ := ordDiff_D_of_pos x w hepos hords ht
    rw [hordD]; omega

end CDivJ.TameOrder

open CDivJ.TameOrder in
theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (v : AlgebraicCurve.Place K F) {f : F} {c : K}
    (hfc : v.ord (f - algebraMap K F c) ≠ 0)
    (htame : (((v.ord (f - algebraMap K F c)).natAbs : ℕ) : K) ≠ 0) :
    v.ordDiff (KaehlerDifferential.D K F f) = v.ord (f - algebraMap K F c) - 1 :=
  by
  have h := ordDiff_D_of_ne_zero x v hfc htame
  rwa [Derivation.map_sub, Derivation.map_algebraMap, sub_zero] at h

end S_AlgebraicCurve_Place_ordDiff_D_eq_ord_sub_algebraMap_sub_one_of_cast_natAbs_ne_zero
end P2MW
export P2MW.S_AlgebraicCurve_Place_ordDiff_D_eq_ord_sub_algebraMap_sub_one_of_cast_natAbs_ne_zero (solution)
