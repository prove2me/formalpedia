-- Prove2me | solution 1 for AlgebraicCurve.Place.exists_finset_forall_ord_sub_algebraMap_eq_one_of_ord_pos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/547c3813-8039-5ae6-a663-816380223102

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Differentials
import Definitions.Def_AlgebraicCurve_Repartitions
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
import Theorems.Thm_AlgebraicCurve_sum_ordDiff_D_le_two_mul_genusFF_of_isSeparable
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_exists_finset_forall_ord_sub_algebraMap_eq_one_of_ord_pos
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"

set_option autoImplicit false

open AlgebraicCurve KaehlerDifferential

namespace CritFin

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

theorem eq_of_ord_sub_algebraMap_pos (w : Place K F) {x : F} {a b : K}
    (ha : 0 < w.ord (x - algebraMap K F a)) (hb : 0 < w.ord (x - algebraMap K F b)) : a = b := by
  by_contra hab
  have hconst : x - algebraMap K F a = algebraMap K F (b - a) + (x - algebraMap K F b) := by
    rw [map_sub]; ring
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have h0 : w.ord (algebraMap K F (b - a)) = 0 := ord_algebraMap_eq_zero w hba
  have hxb : x - algebraMap K F b ≠ 0 := by
    intro h
    rw [h, Place.ord_zero] at hb
    exact lt_irrefl _ hb
  have h := Place.ord_add_eq_of_lt w ((map_ne_zero _).mpr hba) hxb (by rw [h0]; exact hb)
  rw [← hconst, h0] at h
  rw [h] at ha
  exact lt_irrefl _ ha

variable [PerfectField K]

theorem exists_coeff_ord_ge (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (w : Place K F) {s : F} {e : ℕ} (hepos : 0 < e) (hords : w.ord s = (e : ℤ)) :
    ∃ g : F, D K F s = g • D K F w.uniformizer_alt ∧ (g = 0 ∨ (e : ℤ) - 1 ≤ w.ord g) := by
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
  refine ⟨c * ((e : ℕ) : F) * u ^ ((e : ℕ) - 1) + u ^ (e : ℕ) * cv, hD, ?_⟩

  have hordr : cv ≠ 0 → w.ord (u ^ (e : ℕ) * cv) = (e : ℤ) + w.ord cv := fun hcv => by
    rw [w.ord_mul hupow hcv, hordupow]
  by_cases hm : c * ((e : ℕ) : F) * u ^ ((e : ℕ) - 1) = 0
  ·
    rw [hm, zero_add]
    by_cases hcv : cv = 0
    · exact Or.inl (by rw [hcv, mul_zero])
    · right
      rw [hordr hcv]
      omega
  ·
    right
    have heF : ((e : ℕ) : F) ≠ 0 := fun h0 => hm (by rw [h0, mul_zero, zero_mul])
    have he : ((e : ℕ) : K) ≠ 0 := fun h0 => heF (by
      rw [show ((e : ℕ) : F) = algebraMap K F ((e : ℕ) : K) from (map_natCast _ e).symm, h0, map_zero])
    have hordeF : w.ord ((e : ℕ) : F) = 0 := by
      rw [show ((e : ℕ) : F) = algebraMap K F ((e : ℕ) : K) from (map_natCast _ e).symm]
      exact ord_algebraMap_eq_zero w he
    have hordmain : w.ord (c * ((e : ℕ) : F) * u ^ ((e : ℕ) - 1)) = (e : ℤ) - 1 := by
      rw [w.ord_mul (mul_ne_zero hcne heF) (pow_ne_zero _ hune),
        w.ord_mul hcne heF, hordc, hordeF,
        show u ^ ((e : ℕ) - 1) = u ^ (((e : ℕ) - 1 : ℕ) : ℤ) from (zpow_natCast u _).symm,
        Place.ord_zpow, hu1, mul_one]
      have : (((e : ℕ) - 1 : ℕ) : ℤ) = (e : ℤ) - 1 := by omega
      omega
    by_cases hcv : cv = 0
    · rw [hcv, mul_zero, add_zero, hordmain]
    · have hlt : w.ord (c * ((e : ℕ) : F) * u ^ ((e : ℕ) - 1)) < w.ord (u ^ (e : ℕ) * cv) := by
        rw [hordmain, hordr hcv]
        omega
      rw [Place.ord_add_eq_of_lt w hm (mul_ne_zero hupow hcv) hlt, hordmain]

theorem one_le_ordDiff_D (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (hx : Transcendental K x) [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F]
    (w : Place K F) {a : K} (h2 : 2 ≤ w.ord (x - algebraMap K F a)) :
    1 ≤ w.ordDiff (D K F x) := by
  have hords : w.ord (x - algebraMap K F a) = (((w.ord (x - algebraMap K F a)).toNat : ℕ) : ℤ) := by omega
  have hepos : 0 < (w.ord (x - algebraMap K F a)).toNat := by omega
  obtain ⟨g, hDeq, hg⟩ := exists_coeff_ord_ge x w hepos hords
  have hDx : D K F (x - algebraMap K F a) = D K F x := by
    rw [Derivation.map_sub, Derivation.map_algebraMap, sub_zero]
  rw [hDx] at hDeq
  have hDx0 : D K F x ≠ 0 := KaehlerDifferential.D_ne_zero_of_transcendental K x hx
  have hu1 : w.ord w.uniformizer_alt = 1 := w.ord_uniformizer_alt w.exists_ord_eq_one
  have htr : Transcendental K w.uniformizer_alt :=
    w.transcendental_of_ord_ne_zero (by rw [hu1]; exact one_ne_zero)
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F :=
    Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsSeparable (IntermediateField.adjoin K ({w.uniformizer_alt} : Set F)) F :=
    Place.isSeparable_adjoin_of_ord_eq_one x w hu1
  have hDu : D K F w.uniformizer_alt ≠ 0 := KaehlerDifferential.D_ne_zero_of_transcendental K _ htr
  have hg0 : g ≠ 0 := fun h0 => hDx0 (by rw [hDeq, h0, zero_smul])
  rcases hg with h | h
  · exact absurd h hg0
  · rw [Place.ordDiff_def, diffCoeff_eq_of_eq_smul hDu hDeq]
    omega

end CritFin

open CritFin in

theorem solution
    {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F] [IsCurveOver K F]
    (x : F) (hx : Transcendental K x)
    (hfd : FiniteDimensional ↥(IntermediateField.adjoin K ({x} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K ({x} : Set F)) F) :
    ∃ C : Finset K, ∀ c : K, c ∉ C → ∀ v : AlgebraicCurve.Place K F,
      0 < v.ord (x - algebraMap K F c) → v.ord (x - algebraMap K F c) = 1 := by
  classical
  haveI : PerfectField K := inferInstance
  haveI := hfd
  haveI := hsep

  let Ram : Set (AlgebraicCurve.Place K F) := {P | ∃ a : K, 2 ≤ P.ord (x - algebraMap K F a)}

  have hbound : ∀ T : Finset (AlgebraicCurve.Place K F), (↑T : Set (AlgebraicCurve.Place K F)) ⊆ Ram →
      (T.card : ℤ) ≤ 2 * (genusFF K F : ℤ) - 2 +
        2 * (Module.finrank (IntermediateField.adjoin K ({x} : Set F)) F : ℤ) := by
    intro T hT
    have hT0 : ∀ P ∈ T, 0 ≤ P.ord x := by
      intro P hP
      obtain ⟨a, ha⟩ := hT hP
      have hxa : x - algebraMap K F a ≠ 0 := by
        intro h
        rw [h, Place.ord_zero] at ha
        omega
      have hmem : x - algebraMap K F a ∈ P.toValuationSubring :=
        (Place.mem_iff_ord_nonneg _ hxa).mpr (by omega)
      have hx' : x = (x - algebraMap K F a) + algebraMap K F a := by ring
      rw [hx']
      exact Place.ord_nonneg_of_mem _ (add_mem hmem (P.algebraMap_mem' a))
    have h := AlgebraicCurve.sum_ordDiff_D_le_two_mul_genusFF_of_isSeparable K x hx hfd hsep T hT0 ∅
      (fun P hP => absurd hP (Finset.notMem_empty P))
    rw [Finset.sum_empty, add_zero] at h
    have h1 : ∀ P ∈ T, (1 : ℤ) ≤ P.ordDiff (KaehlerDifferential.D K F x) := fun P hP =>
      (hT hP).elim fun a ha => CritFin.one_le_ordDiff_D x hx P ha
    calc (T.card : ℤ) = ∑ P ∈ T, (1 : ℤ) := by simp
      _ ≤ ∑ P ∈ T, P.ordDiff (KaehlerDifferential.D K F x) := Finset.sum_le_sum h1
      _ ≤ _ := h
  have hfin : Ram.Finite := by
    by_contra hinf
    obtain ⟨T, hT, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf
      ((2 * (genusFF K F : ℤ) - 2 + 2 * (Module.finrank (IntermediateField.adjoin K ({x} : Set F)) F : ℤ)).toNat + 1)
    have h := hbound T hT
    rw [hcard] at h
    omega

  refine ⟨hfin.toFinset.image fun P => if h : P ∈ Ram then Classical.choose h else 0, ?_⟩
  intro c hc v hv
  by_contra hne
  have hvR : v ∈ Ram := ⟨c, by omega⟩
  have ha : 2 ≤ v.ord (x - algebraMap K F (Classical.choose hvR)) := Classical.choose_spec hvR
  have heq : Classical.choose hvR = c := CritFin.eq_of_ord_sub_algebraMap_pos v (by omega) hv
  exact hc (Finset.mem_image.mpr ⟨v, hfin.mem_toFinset.mpr hvR, by rw [dif_pos hvR, heq]⟩)

end S_AlgebraicCurve_Place_exists_finset_forall_ord_sub_algebraMap_eq_one_of_ord_pos
end P2MW
export P2MW.S_AlgebraicCurve_Place_exists_finset_forall_ord_sub_algebraMap_eq_one_of_ord_pos (solution)
