-- Prove2me | solution 1 for AlgebraicCurve.SemistableCovering.exists_mem_riemannRochSpace_forall_residue_eq_of_glued_of_rankOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/0198b85c-7229-524f-8ec3-018aeb251598

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_AlgebraicCurve_SemistableCovering_exists_linearIndependent_pi_residue_of_mem_riemannRochSpace_of_rankOne
import Theorems.Thm_AlgebraicCurve_Annulus_ord_residue_nonneg_and_evalAt_residue_eq_of_isAttached_of_isAttached
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Theorems.Thm_AlgebraicCurve_ell_eq_degree_add_one_sub_genusFF_of_isAlgClosed_of_isSeparable
import Theorems.Thm_AlgebraicCurve_ell_le_ell_sub_single_add_deg
import Theorems.Thm_AlgebraicCurve_degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental
import Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_SemistableCovering_exists_mem_riemannRochSpace_forall_residue_eq_of_glued_of_rankOne
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.Gamma0Pair.isElliptic AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff"
p2m_attr_erase "simp" "ModularCurve.coeffMap_id ModularCurve.coeffMap_single AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk"
p2m_attr_erase "simp" "ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

p2m_open "AlgebraicCurve~genus IsLocalRing"

namespace K3TwistedLift

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]

section Red

variable {Fb : Type*} [Field Fb] [Algebra (ResidueField A) Fb]

open Classical in

def red (C : ComponentChart A F Fb) (u : F) : Fb :=
  if h : u ∈ C.integers then C.residue ⟨u, h⟩ else 0

theorem red_of_mem (C : ComponentChart A F Fb) {u : F} (h : u ∈ C.integers) :
    red C u = C.residue ⟨u, h⟩ := by
  simp only [red, dif_pos h]

theorem red_zero (C : ComponentChart A F Fb) : red C (0 : F) = 0 := by
  rw [red_of_mem C (zero_mem _)]
  have : (⟨(0 : F), zero_mem _⟩ : C.integers) = 0 := rfl
  rw [this, map_zero]

theorem red_one (C : ComponentChart A F Fb) : red C (1 : F) = 1 := by
  rw [red_of_mem C (one_mem _)]
  have : (⟨(1 : F), one_mem _⟩ : C.integers) = 1 := rfl
  rw [this, map_one]

theorem red_add (C : ComponentChart A F Fb) {u v : F} (hu : u ∈ C.integers) (hv : v ∈ C.integers) :
    red C (u + v) = red C u + red C v := by
  rw [red_of_mem C (add_mem hu hv), red_of_mem C hu, red_of_mem C hv, ← map_add]
  rfl

theorem red_mul (C : ComponentChart A F Fb) {u v : F} (hu : u ∈ C.integers) (hv : v ∈ C.integers) :
    red C (u * v) = red C u * red C v := by
  rw [red_of_mem C (mul_mem hu hv), red_of_mem C hu, red_of_mem C hv, ← map_mul]
  rfl

theorem red_neg (C : ComponentChart A F Fb) {u : F} (hu : u ∈ C.integers) :
    red C (-u) = -red C u := by
  rw [red_of_mem C (neg_mem hu), red_of_mem C hu, ← map_neg]
  rfl

theorem red_sub (C : ComponentChart A F Fb) {u v : F} (hu : u ∈ C.integers) (hv : v ∈ C.integers) :
    red C (u - v) = red C u - red C v := by
  rw [sub_eq_add_neg, red_add C hu (neg_mem hv), red_neg C hv, sub_eq_add_neg]

theorem algebraMap_mem (C : ComponentChart A F Fb) (a : A) : algebraMap L F (a : L) ∈ C.integers :=
  (C.algebraMap_mem_iff _).mpr a.2

theorem red_algebraMap (C : ComponentChart A F Fb) (a : A) :
    red C (algebraMap L F (a : L)) = algebraMap (ResidueField A) Fb (residue A a) := by
  rw [red_of_mem C (algebraMap_mem C a)]
  exact C.residue_algebraMap a

private theorem _root_.K3TwistedLift.smul_mem (C : ComponentChart A F Fb) (a : A) {u : F} (hu : u ∈ C.integers) :
    (a : L) • u ∈ C.integers := by
  rw [Algebra.smul_def]
  exact mul_mem (algebraMap_mem C a) hu

p2m_export "K3TwistedLift" "smul_mem"
theorem red_smul (C : ComponentChart A F Fb) (a : A) {u : F} (hu : u ∈ C.integers) :
    red C ((a : L) • u) = (residue A a) • red C u := by
  rw [Algebra.smul_def, red_mul C (algebraMap_mem C a) hu, red_algebraMap, Algebra.smul_def]

theorem sum_smul_mem (C : ComponentChart A F Fb) {k : ℕ} (γ : Fin k → A) (b : Fin k → F)
    (hb : ∀ j, b j ∈ C.integers) : ∑ j, (γ j : L) • b j ∈ C.integers :=
  Subring.sum_mem _ fun j _ => smul_mem C (γ j) (hb j)

theorem red_sum_smul (C : ComponentChart A F Fb) {k : ℕ} (γ : Fin k → A) (b : Fin k → F)
    (hb : ∀ j, b j ∈ C.integers) :
    red C (∑ j, (γ j : L) • b j) = ∑ j, (residue A (γ j)) • red C (b j) := by
  classical
  induction (Finset.univ : Finset (Fin k)) using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact red_zero C
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, red_add C (smul_mem C _ (hb j))
      (Subring.sum_mem _ fun i _ => smul_mem C (γ i) (hb i)), red_smul C _ (hb j), ih]

theorem isUnit_of_red_ne_zero (C : ComponentChart A F Fb) {u : F} (hu : u ∈ C.integers)
    (h : red C u ≠ 0) : IsUnit (⟨u, hu⟩ : C.integers) := by
  by_contra hnu
  apply h
  rw [red_of_mem C hu]
  have hmem : (⟨u, hu⟩ : C.integers) ∈ maximalIdeal C.integers := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; exact hnu
  rw [← C.ker_residue, RingHom.mem_ker] at hmem
  exact hmem

theorem inv_mem_of_red_ne_zero (C : ComponentChart A F Fb) {u : F} (hu : u ∈ C.integers)
    (h : red C u ≠ 0) : u⁻¹ ∈ C.integers := by
  obtain ⟨w, hw⟩ := isUnit_of_red_ne_zero C hu h
  have hu0 : u ≠ 0 := by
    rintro rfl; exact h (red_zero C)
  have hwF : ((w : C.integers) : F) = u := by rw [hw]
  have hinv : u⁻¹ = ((w⁻¹ : C.integersˣ) : C.integers) := by
    have h1 : ((w : C.integers) : F) * ((w⁻¹ : C.integersˣ) : C.integers) = 1 := by
      rw [← Subring.coe_mul]
      have : ((w * w⁻¹ : C.integersˣ) : C.integers) = 1 := by rw [mul_inv_cancel]; rfl
      have h2 : ((w : C.integers) : C.integers) * ((w⁻¹ : C.integersˣ) : C.integers) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      rw [h2]; rfl
    rw [hwF] at h1
    exact (eq_inv_of_mul_eq_one_right h1).symm
  rw [hinv]
  exact SetLike.coe_mem _

theorem red_inv (C : ComponentChart A F Fb) {u : F} (hu : u ∈ C.integers) (h : red C u ≠ 0) :
    red C u⁻¹ = (red C u)⁻¹ := by
  have hu0 : u ≠ 0 := by
    rintro rfl; exact h (red_zero C)
  have hi := inv_mem_of_red_ne_zero C hu h
  have h1 : red C u * red C u⁻¹ = 1 := by
    rw [← red_mul C hu hi, mul_inv_cancel₀ hu0, red_one]
  exact (eq_inv_of_mul_eq_one_right h1)

theorem ne_zero_of_red_ne_zero (C : ComponentChart A F Fb) {u : F} (h : red C u ≠ 0) : u ≠ 0 := by
  rintro rfl; exact h (red_zero C)

end Red

section Eval

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

theorem evalAt_zero' (v : Place K E) : v.evalAt (0 : E) = 0 := by
  simpa using Place.evalAt_algebraMap v (0 : K)

theorem evalAt_add (v : Place K E) (hv : v.IsRational) {f g : E} (hf : f ∈ v.toValuationSubring)
    (hg : g ∈ v.toValuationSubring) : v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_add, v.algebraMap_evalAt hv (add_mem hf hg), v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_add]
  rfl

theorem evalAt_smul (v : Place K E) (hv : v.IsRational) (c : K) {f : E} (hf : f ∈ v.toValuationSubring) :
    v.evalAt (c • f) = c * v.evalAt f := by
  rw [Algebra.smul_def, Place.evalAt_mul v hv (v.algebraMap_mem' c) hf, Place.evalAt_algebraMap]

theorem evalAt_sub (v : Place K E) (hv : v.IsRational) {f g : E} (hf : f ∈ v.toValuationSubring)
    (hg : g ∈ v.toValuationSubring) : v.evalAt (f - g) = v.evalAt f - v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_sub, v.algebraMap_evalAt hv (sub_mem hf hg), v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_sub]
  rfl

theorem evalAt_sum_smul (v : Place K E) (hv : v.IsRational) {k : ℕ} (c : Fin k → K) (b : Fin k → E)
    (hb : ∀ j, b j ∈ v.toValuationSubring) :
    v.evalAt (∑ j, c j • b j) = ∑ j, c j * v.evalAt (b j) := by
  classical
  induction (Finset.univ : Finset (Fin k)) using Finset.induction_on with
  | empty => simpa using Place.evalAt_algebraMap v (0 : K)
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, evalAt_add v hv ?_ ?_, evalAt_smul v hv _ (hb j), ih]
    · rw [Algebra.smul_def]; exact mul_mem (v.algebraMap_mem' _) (hb j)
    · exact Subring.sum_mem _ fun i _ => by rw [Algebra.smul_def]; exact mul_mem (v.algebraMap_mem' _) (hb i)

theorem isUnit_mk_of_ord_eq_zero (v : Place K E) {f : E} (hf : f ≠ 0) (h : v.ord f = 0)
    (hmem : f ∈ v.toValuationSubring) : IsUnit (⟨f, hmem⟩ : v.toValuationSubring) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hϖ
  rw [h, zpow_zero, mul_one] at hu
  have : (⟨f, hmem⟩ : v.toValuationSubring) = (u : v.toValuationSubring) := Subtype.ext hu
  rw [this]; exact u.isUnit

theorem evalAt_eq_zero_iff (v : Place K E) (hv : v.IsRational) {f : E} (hf0 : f ≠ 0)
    (hf : f ∈ v.toValuationSubring) : v.evalAt f = 0 ↔ 1 ≤ v.ord f := by
  have h0 : 0 ≤ v.ord f := (Place.mem_iff_ord_nonneg v hf0).mp hf
  constructor
  · intro h
    by_contra hlt
    have hz : v.ord f = 0 := by omega
    have hu := isUnit_mk_of_ord_eq_zero v hf0 hz hf
    have hres := v.algebraMap_evalAt hv hf
    rw [h, map_zero] at hres
    exact ((residue_ne_zero_iff_isUnit _).mpr hu) hres.symm
  · intro h
    have hres := v.algebraMap_evalAt hv hf
    have hnu : ¬ IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
      intro hu
      have := v.ord_coe_unit hu.unit
      rw [IsUnit.unit_spec] at this
      change v.ord f = 0 at this
      omega
    have hres0 : residue v.toValuationSubring ⟨f, hf⟩ = 0 := by
      rwa [residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rw [hres0, map_eq_zero] at hres
    exact hres

theorem ord_eq_zero_of_evalAt_ne_zero (v : Place K E) (hv : v.IsRational) {f : E} (hf0 : f ≠ 0)
    (hf : f ∈ v.toValuationSubring) (h : v.evalAt f ≠ 0) : v.ord f = 0 := by
  have h0 : 0 ≤ v.ord f := (Place.mem_iff_ord_nonneg v hf0).mp hf
  have h1 : ¬ 1 ≤ v.ord f := fun h1 => h ((evalAt_eq_zero_iff v hv hf0 hf).mpr h1)
  omega

theorem mem_of_ord_nonneg (v : Place K E) {f : E} (h : 0 ≤ v.ord f) : f ∈ v.toValuationSubring := by
  rcases eq_or_ne f 0 with rfl | hf0
  · exact zero_mem _
  · exact (Place.mem_iff_ord_nonneg v hf0).mpr h

end Eval

end K3TwistedLift

namespace K3TwistedLiftRR

section RR

variable {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  [IsCurveOver K F] [Algebra.EssFiniteType K F]

theorem degree_single_eq (v : Place K F) (n : ℤ) :
    Divisor.degree (Finsupp.single v n) = n := by
  rw [Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed v]; simp

theorem degree_eq_sum (D : Divisor K F) : Divisor.degree D = D.sum fun _ n => n := by
  have : Divisor.degree D = D.sum fun Q n => n * (Q.deg : ℤ) := by
    unfold Divisor.degree
    rw [Finsupp.liftAddHom_apply]
    rfl
  rw [this]
  apply Finsupp.sum_congr
  intro Q _
  rw [IsCurveOver.deg_eq_one_of_isAlgClosed Q]
  simp

theorem ord_ge_of_mem_lSpace {D : Divisor K F} {f : F} (hf : f ∈ LSpace D) (hf0 : f ≠ 0)
    (v : Place K F) : -D v ≤ v.ord f := by
  rcases (mem_lSpace_iff_ord.mp hf) with h | h
  · exact absurd h hf0
  · exact h v

theorem mem_toValuationSubring_of_mem_lSpace {D : Divisor K F} {f : F} (hf : f ∈ LSpace D)
    (v : Place K F) (hv : D v ≤ 0) : f ∈ v.toValuationSubring := by
  rcases eq_or_ne f 0 with rfl | hf0
  · exact zero_mem _
  · rw [Place.mem_iff_ord_nonneg v hf0]
    have := ord_ge_of_mem_lSpace hf hf0 v
    omega

theorem ell_eq (D : Divisor K F) (hD : 2 * (genusFF K F : ℤ) - 1 ≤ D.degree) :
    (ell D : ℤ) = D.degree + 1 - (genusFF K F : ℤ) := by
  obtain ⟨t, ht, hfin, hsep⟩ :=
    (IsCurveOver.exists_separating_transcendental (K := K) (F := F))
  exact ell_eq_degree_add_one_sub_genusFF_of_isAlgClosed_of_isSeparable K t ht hfin hsep D hD

theorem infinite_place : Infinite (Place K F) := by
  obtain ⟨t, ht, hfin, -⟩ := (IsCurveOver.exists_separating_transcendental (K := K) (F := F))
  haveI := hfin

  have hpole : ∀ {f : F}, Transcendental K f → ∃ v : Place K F, v.ord f < 0 := by
    intro f hf
    haveI := AlgebraicCurve.finiteDimensional_adjoin_of_transcendental t hf
    classical
    have hf0 : f ≠ 0 := by rintro rfl; exact hf isAlgebraic_zero
    obtain ⟨Df, hDf, -⟩ := (IsCurveOver.hasPrincipalDivisors (K := K) (F := F)).exists_divisor f hf0
    let D : Divisor K F := Finsupp.onFinset Df.support (fun v => max 0 (-v.ord f)) (by
        intro v hv
        rw [Finsupp.mem_support_iff, hDf v]
        intro h0; apply hv; simp [h0])
    have hD : ∀ v, D v = max 0 (-v.ord f) := fun v => by simp [D, Finsupp.onFinset_apply]
    have hdeg := AlgebraicCurve.degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental f hf D hD
    have hpos : 0 < Module.finrank (IntermediateField.adjoin K ({f} : Set F)) F := Module.finrank_pos
    have hne : D ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hdeg
      omega
    obtain ⟨v, hv⟩ := Finsupp.ne_iff.mp hne
    refine ⟨v, ?_⟩
    rw [hD v] at hv
    simp only [Finsupp.coe_zero, Pi.zero_apply, ne_eq] at hv
    by_contra hge
    apply hv
    rw [max_eq_left]
    omega
  have hz : ∀ a : K, ∃ v : Place K F, 0 < v.ord (t - algebraMap K F a) := by
    intro a
    have hta : Transcendental K (t - algebraMap K F a)⁻¹ := by
      intro halg
      apply ht
      have h1 : IsAlgebraic K (t - algebraMap K F a) := by simpa using halg.inv
      simpa using h1.add (isAlgebraic_algebraMap a)
    obtain ⟨v, hv⟩ := hpole hta
    refine ⟨v, ?_⟩
    rw [Place.ord_inv] at hv
    omega
  choose z hz using hz
  refine Infinite.of_injective z ?_
  intro a b hab
  by_contra hne
  have ha := hz a
  have hb := hz b
  rw [← hab] at hb
  have hta0 : t - algebraMap K F a ≠ 0 := by
    intro h; rw [h, Place.ord_zero] at ha; exact lt_irrefl _ ha
  have htb0 : t - algebraMap K F b ≠ 0 := by
    intro h; rw [h, Place.ord_zero] at hb; exact lt_irrefl _ hb
  have hlt : ∀ {f : F}, f ≠ 0 → 0 < (z a).ord f → (z a).adicValuation f < 1 := by
    intro f hf0 h
    rw [(z a).adicValuation_eq_exp_neg_ord hf0, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have h1 := hlt hta0 ha
  have h2 := hlt htb0 hb
  have hab0 : (b - a : K) ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have h3 : (z a).adicValuation (algebraMap K F (b - a)) = 1 := by
    rw [(z a).adicValuation_eq_exp_neg_ord ((map_ne_zero _).mpr hab0), Place.ord_algebraMap, neg_zero,
      WithZero.exp_zero]
  have hid : algebraMap K F (b - a) = (t - algebraMap K F a) - (t - algebraMap K F b) := by
    rw [map_sub]; ring
  rw [hid] at h3
  have h4 := Valuation.map_sub (z a).adicValuation (t - algebraMap K F a) (t - algebraMap K F b)
  rw [h3] at h4
  rcases le_max_iff.mp h4 with h | h
  · exact absurd h1 (not_lt.mpr h)
  · exact absurd h2 (not_lt.mpr h)

theorem finiteDimensional_lSpace' (E : Divisor K F) : FiniteDimensional K (LSpace E) := by
  classical
  haveI := infinite_place (K := K) (F := F)
  obtain ⟨Q₀⟩ : Nonempty (Place K F) := inferInstance

  obtain ⟨k, hk⟩ : ∃ k : ℕ, 2 * (genusFF K F : ℤ) ≤ E.degree + k := by
    refine ⟨(2 * (genusFF K F : ℤ) - E.degree).toNat, ?_⟩
    have := Int.self_le_toNat (2 * (genusFF K F : ℤ) - E.degree)
    omega
  set E' : Divisor K F := E + Finsupp.single Q₀ (k : ℤ) with hE'
  have hdeg : E'.degree = E.degree + k := by rw [hE', map_add, degree_single_eq]
  have hell := ell_eq E' (by rw [hdeg]; omega)
  have hpos : 0 < ell E' := by
    have : (0 : ℤ) < ell E' := by rw [hell, hdeg]; omega
    exact_mod_cast this
  haveI : FiniteDimensional K (LSpace E') := Module.finite_of_finrank_pos hpos
  have hle : LSpace E ≤ LSpace E' := lSpace_mono (by
    intro v
    rw [hE', Finsupp.add_apply, Finsupp.single_apply]
    split_ifs <;> omega)
  exact Submodule.finiteDimensional_of_le hle

theorem degree_add_one_sub_genus_le_ell (E : Divisor K F) :
    E.degree + 1 - (genusFF K F : ℤ) ≤ (ell E : ℤ) := by
  classical
  haveI := infinite_place (K := K) (F := F)
  obtain ⟨Q₀⟩ : Nonempty (Place K F) := inferInstance

  have hstep : ∀ k : ℕ, (ell (E + Finsupp.single Q₀ (k : ℤ)) : ℤ) ≤ ell E + k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h := ell_le_ell_sub_single_add_deg (E + Finsupp.single Q₀ ((k + 1 : ℕ) : ℤ)) Q₀
      rw [IsCurveOver.deg_eq_one_of_isAlgClosed Q₀] at h
      have hsub : E + Finsupp.single Q₀ ((k + 1 : ℕ) : ℤ) - Finsupp.single Q₀ 1 =
          E + Finsupp.single Q₀ (k : ℤ) := by
        rw [add_sub_assoc, ← Finsupp.single_sub]
        congr 2
        push_cast; ring
      rw [hsub] at h
      have h' : (ell (E + Finsupp.single Q₀ ((k + 1 : ℕ) : ℤ)) : ℤ) ≤ ell (E + Finsupp.single Q₀ (k : ℤ)) + 1 := by
        exact_mod_cast h
      push_cast at ih ⊢
      linarith
  obtain ⟨k, hk⟩ : ∃ k : ℕ, 2 * (genusFF K F : ℤ) - 1 ≤ E.degree + k := by
    refine ⟨(2 * (genusFF K F : ℤ) - 1 - E.degree).toNat, ?_⟩
    have := Int.self_le_toNat (2 * (genusFF K F : ℤ) - 1 - E.degree)
    omega
  have hdeg : (E + Finsupp.single Q₀ (k : ℤ)).degree = E.degree + k := by rw [map_add, degree_single_eq]
  have hell := ell_eq (E + Finsupp.single Q₀ (k : ℤ)) (by rw [hdeg]; omega)
  have := hstep k
  rw [hell, hdeg] at this
  linarith

theorem exists_mem_lSpace_forall_evalAt_eq (E : Divisor K F) (Z : Finset (Place K F))
    (hZ : ∀ x ∈ Z, E x = 0) (hrat : ∀ x ∈ Z, x.IsRational)
    (hdeg : 2 * (genusFF K F : ℤ) - 1 + Z.card ≤ E.degree) (val : Place K F → K) :
    ∃ s : F, s ∈ LSpace E ∧ ∀ x ∈ Z, x.evalAt s = val x := by
  classical
  haveI := finiteDimensional_lSpace' (K := K) E

  have hreg : ∀ s ∈ LSpace E, ∀ x ∈ Z, s ∈ x.toValuationSubring := fun s hs x hx =>
    mem_toValuationSubring_of_mem_lSpace hs x (by rw [hZ x hx])
  let ev : LSpace E →ₗ[K] (Z → K) :=
    { toFun := fun s x => (x : Place K F).evalAt (s : F)
      map_add' := fun s s' => by
        funext x
        exact K3TwistedLift.evalAt_add _ (hrat x x.2) (hreg _ s.2 x x.2) (hreg _ s'.2 x x.2)
      map_smul' := fun a s => by
        funext x
        exact K3TwistedLift.evalAt_smul _ (hrat x x.2) a (hreg _ s.2 x x.2) }
  have hev : ∀ (s : LSpace E) (x : Z), ev s x = (x : Place K F).evalAt (s : F) := fun _ _ => rfl

  set EZ : Divisor K F := ∑ x ∈ Z, Finsupp.single x (1 : ℤ) with hEZ
  have hEZ_apply : ∀ v, EZ v = if v ∈ Z then 1 else 0 := by
    intro v
    rw [hEZ, Finsupp.finsetSum_apply]
    split_ifs with hv
    · rw [Finset.sum_eq_single_of_mem v hv]
      · simp
      · intro b _ hb; simp [hb]
    · apply Finset.sum_eq_zero
      intro x hx
      have : x ≠ v := fun h => hv (h ▸ hx)
      simp [this]
  have hker_le : ∀ s : LSpace E, s ∈ LinearMap.ker ev → (s : F) ∈ LSpace (E - EZ) := by
    intro s hs
    rw [LinearMap.mem_ker] at hs
    rcases eq_or_ne (s : F) 0 with h0 | h0
    · rw [h0]; exact Submodule.zero_mem _
    rw [mem_lSpace_iff_ord]
    refine Or.inr fun v => ?_
    have h1 := ord_ge_of_mem_lSpace s.2 h0 v
    rw [Finsupp.sub_apply, hEZ_apply]
    split_ifs with hv
    · have hval : (v : Place K F).evalAt (s : F) = 0 := by
        have := congrFun hs ⟨v, hv⟩
        rw [hev] at this
        exact this
      have := (K3TwistedLift.evalAt_eq_zero_iff v (hrat v hv) h0 (hreg _ s.2 v hv)).mp hval
      rw [hZ v hv]; omega
    · omega
  let j : LinearMap.ker ev →ₗ[K] LSpace (E - EZ) :=
    { toFun := fun s => ⟨(s : LSpace E), hker_le _ s.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro s s' h
    apply Subtype.ext; apply Subtype.ext
    exact congrArg (fun y : LSpace (E - EZ) => (y : F)) h
  haveI := finiteDimensional_lSpace' (K := K) (E - EZ)
  have hker := LinearMap.finrank_le_finrank_of_injective hj

  have hdegEZ : EZ.degree = Z.card := by
    rw [hEZ, map_sum]; simp_rw [degree_single_eq]; simp
  have hE := ell_eq E (by omega)
  have hE' := ell_eq (E - EZ) (by rw [map_sub, hdegEZ]; omega)
  have hrn := LinearMap.finrank_range_add_finrank_ker ev
  have hrange_le : Module.finrank K (LinearMap.range ev) ≤ Z.card := by
    have := Submodule.finrank_le (LinearMap.range ev)
    rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at this
  have hrange : Module.finrank K (LinearMap.range ev) = Module.finrank K (Z → K) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
    have h1 : (Module.finrank K (LSpace E) : ℤ) = ell E := rfl
    have h2 : (Module.finrank K (LSpace (E - EZ)) : ℤ) = ell (E - EZ) := rfl
    have : (Module.finrank K (LinearMap.ker ev) : ℤ) ≤ ell (E - EZ) := by exact_mod_cast hker
    rw [hE', map_sub, hdegEZ] at this
    have hrn' : (Module.finrank K (LinearMap.range ev) : ℤ) + Module.finrank K (LinearMap.ker ev) = ell E := by
      exact_mod_cast hrn
    rw [hE] at hrn'
    have : (Z.card : ℤ) ≤ Module.finrank K (LinearMap.range ev) := by linarith
    have : Z.card ≤ Module.finrank K (LinearMap.range ev) := by exact_mod_cast this
    omega
  have htop : LinearMap.range ev = ⊤ := Submodule.eq_top_of_finrank_eq hrange
  obtain ⟨s, hs⟩ := LinearMap.range_eq_top.mp htop (fun x => val x)
  refine ⟨s, s.2, fun x hx => ?_⟩
  have := congrFun hs ⟨x, hx⟩
  rw [hev] at this
  exact this

end RR

end K3TwistedLiftRR

namespace K3TwistedLiftRR

section Charts

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
variable {Fb : Type*} [Field Fb] [Algebra (ResidueField A) Fb]

theorem mapDomain_apply_eq_sum {α β : Type*} [DecidableEq β] (φ : α → β) (D : α →₀ ℤ) (b : β) :
    Finsupp.mapDomain φ D b = ∑ a ∈ D.support, if φ a = b then D a else 0 := by
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  show (Finsupp.single (φ a) (D a)) b = _
  rw [Finsupp.single_apply]

theorem neg_mapDomain_le_ord_residue [HasPrincipalDivisors L F]
    (C : ComponentChart A F Fb) {f : F} (hf : f ∈ C.integers) (hres : C.residue ⟨f, hf⟩ ≠ 0)
    (D' : Divisor L F) (hD'in : ∀ v ∈ C.dom, -D' v ≤ v.ord f) (hD'out : ∀ v, v ∉ C.dom → D' v = 0)
    (Q : Place (ResidueField A) Fb) (hQ : Q ∉ C.nodes) :
    -(Finsupp.mapDomain C.placeMap D' Q) ≤ Q.ord (C.residue ⟨f, hf⟩) := by
  classical
  have hf0 : f ≠ 0 := by
    rintro rfl
    apply hres
    have : (⟨(0 : F), hf⟩ : C.integers) = 0 := Subtype.ext rfl
    rw [this, map_zero]
  obtain ⟨Df, hDf, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) f hf0
  set Dfi : Divisor L F := Df.filter (· ∈ C.dom) with hDfi
  have hDfi_in : ∀ v ∈ C.dom, Dfi v = v.ord f := fun v hv => by
    rw [hDfi, Finsupp.filter_apply_pos _ _ hv, hDf v]
  have hDfi_out : ∀ v, v ∉ C.dom → Dfi v = 0 := fun v hv => by
    rw [hDfi, Finsupp.filter_apply_neg _ _ hv]
  have hmap := C.mapDomain_placeMap ⟨f, hf⟩ hres Dfi hDfi_in hDfi_out Q hQ
  have hG : 0 ≤ Dfi + D' := by
    intro v
    rw [Finsupp.coe_zero, Pi.zero_apply, Finsupp.add_apply]
    by_cases hv : v ∈ C.dom
    · rw [hDfi_in v hv]; have := hD'in v hv; omega
    · rw [hDfi_out v hv, hD'out v hv]; simp
  have hpos := Finsupp.mapDomain_nonneg (f := C.placeMap) hG
  have := hpos Q
  rw [Finsupp.coe_zero, Pi.zero_apply, Finsupp.mapDomain_add, Finsupp.add_apply, hmap] at this
  omega

end Charts

end K3TwistedLiftRR

namespace K3TwistedLift

section Twist

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]

theorem dom_data (An : Annulus A F) {v : Place L F} (hv : v ∈ An.dom) :
    v.IsRational ∧ An.param ∈ v.toValuationSubring ∧
      (∃ h : v.evalAt An.param ∈ A, (⟨v.evalAt An.param, h⟩ : A) ∈ maximalIdeal A) ∧
      v.evalAt An.param ≠ 0 ∧ ∃ m ∈ maximalIdeal A, (An.modulus : L) = v.evalAt An.param * m :=
  An.mem_dom v hv

theorem param_sub_ne_zero (An : Annulus A F) {w : Place L F} (hw : w ∈ An.dom) :
    An.param - algebraMap L F (w.evalAt An.param) ≠ 0 := by
  intro h
  have := An.ord_param_sub w hw
  rw [h, Place.ord_zero] at this
  exact zero_ne_one this

theorem ord_param_sub_of_ne (An : Annulus A F) {v w : Place L F} (hv : v ∈ An.dom) (hw : w ∈ An.dom)
    (hvw : v ≠ w) : v.ord (An.param - algebraMap L F (w.evalAt An.param)) = 0 := by
  obtain ⟨hvrat, hzv, ⟨hvA, hvmax⟩, hv0, -⟩ := dom_data An hv
  obtain ⟨hwrat, hzw, ⟨hwA, hwmax⟩, hw0, mw, hmw, hμw⟩ := dom_data An hw
  have hmem : An.param - algebraMap L F (w.evalAt An.param) ∈ v.toValuationSubring :=
    sub_mem hzv (v.algebraMap_mem' _)
  refine ord_eq_zero_of_evalAt_ne_zero v hvrat (param_sub_ne_zero An hw) hmem ?_
  intro hval
  rw [evalAt_sub v hvrat hzv (v.algebraMap_mem' _), Place.evalAt_algebraMap, sub_eq_zero] at hval

  obtain ⟨Q, -, huniq⟩ := An.existsUnique_evalAt_eq ⟨w.evalAt An.param, hwA⟩ hwmax hw0 ⟨mw, hmw, hμw⟩
  exact hvw ((huniq v ⟨hv, hval⟩).trans (huniq w ⟨hw, rfl⟩).symm)

theorem twisted_node_law [IsAlgClosed L] [HasPrincipalDivisors L F]
    {Fa : Type*} [Field Fa] [Algebra (ResidueField A) Fa]
    {Fb : Type*} [Field Fb] [Algebra (ResidueField A) Fb]
    (An An' : Annulus A F) (hdom : An'.dom = An.dom) (hmod : An'.modulus = An.modulus)
    (hmod0 : ((An.modulus : A) : L) ≠ 0)
    (hparam : An'.param * An.param = algebraMap L F (An.modulus : L))
    (Ca : ComponentChart A F Fa) (xa : Place (ResidueField A) Fa) (hxa : xa.IsRational)
    (hatta : An.IsAttached Ca xa)
    (Cb : ComponentChart A F Fb) (xb : Place (ResidueField A) Fb) (hxb : xb.IsRational)
    (hattb : An'.IsAttached Cb xb)
    (π : A) (hπ0 : π ≠ 0) (P P' : Place L F) (hP : P ∈ An.dom) (hP' : P' ∈ An.dom) (hPP' : P ≠ P')
    (d : ℕ) (u u' : Aˣ) (h : P.evalAt An.param ∈ A) (h' : P'.evalAt An.param ∈ A)
    (hd : (⟨P.evalAt An.param, h⟩ : A) = u * π ^ d) (hd' : (⟨P'.evalAt An.param, h'⟩ : A) = u' * π ^ d)
    (f : F) (hf0 : f ≠ 0) (hfa : f ∈ Ca.integers) (hfb : f ∈ Cb.integers)
    (hreg : ∀ v ∈ An.dom, v ≠ P → v ≠ P' → 0 ≤ v.ord f) (hregP : -1 ≤ P.ord f) (hregP' : 1 ≤ P'.ord f) :
    (Ca.residue ⟨f, hfa⟩ ≠ 0 → 0 ≤ xa.ord (Ca.residue ⟨f, hfa⟩)) ∧
    (Cb.residue ⟨f, hfb⟩ ≠ 0 → 0 ≤ xb.ord (Cb.residue ⟨f, hfb⟩)) ∧
    xa.evalAt (Ca.residue ⟨f, hfa⟩) =
      IsLocalRing.residue A ((u : A) * ↑u'⁻¹) * xb.evalAt (Cb.residue ⟨f, hfb⟩) := by
  classical

  set z : F := An.param with hz
  set z' : F := An'.param with hz'
  set a : L := P.evalAt z with ha
  set a' : L := P'.evalAt z with ha'
  set q : A := (u : A) * ↑u'⁻¹ with hq
  obtain ⟨hPrat, hzP, ⟨hPA, hPmax⟩, hP0, -⟩ := dom_data An hP
  obtain ⟨hP'rat, hzP', ⟨hP'A, hP'max⟩, hP'0, m', hm', hμ'⟩ := dom_data An hP'

  have hqa : a = (q : L) * a' := by
    have h1 : (⟨a, h⟩ : A) = q * ⟨a', h'⟩ := by
      rw [hd, hd', hq]
      have : (u : A) * ↑u'⁻¹ * (↑u' * π ^ d) = u * (↑u'⁻¹ * ↑u') * π ^ d := by ring
      rw [this, Units.inv_mul, mul_one]
    have := congrArg Subtype.val h1
    simpa using this
  have hq_unit : IsUnit q := (u * u'⁻¹).isUnit
  have hq_res : residue A q ≠ 0 := (residue_ne_zero_iff_isUnit q).mpr hq_unit
  have hres_a' : residue A ⟨a', h'⟩ = 0 := (residue_eq_zero_iff _).mpr hP'max
  have hres_a : residue A ⟨a, h⟩ = 0 := (residue_eq_zero_iff _).mpr hPmax
  have hres_m' : residue A m' = 0 := (residue_eq_zero_iff _).mpr hm'

  set N : F := z - algebraMap L F a with hN
  set Dn : F := z - algebraMap L F a' with hDn
  have hN0 : N ≠ 0 := param_sub_ne_zero An hP
  have hDn0 : Dn ≠ 0 := param_sub_ne_zero An hP'
  set r : F := N * Dn⁻¹ with hr
  set f₁ : F := f * r with hf₁
  have hr0 : r ≠ 0 := mul_ne_zero hN0 (inv_ne_zero hDn0)
  have hf₁0 : f₁ ≠ 0 := mul_ne_zero hf0 hr0

  have hordN : ∀ v ∈ An.dom, v.ord N = if v = P then 1 else 0 := by
    intro v hv
    split_ifs with hvP
    · subst hvP; exact An.ord_param_sub _ hP
    · exact ord_param_sub_of_ne An hv hP hvP
  have hordDn : ∀ v ∈ An.dom, v.ord Dn = if v = P' then 1 else 0 := by
    intro v hv
    split_ifs with hvP
    · subst hvP; exact An.ord_param_sub _ hP'
    · exact ord_param_sub_of_ne An hv hP' hvP
  have hreg₁ : ∀ v ∈ An.dom, 0 ≤ v.ord f₁ := by
    intro v hv
    rw [hf₁, hr, Place.ord_mul _ hf0 hr0, Place.ord_mul _ hN0 (inv_ne_zero hDn0), Place.ord_inv,
      hordN v hv, hordDn v hv]
    by_cases hvP : v = P
    · subst hvP
      rw [if_pos rfl, if_neg hPP']
      omega
    · by_cases hvP' : v = P'
      · subst hvP'
        rw [if_neg hvP, if_pos rfl]
        omega
      · rw [if_neg hvP, if_neg hvP']
        have := hreg v hv hvP hvP'
        omega

  have hatta' := hatta
  obtain ⟨-, hza, hza1, -⟩ := hatta'
  have hredz : red Ca z ≠ 0 := by
    rw [red_of_mem Ca hza]
    intro h0
    rw [h0, Place.ord_zero] at hza1
    exact zero_ne_one hza1
  have haA : algebraMap L F a ∈ Ca.integers := algebraMap_mem Ca ⟨a, h⟩
  have ha'A : algebraMap L F a' ∈ Ca.integers := algebraMap_mem Ca ⟨a', h'⟩
  have hNa : N ∈ Ca.integers := sub_mem hza haA
  have hDna : Dn ∈ Ca.integers := sub_mem hza ha'A
  have hredNa : red Ca N = red Ca z := by
    rw [hN, red_sub Ca hza haA]
    have : red Ca (algebraMap L F a) = 0 := by
      have := red_algebraMap Ca ⟨a, h⟩
      rw [hres_a, map_zero] at this
      exact this
    rw [this, sub_zero]
  have hredDna : red Ca Dn = red Ca z := by
    rw [hDn, red_sub Ca hza ha'A]
    have : red Ca (algebraMap L F a') = 0 := by
      have := red_algebraMap Ca ⟨a', h'⟩
      rw [hres_a', map_zero] at this
      exact this
    rw [this, sub_zero]
  have hDna_inv : Dn⁻¹ ∈ Ca.integers := inv_mem_of_red_ne_zero Ca hDna (by rw [hredDna]; exact hredz)
  have hra : r ∈ Ca.integers := mul_mem hNa hDna_inv
  have hredra : red Ca r = 1 := by
    rw [hr, red_mul Ca hNa hDna_inv, red_inv Ca hDna (by rw [hredDna]; exact hredz), hredNa, hredDna,
      mul_inv_cancel₀ hredz]
  have hf₁a : f₁ ∈ Ca.integers := mul_mem hfa hra
  have hredf₁a : red Ca f₁ = red Ca f := by
    rw [hf₁, red_mul Ca hfa hra, hredra, mul_one]

  have hattb' := hattb
  obtain ⟨-, hz'b, hz'b1, -⟩ := hattb'
  have hredz' : red Cb z' ≠ 0 := by
    rw [red_of_mem Cb hz'b]
    intro h0
    rw [h0, Place.ord_zero] at hz'b1
    exact zero_ne_one hz'b1
  have hz'0 : z' ≠ 0 := ne_zero_of_red_ne_zero Cb hredz'
  have hz'inv : z'⁻¹ ∈ Cb.integers := inv_mem_of_red_ne_zero Cb hz'b hredz'

  have hzeq : z = algebraMap L F a' * algebraMap L F (m' : L) * z'⁻¹ := by
    have h1 : z' * z = algebraMap L F a' * algebraMap L F (m' : L) := by
      rw [hparam, ← map_mul]
      exact (congrArg (algebraMap L F) hμ' : _)
    calc z = z'⁻¹ * (z' * z) := by rw [← mul_assoc, inv_mul_cancel₀ hz'0, one_mul]
      _ = algebraMap L F a' * algebraMap L F (m' : L) * z'⁻¹ := by rw [h1]; ring
  set t : F := algebraMap L F (m' : L) * z'⁻¹ with ht
  have htb : t ∈ Cb.integers := mul_mem (algebraMap_mem Cb m') hz'inv
  have hredt : red Cb t = 0 := by
    rw [ht, red_mul Cb (algebraMap_mem Cb m') hz'inv, red_algebraMap Cb m', hres_m', map_zero, zero_mul]
  have ha'0 : algebraMap L F a' ≠ 0 := (map_ne_zero _).mpr hP'0

  have hNeq : N = algebraMap L F a' * (t - algebraMap L F (q : L)) := by
    rw [hN, hzeq, hqa, map_mul, ht]; ring
  have hDneq : Dn = algebraMap L F a' * (t - 1) := by
    rw [hDn, hzeq, ht]; ring
  have hqb : algebraMap L F (q : L) ∈ Cb.integers := algebraMap_mem Cb q
  have hNb' : t - algebraMap L F (q : L) ∈ Cb.integers := sub_mem htb hqb
  have hDnb' : t - 1 ∈ Cb.integers := sub_mem htb (one_mem _)
  have hred_tq : red Cb (t - algebraMap L F (q : L)) = -algebraMap (ResidueField A) Fb (residue A q) := by
    rw [red_sub Cb htb hqb, hredt, red_algebraMap Cb q, zero_sub]
  have hred_t1 : red Cb (t - 1) = -1 := by
    rw [red_sub Cb htb (one_mem _), hredt, red_one, zero_sub]
  have hred_t1_ne : red Cb (t - 1) ≠ 0 := by rw [hred_t1]; exact neg_ne_zero.mpr one_ne_zero
  have ht1_inv : (t - 1)⁻¹ ∈ Cb.integers := inv_mem_of_red_ne_zero Cb hDnb' hred_t1_ne
  have hreq : r = (t - algebraMap L F (q : L)) * (t - 1)⁻¹ := by
    rw [hr, hNeq, hDneq, mul_inv]
    field_simp
  have hrb : r ∈ Cb.integers := by rw [hreq]; exact mul_mem hNb' ht1_inv
  have hredrb : red Cb r = algebraMap (ResidueField A) Fb (residue A q) := by
    rw [hreq, red_mul Cb hNb' ht1_inv, red_inv Cb hDnb' hred_t1_ne, hred_tq, hred_t1]
    field_simp
  have hf₁b : f₁ ∈ Cb.integers := mul_mem hfb hrb
  have hredf₁b : red Cb f₁ = red Cb f * algebraMap (ResidueField A) Fb (residue A q) := by
    rw [hf₁, red_mul Cb hfb hrb, hredrb]

  have hdom' : ∀ v ∈ An.dom, 0 ≤ v.ord f₁ := hreg₁
  obtain ⟨h1, h2, h3⟩ :=
    Annulus.ord_residue_nonneg_and_evalAt_residue_eq_of_isAttached_of_isAttached A An An' hdom hmod hmod0
      hparam Ca xa hxa hatta Cb xb hxb hattb f₁ hf₁a hf₁b hdom'

  have e1 : Ca.residue ⟨f₁, hf₁a⟩ = Ca.residue ⟨f, hfa⟩ := by
    rw [← red_of_mem, ← red_of_mem, hredf₁a]
  have e2 : Cb.residue ⟨f₁, hf₁b⟩ =
      Cb.residue ⟨f, hfb⟩ * algebraMap (ResidueField A) Fb (residue A q) := by
    rw [← red_of_mem, ← red_of_mem, hredf₁b]
  have hqb0 : algebraMap (ResidueField A) Fb (residue A q) ≠ 0 := (map_ne_zero _).mpr hq_res
  rw [e1] at h1 h3
  rw [e2] at h2 h3
  refine ⟨h1, fun hne => ?_, ?_⟩
  · have := h2 (mul_ne_zero hne hqb0)
    rwa [Place.ord_mul _ hne hqb0, Place.ord_algebraMap, add_zero] at this
  · rw [h3]
    by_cases hne : Cb.residue ⟨f, hfb⟩ = 0
    · rw [hne, zero_mul, evalAt_zero', mul_zero]
    · have hreg2 : Cb.residue ⟨f, hfb⟩ ∈ xb.toValuationSubring := by
        apply mem_of_ord_nonneg
        have := h2 (mul_ne_zero hne hqb0)
        rwa [Place.ord_mul _ hne hqb0, Place.ord_algebraMap, add_zero] at this
      rw [Place.evalAt_mul xb hxb hreg2 (xb.algebraMap_mem' _), Place.evalAt_algebraMap, mul_comm]

end Twist

end K3TwistedLift

set_option maxHeartbeats 1600000 in
open K3TwistedLift K3TwistedLiftRR in
open Classical in
theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (F : Type*) [Field F] [Algebra L F]
    (n m : ℕ) (Fbar : Fin n → Type*) [∀ i, Field (Fbar i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    (hratBar : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q.IsRational)
    (C : ∀ i, ComponentChart A F (Fbar i))
    (hratF : ∀ i, ∀ P ∈ (C i).dom, P.IsRational)
    (An An' : Fin m → Annulus A F) (src tgt : Fin m → Fin n)
    (xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e)))
    (xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e)))
    (w : Fin m → ℕ)
    (hpair : ∀ e, (An' e).dom = (An e).dom ∧ (An' e).modulus = (An e).modulus ∧
      ((An e).modulus : L) ≠ 0 ∧
      (An' e).param * (An e).param = algebraMap L F ((An e).modulus : L))
    (hw : ∀ e, ∃ u : Aˣ, (An e).modulus = u * π ^ w e)
    (hatt : ∀ e, (An e).IsAttached (C (src e)) (xs e) ∧ (An' e).IsAttached (C (tgt e)) (xt e))
    (hnodes : (∀ i, ∀ x ∈ (C i).nodes, ∃ e,
        (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩ ∨
        (⟨tgt e, xt e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∀ E E' : Fin m ⊕ Fin m,
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E = ⟨i, x⟩ →
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E' = ⟨i, x⟩ → E = E'))
    (hcover : ∀ P : Place L F,
      (∃ i, P ∈ (C i).dom ∧ (∀ j, P ∈ (C j).dom → j = i) ∧ ∀ e, P ∉ (An e).dom) ∨
      (∃ e, P ∈ (An e).dom ∧ (∀ e', P ∈ (An e').dom → e' = e) ∧ ∀ i, P ∉ (C i).dom))
    (hdisc : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q ∉ (C i).nodes →
      ∃ (T : F) (hT : T ∈ (C i).integers), (C i).residue ⟨T, hT⟩ ≠ 0 ∧ Q.ord ((C i).residue ⟨T, hT⟩) = 1 ∧
        (∀ P ∈ (C i).dom, (C i).placeMap P = Q → T ∈ P.toValuationSubring ∧
          ∃ h : P.evalAt T ∈ A, (⟨P.evalAt T, h⟩ : A) ∈ IsLocalRing.maximalIdeal A) ∧
        ∀ c : A, c ∈ IsLocalRing.maximalIdeal A →
          ∃! P : Place L F, P ∈ (C i).dom ∧ (C i).placeMap P = Q ∧ P.evalAt T = c)
    (hgenus : genusFF L F + n = (∑ i, genusFF (IsLocalRing.ResidueField A) (Fbar i)) + m + 1)
    [IsCurveOver L F] [Algebra.EssFiniteType L F]
    [∀ i, IsCurveOver (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, Algebra.EssFiniteType (IsLocalRing.ResidueField A) (Fbar i)]
    (E : Fin n → Divisor L F) (hE : ∀ i, ∀ Q ∈ (E i).support, Q ∈ (C i).dom) (hE0 : ∀ i, 0 ≤ E i)
    (hdegE : ∀ i, 2 * (genusFF (IsLocalRing.ResidueField A) (Fbar i) : ℤ) - 1 + ((C i).nodes.card : ℤ) ≤
      Divisor.degree (Finsupp.mapDomain (C i).placeMap (E i) : Divisor (IsLocalRing.ResidueField A) (Fbar i)))
    (e₀ : Fin m) (P P' : Place L F) (hP : P ∈ (An e₀).dom) (hP' : P' ∈ (An e₀).dom) (hPP' : P ≠ P')
    (d : ℕ) (u u' : Aˣ) (h : P.evalAt (An e₀).param ∈ A) (h' : P'.evalAt (An e₀).param ∈ A)
    (hd : (⟨P.evalAt (An e₀).param, h⟩ : A) = u * π ^ d) (hd' : (⟨P'.evalAt (An e₀).param, h'⟩ : A) = u' * π ^ d)
    (sbar : ∀ i, Fbar i)
    (hsRR : ∀ i, sbar i ∈ riemannRochSpace (Finsupp.mapDomain (C i).placeMap (E i)))
    (hsnode : ∀ i, ∀ x ∈ (C i).nodes, (sbar i) ∈ x.toValuationSubring ∧ x.ord (sbar i) = 0)

    (hglue : ∀ e, e ≠ e₀ → (xs e).evalAt (sbar (src e)) = (xt e).evalAt (sbar (tgt e)))
    (hglue₀ : (xs e₀).evalAt (sbar (src e₀)) =
      IsLocalRing.residue A ((u : A) * ↑u'⁻¹) * (xt e₀).evalAt (sbar (tgt e₀)))
    :
    ∃ g : F, g ≠ 0 ∧ g ∈ riemannRochSpace ((∑ i, E i) + Finsupp.single P 1 - Finsupp.single P' 1) ∧
      ∀ i, ∃ hg : g ∈ (C i).integers, (C i).residue ⟨g, hg⟩ = sbar i := by
  classical
  haveI hκ : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A

  set D : Divisor L F := (∑ i, E i) + Finsupp.single P 1 - Finsupp.single P' 1 with hDdef
  set Ebar : ∀ i, Divisor (ResidueField A) (Fbar i) := fun i => Finsupp.mapDomain (C i).placeMap (E i)
    with hEbar
  have hEbar_i : ∀ i, Ebar i = Finsupp.mapDomain (C i).placeMap (E i) := fun i => rfl
  have hdegE' : ∀ i, 2 * (genusFF (IsLocalRing.ResidueField A) (Fbar i) : ℤ) - 1 + ((C i).nodes.card : ℤ) ≤
      (Ebar i).degree := fun i => hdegE i

  set c : Fin m → ResidueField A := fun e => if e = e₀ then IsLocalRing.residue A ((u : A) * ↑u'⁻¹) else 1
    with hcdef
  have hc₀ : c e₀ = IsLocalRing.residue A ((u : A) * ↑u'⁻¹) := by rw [hcdef]; exact if_pos rfl
  have hc_ne : ∀ e, e ≠ e₀ → c e = 1 := fun e he => by rw [hcdef]; exact if_neg he

  have dom_unique : ∀ {v : Place L F} {i j : Fin n}, v ∈ (C i).dom → v ∈ (C j).dom → j = i := by
    intro v i j hi hj
    rcases hcover v with ⟨k, -, huniq, -⟩ | ⟨e, -, -, hnot⟩
    · rw [huniq i hi, huniq j hj]
    · exact absurd hi (hnot i)
  have ann_not_dom : ∀ {v : Place L F} (e : Fin m), v ∈ (An e).dom → ∀ i, v ∉ (C i).dom := by
    intro v e he i hi
    rcases hcover v with ⟨k, -, -, hno⟩ | ⟨e', -, -, hnot⟩
    · exact hno e he
    · exact hnot i hi
  have ann_unique : ∀ {v : Place L F} {e e' : Fin m}, v ∈ (An e).dom → v ∈ (An e').dom → e' = e := by
    intro v e e' he he'
    rcases hcover v with ⟨k, -, -, hno⟩ | ⟨e'', -, huniq, -⟩
    · exact absurd he (hno e)
    · rw [huniq e he, huniq e' he']
  have hE_out : ∀ i v, v ∉ (C i).dom → E i v = 0 := by
    intro i v hv
    by_contra hne
    exact hv (hE i v (Finsupp.mem_support_iff.mpr hne))

  have hD_apply : ∀ v, D v = (∑ i, E i v) + (Finsupp.single P (1 : ℤ)) v - (Finsupp.single P' (1 : ℤ)) v := by
    intro v
    rw [hDdef, Finsupp.sub_apply, Finsupp.add_apply, Finsupp.finsetSum_apply]
  have hD_dom : ∀ i, ∀ v ∈ (C i).dom, D v = E i v := by
    intro i v hv
    rw [hD_apply, Finset.sum_eq_single i, Finsupp.single_apply, Finsupp.single_apply, if_neg, if_neg]
    · ring
    · intro hP'v; subst hP'v; exact ann_not_dom e₀ hP' i hv
    · intro hPv; subst hPv; exact ann_not_dom e₀ hP i hv
    · intro j _ hji
      exact hE_out j v (fun hvj => hji (dom_unique hv hvj))
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have hD_ann : ∀ e, ∀ v ∈ (An e).dom, D v = (if v = P then 1 else 0) - (if v = P' then 1 else 0) := by
    intro e v hv
    rw [hD_apply, Finset.sum_eq_zero (fun i _ => hE_out i v (ann_not_dom e hv i)), zero_add,
      Finsupp.single_apply, Finsupp.single_apply]
    by_cases hvP : v = P
    · have h1 : ¬ P' = v := fun hh => hPP' (hh.trans hvP).symm
      rw [if_pos hvP.symm, if_neg h1, if_pos hvP, if_neg (fun hh => h1 hh.symm)]
    · by_cases hvP' : v = P'
      · rw [if_neg (fun hh => hvP hh.symm), if_pos hvP'.symm, if_neg hvP, if_pos hvP']
      · rw [if_neg (fun hh => hvP hh.symm), if_neg (fun hh => hvP' hh.symm), if_neg hvP, if_neg hvP']
  have hEbar_node : ∀ i, ∀ x ∈ (C i).nodes, Ebar i x = 0 := by
    intro i x hx
    rw [hEbar_i, mapDomain_apply_eq_sum]
    apply Finset.sum_eq_zero
    intro v hv
    split_ifs with hh
    · exfalso
      exact (C i).placeMap_not_mem_nodes v (hE i v hv) (hh ▸ hx)
    · rfl
  have hres_zero : ∀ i (h0 : (0 : F) ∈ (C i).integers), (C i).residue ⟨0, h0⟩ = 0 := by
    intro i h0
    have : (⟨(0 : F), h0⟩ : (C i).integers) = 0 := Subtype.ext rfl
    rw [this, map_zero]

  have nec : ∀ (f : F) (hf : ∀ i, f ∈ (C i).integers), f ∈ riemannRochSpace D →
      (∀ i, (C i).residue ⟨f, hf i⟩ ∈ riemannRochSpace (Ebar i)) ∧
      ∀ e, (xs e).evalAt ((C (src e)).residue ⟨f, hf (src e)⟩) =
        c e * (xt e).evalAt ((C (tgt e)).residue ⟨f, hf (tgt e)⟩) := by
    intro f hf hfD
    rcases eq_or_ne f 0 with hf0 | hf0
    · subst hf0
      refine ⟨fun i => ?_, fun e => ?_⟩
      · rw [hres_zero]; exact Submodule.zero_mem _
      · rw [hres_zero, hres_zero, evalAt_zero', evalAt_zero', mul_zero]
    have hordD : ∀ v, -D v ≤ v.ord f := ord_ge_of_mem_lSpace hfD hf0

    have node_law : ∀ e,
        ((C (src e)).residue ⟨f, hf (src e)⟩ ≠ 0 → 0 ≤ (xs e).ord ((C (src e)).residue ⟨f, hf (src e)⟩)) ∧
        ((C (tgt e)).residue ⟨f, hf (tgt e)⟩ ≠ 0 → 0 ≤ (xt e).ord ((C (tgt e)).residue ⟨f, hf (tgt e)⟩)) ∧
        (xs e).evalAt ((C (src e)).residue ⟨f, hf (src e)⟩) =
          c e * (xt e).evalAt ((C (tgt e)).residue ⟨f, hf (tgt e)⟩) := by
      intro e
      by_cases he : e = e₀
      · subst he
        rw [hc₀]
        refine twisted_node_law (An e) (An' e) (hpair e).1 (hpair e).2.1 (hpair e).2.2.1 (hpair e).2.2.2
          (C (src e)) (xs e) (hratBar _ _) (hatt e).1 (C (tgt e)) (xt e) (hratBar _ _) (hatt e).2
          π hπ0 P P' hP hP' hPP' d u u' h h' hd hd' f hf0 (hf _) (hf _) ?_ ?_ ?_
        · intro v hv hvP hvP'
          have := hordD v
          rw [hD_ann e v hv, if_neg hvP, if_neg hvP'] at this
          simpa using this
        · have := hordD P
          rw [hD_ann e P hP, if_pos rfl, if_neg hPP'] at this
          simpa using this
        · have := hordD P'
          rw [hD_ann e P' hP', if_neg (Ne.symm hPP'), if_pos rfl] at this
          simpa using this
      · rw [hc_ne e he, one_mul]
        refine Annulus.ord_residue_nonneg_and_evalAt_residue_eq_of_isAttached_of_isAttached A (An e) (An' e)
          (hpair e).1 (hpair e).2.1 (hpair e).2.2.1 (hpair e).2.2.2 (C (src e)) (xs e) (hratBar _ _) (hatt e).1
          (C (tgt e)) (xt e) (hratBar _ _) (hatt e).2 f (hf _) (hf _) (fun v hv => ?_)
        have := hordD v
        have hvP : v ≠ P := fun hvP => he (ann_unique hP (hvP ▸ hv))
        have hvP' : v ≠ P' := fun hvP' => he (ann_unique hP' (hvP' ▸ hv))
        rw [hD_ann e v hv, if_neg hvP, if_neg hvP'] at this
        simpa using this
    refine ⟨fun i => ?_, fun e => (node_law e).2.2⟩
    by_cases hres : (C i).residue ⟨f, hf i⟩ = 0
    · rw [hres]; exact Submodule.zero_mem _
    show (C i).residue ⟨f, hf i⟩ ∈ LSpace (Ebar i)
    rw [mem_lSpace_iff_ord]
    refine Or.inr fun Q => ?_
    by_cases hQ : Q ∈ (C i).nodes
    · rw [hEbar_node i Q hQ, neg_zero]
      obtain ⟨e, he | he⟩ := hnodes.1 i Q hQ
      · obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp he
        subst h1
        have h3 := eq_of_heq h2
        subst h3
        exact (node_law e).1 hres
      · obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp he
        subst h1
        have h3 := eq_of_heq h2
        subst h3
        exact (node_law e).2.1 hres
    · rw [hEbar_i]
      refine neg_mapDomain_le_ord_residue (C i) (hf i) hres _ (fun v hv => ?_) (hE_out i) Q hQ
      rw [← hD_dom i v hv]; exact hordD v

  have hn : 0 < n := Fin.pos (src e₀)
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hreg_node : ∀ i (t : Fbar i), t ∈ LSpace (Ebar i) → ∀ x ∈ (C i).nodes, t ∈ x.toValuationSubring := by
    intro i t ht x hx
    exact mem_toValuationSubring_of_mem_lSpace ht x (by rw [hEbar_node i x hx])
  let G : Submodule (ResidueField A) (∀ i, Fbar i) :=
    { carrier := {t | (∀ i, t i ∈ LSpace (Ebar i)) ∧
        ∀ e, (xs e).evalAt (t (src e)) = c e * (xt e).evalAt (t (tgt e))}
      add_mem' := by
        rintro t t' ⟨ht, hte⟩ ⟨ht', hte'⟩
        refine ⟨fun i => Submodule.add_mem _ (ht i) (ht' i), fun e => ?_⟩
        rw [Pi.add_apply, Pi.add_apply,
          evalAt_add _ (hratBar _ _) (hreg_node _ _ (ht _) _ (hatt e).1.1) (hreg_node _ _ (ht' _) _ (hatt e).1.1),
          evalAt_add _ (hratBar _ _) (hreg_node _ _ (ht _) _ (hatt e).2.1) (hreg_node _ _ (ht' _) _ (hatt e).2.1),
          hte e, hte' e]
        ring
      zero_mem' := by
        refine ⟨fun i => Submodule.zero_mem _, fun e => ?_⟩
        rw [Pi.zero_apply, Pi.zero_apply, evalAt_zero', evalAt_zero', mul_zero]
      smul_mem' := by
        rintro a t ⟨ht, hte⟩
        refine ⟨fun i => Submodule.smul_mem _ a (ht i), fun e => ?_⟩
        rw [Pi.smul_apply, Pi.smul_apply,
          evalAt_smul _ (hratBar _ _) a (hreg_node _ _ (ht _) _ (hatt e).1.1),
          evalAt_smul _ (hratBar _ _) a (hreg_node _ _ (ht _) _ (hatt e).2.1), hte e]
        ring }
  have hG_mem : ∀ t : ∀ i, Fbar i, t ∈ G ↔ (∀ i, t i ∈ LSpace (Ebar i)) ∧
      ∀ e, (xs e).evalAt (t (src e)) = c e * (xt e).evalAt (t (tgt e)) := fun t => Iff.rfl

  have hsG : sbar ∈ G := by
    refine (hG_mem _).mpr ⟨hsRR, fun e => ?_⟩
    by_cases he : e = e₀
    · subst he; rw [hc₀]; exact hglue₀
    · rw [hc_ne e he, one_mul]; exact hglue e he

  haveI hΛfin : ∀ i, FiniteDimensional (ResidueField A) (LSpace (Ebar i)) := fun i =>
    finiteDimensional_lSpace' (K := ResidueField A) (Ebar i)
  let δ : (∀ i, LSpace (Ebar i)) →ₗ[ResidueField A] (Fin m → ResidueField A) :=
    { toFun := fun s e => (xs e).evalAt ((s (src e) : Fbar (src e))) - c e * (xt e).evalAt ((s (tgt e) : Fbar (tgt e)))
      map_add' := fun s s' => by
        funext e
        simp only [Pi.add_apply, Submodule.coe_add]
        rw [evalAt_add _ (hratBar _ _) (hreg_node _ _ (s (src e)).2 _ (hatt e).1.1)
            (hreg_node _ _ (s' (src e)).2 _ (hatt e).1.1),
          evalAt_add _ (hratBar _ _) (hreg_node _ _ (s (tgt e)).2 _ (hatt e).2.1)
            (hreg_node _ _ (s' (tgt e)).2 _ (hatt e).2.1)]
        ring
      map_smul' := fun a s => by
        funext e
        simp only [Pi.smul_apply, Submodule.coe_smul, RingHom.id_apply, smul_eq_mul]
        rw [evalAt_smul _ (hratBar _ _) a (hreg_node _ _ (s (src e)).2 _ (hatt e).1.1),
          evalAt_smul _ (hratBar _ _) a (hreg_node _ _ (s (tgt e)).2 _ (hatt e).2.1)]
        ring }
  have hδ_apply : ∀ s e, δ s e =
      (xs e).evalAt ((s (src e) : Fbar (src e))) - c e * (xt e).evalAt ((s (tgt e) : Fbar (tgt e))) :=
    fun _ _ => rfl

  let φ : G →ₗ[ResidueField A] LinearMap.ker δ :=
    { toFun := fun t => ⟨fun i => ⟨(t : ∀ i, Fbar i) i, ((hG_mem _).mp t.2).1 i⟩, by
        rw [LinearMap.mem_ker]
        funext e
        rw [hδ_apply]
        simp only [Pi.zero_apply]
        rw [((hG_mem _).mp t.2).2 e, sub_self]⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hφ : Function.Injective φ := by
    intro t t' htt
    apply Subtype.ext
    funext i
    have := congrArg (fun y : LinearMap.ker δ => ((y : ∀ i, LSpace (Ebar i)) i : Fbar i)) htt
    exact this
  haveI hGfin : FiniteDimensional (ResidueField A) G := Module.Finite.of_injective φ hφ
  have hG_le_ker : Module.finrank (ResidueField A) G ≤ Module.finrank (ResidueField A) (LinearMap.ker δ) :=
    LinearMap.finrank_le_finrank_of_injective hφ

  have hval : ∀ (τs : Fin m → ResidueField A) (τt : Fin m → ResidueField A),
      ∃ s : ∀ i, LSpace (Ebar i), ∀ e,
        (xs e).evalAt ((s (src e) : Fbar (src e))) = τs e ∧ (xt e).evalAt ((s (tgt e) : Fbar (tgt e))) = τt e := by
    intro τs τt
    let val : ∀ i, Place (ResidueField A) (Fbar i) → ResidueField A := fun i x =>
      (∑ e ∈ Finset.univ.filter
        (fun e => (⟨src e, xs e⟩ : Σ j, Place (ResidueField A) (Fbar j)) = ⟨i, x⟩), τs e) +
      ∑ e ∈ Finset.univ.filter
        (fun e => (⟨tgt e, xt e⟩ : Σ j, Place (ResidueField A) (Fbar j)) = ⟨i, x⟩), τt e
    have hval_src : ∀ e, val (src e) (xs e) = τs e := by
      intro e
      show (∑ e' ∈ Finset.univ.filter (fun e' =>
        (⟨src e', xs e'⟩ : Σ j, Place (ResidueField A) (Fbar j)) = ⟨src e, xs e⟩), τs e') +
        ∑ e' ∈ Finset.univ.filter (fun e' =>
        (⟨tgt e', xt e'⟩ : Σ j, Place (ResidueField A) (Fbar j)) = ⟨src e, xs e⟩), τt e' = τs e
      rw [Finset.sum_eq_single_of_mem e (by simp), Finset.sum_eq_zero, add_zero]
      · intro e' he'
        exfalso
        rw [Finset.mem_filter] at he'
        have := hnodes.2 (src e) (xs e) (hatt e).1.1 (Sum.inr e') (Sum.inl e) he'.2 rfl
        exact Sum.inr_ne_inl this
      · intro e' he' hne
        exfalso
        rw [Finset.mem_filter] at he'
        have := hnodes.2 (src e) (xs e) (hatt e).1.1 (Sum.inl e') (Sum.inl e) he'.2 rfl
        exact hne (Sum.inl_injective this)
    have hval_tgt : ∀ e, val (tgt e) (xt e) = τt e := by
      intro e
      show (∑ e' ∈ Finset.univ.filter (fun e' =>
        (⟨src e', xs e'⟩ : Σ j, Place (ResidueField A) (Fbar j)) = ⟨tgt e, xt e⟩), τs e') +
        ∑ e' ∈ Finset.univ.filter (fun e' =>
        (⟨tgt e', xt e'⟩ : Σ j, Place (ResidueField A) (Fbar j)) = ⟨tgt e, xt e⟩), τt e' = τt e
      rw [Finset.sum_eq_zero, zero_add, Finset.sum_eq_single_of_mem e (by simp)]
      · intro e' he' hne
        exfalso
        rw [Finset.mem_filter] at he'
        have := hnodes.2 (tgt e) (xt e) (hatt e).2.1 (Sum.inr e') (Sum.inr e) he'.2 rfl
        exact hne (Sum.inr_injective this)
      · intro e' he'
        exfalso
        rw [Finset.mem_filter] at he'
        have := hnodes.2 (tgt e) (xt e) (hatt e).2.1 (Sum.inl e') (Sum.inr e) he'.2 rfl
        exact Sum.inl_ne_inr this
    have hs : ∀ i, ∃ s : Fbar i, s ∈ LSpace (Ebar i) ∧ ∀ x ∈ (C i).nodes, x.evalAt s = val i x := by
      intro i
      exact exists_mem_lSpace_forall_evalAt_eq (Ebar i) (C i).nodes (hEbar_node i)
        (fun x _ => hratBar i x) (hdegE' i) (val i)
    choose s hsD hsval using hs
    refine ⟨fun i => ⟨s i, hsD i⟩, fun e => ⟨?_, ?_⟩⟩
    · show (xs e).evalAt (s (src e)) = τs e
      rw [hsval _ _ (hatt e).1.1, hval_src]
    · show (xt e).evalAt (s (tgt e)) = τt e
      rw [hsval _ _ (hatt e).2.1, hval_tgt]

  have hδ_surj : LinearMap.range δ = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro t
    obtain ⟨s, hs⟩ := hval t (fun _ => 0)
    refine ⟨s, ?_⟩
    funext e
    rw [hδ_apply, (hs e).1, (hs e).2, mul_zero, sub_zero]

  let δ' : (∀ i, LSpace (Ebar i)) →ₗ[ResidueField A] ((Fin m → ResidueField A) × ResidueField A) :=
    LinearMap.prod δ
      { toFun := fun s => (xt e₀).evalAt ((s (tgt e₀) : Fbar (tgt e₀)))
        map_add' := fun s s' => by
          simp only [Pi.add_apply, Submodule.coe_add]
          rw [evalAt_add _ (hratBar _ _) (hreg_node _ _ (s (tgt e₀)).2 _ (hatt e₀).2.1)
            (hreg_node _ _ (s' (tgt e₀)).2 _ (hatt e₀).2.1)]
        map_smul' := fun a s => by
          simp only [Pi.smul_apply, Submodule.coe_smul, RingHom.id_apply, smul_eq_mul]
          rw [evalAt_smul _ (hratBar _ _) a (hreg_node _ _ (s (tgt e₀)).2 _ (hatt e₀).2.1)] }
  have hδ'_surj : Function.Surjective δ' := by
    rintro ⟨t, τ⟩
    obtain ⟨s, hs⟩ := hval (fun e => t e + c e * (if e = e₀ then τ else 0)) (fun e => if e = e₀ then τ else 0)
    refine ⟨s, Prod.ext ?_ ?_⟩
    · funext e
      show δ s e = t e
      rw [hδ_apply, (hs e).1, (hs e).2]
      ring
    · show (xt e₀).evalAt ((s (tgt e₀) : Fbar (tgt e₀))) = τ
      rw [(hs e₀).2, if_pos rfl]
  have hsum_ge : m + 1 ≤ ∑ i, Module.finrank (ResidueField A) (LSpace (Ebar i)) := by
    have := LinearMap.finrank_range_le δ'
    rw [LinearMap.range_eq_top.mpr hδ'_surj, finrank_top, Module.finrank_prod,
      Module.finrank_fintype_fun_eq_card, Fintype.card_fin, Module.finrank_self,
      Module.finrank_pi_fintype] at this
    exact this
  have hker : (Module.finrank (ResidueField A) (LinearMap.ker δ) : ℤ) =
      (∑ i, (ell (Ebar i) : ℤ)) - m := by
    have h1 := LinearMap.finrank_range_add_finrank_ker δ
    rw [hδ_surj, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
      Module.finrank_pi_fintype] at h1
    have h1' : (m : ℤ) + Module.finrank (ResidueField A) (LinearMap.ker δ) =
        ∑ i, (Module.finrank (ResidueField A) (LSpace (Ebar i)) : ℤ) := by exact_mod_cast h1
    have : ∀ i, (Module.finrank (ResidueField A) (LSpace (Ebar i)) : ℤ) = ell (Ebar i) := fun i => rfl
    simp_rw [this] at h1'
    linarith only [h1']

  have hellbar : ∀ i, (ell (Ebar i) : ℤ) = (Ebar i).degree + 1 - (genusFF (ResidueField A) (Fbar i) : ℤ) := by
    intro i
    apply ell_eq
    have := hdegE' i
    have hc : (0 : ℤ) ≤ (C i).nodes.card := Nat.cast_nonneg _
    linarith only [this, hc]
  have hdegEbar : ∀ i, (Ebar i).degree = (E i).degree := by
    intro i
    rw [degree_eq_sum, degree_eq_sum, hEbar_i, Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]
  have hdegD : D.degree = ∑ i, (E i).degree := by
    rw [hDdef, map_sub, map_add, map_sum, degree_single_eq, degree_single_eq]
    ring
  set k : ℕ := Module.finrank L (riemannRochSpace D) with hk
  have hRiemann : D.degree + 1 - (genusFF L F : ℤ) ≤ (k : ℤ) := degree_add_one_sub_genus_le_ell (K := L) D
  have hgenus' : (genusFF L F : ℤ) + n = (∑ i, (genusFF (ResidueField A) (Fbar i) : ℤ)) + m + 1 := by
    exact_mod_cast hgenus
  have hker_eq : (Module.finrank (ResidueField A) (LinearMap.ker δ) : ℤ) = D.degree + 1 - (genusFF L F : ℤ) := by
    rw [hker]
    have hsum : (∑ i, (ell (Ebar i) : ℤ)) = D.degree + n - ∑ i, (genusFF (ResidueField A) (Fbar i) : ℤ) := by
      simp_rw [hellbar, hdegEbar]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hdegD]
      simp
    rw [hsum]
    linarith only [hgenus']
  have hcount : (Module.finrank (ResidueField A) (LinearMap.ker δ) : ℤ) ≤ k := by
    rw [hker_eq]; exact hRiemann
  have hG_le : Module.finrank (ResidueField A) G ≤ k := by
    have : (Module.finrank (ResidueField A) G : ℤ) ≤ k := le_trans (by exact_mod_cast hG_le_ker) hcount
    exact_mod_cast this
  have hk_pos : 1 ≤ k := by
    have h1 : (1 : ℤ) ≤ (Module.finrank (ResidueField A) (LinearMap.ker δ) : ℤ) := by
      rw [hker]
      have : ((m + 1 : ℕ) : ℤ) ≤ ∑ i, (Module.finrank (ResidueField A) (LSpace (Ebar i)) : ℤ) := by
        exact_mod_cast hsum_ge
      have h2 : ∀ i, (Module.finrank (ResidueField A) (LSpace (Ebar i)) : ℤ) = ell (Ebar i) := fun i => rfl
      simp_rw [h2] at this
      push_cast at this
      linarith only [this]
    have : (1 : ℤ) ≤ k := le_trans h1 hcount
    exact_mod_cast this

  obtain ⟨b, hbi, hbD, hli⟩ :=
    AlgebraicCurve.SemistableCovering.exists_linearIndependent_pi_residue_of_mem_riemannRochSpace_of_rankOne A π hπ
      hπ0 hrk F n m Fbar hratBar C hratF An An' src tgt xs xt w hpair hw hatt hnodes hcover hdisc hgenus D
  set ρ : Fin k → (∀ i, Fbar i) := fun j i => (C i).residue ⟨b j, hbi j i⟩ with hρ
  have hρG : ∀ j, ρ j ∈ G := fun j => (hG_mem _).mpr (nec (b j) (hbi j) (hbD j))
  have hspan_le : Submodule.span (ResidueField A) (Set.range ρ) ≤ G := Submodule.span_le.mpr (by
    rintro _ ⟨j, rfl⟩; exact hρG j)
  have hspan_rank : Module.finrank (ResidueField A) (Submodule.span (ResidueField A) (Set.range ρ)) = k := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hspan_eq : Submodule.span (ResidueField A) (Set.range ρ) = G :=
    Submodule.eq_of_le_of_finrank_le hspan_le (by rw [hspan_rank]; exact hG_le)
  have hmem : sbar ∈ Submodule.span (ResidueField A) (Set.range ρ) := by rw [hspan_eq]; exact hsG
  obtain ⟨cc, hcc⟩ := (Submodule.mem_span_range_iff_exists_fun (ResidueField A)).mp hmem

  set j₀ : Fin k := ⟨0, hk_pos⟩ with hj₀
  have hex : ∀ j, ∃ γ : A, residue A γ = cc j := fun j => Ideal.Quotient.mk_surjective (cc j)
  choose γ' hγ' using hex
  let γ : Fin k → A := fun j => if (∀ j', cc j' = 0) then (if j = j₀ then π else 0) else γ' j
  have hγ : ∀ j, residue A (γ j) = cc j := by
    intro j
    by_cases hall : ∀ j', cc j' = 0
    · simp only [γ, if_pos hall]
      split_ifs
      · rw [hall j]; exact (residue_eq_zero_iff _).mpr hπ
      · rw [hall j, map_zero]
    · simp only [γ, if_neg hall]
      exact hγ' j
  have hγne : ∃ j, γ j ≠ 0 := by
    by_cases hall : ∀ j', cc j' = 0
    · refine ⟨j₀, ?_⟩
      simp only [γ, if_pos hall, if_pos rfl]
      exact hπ0
    · have hall' := hall
      push Not at hall'
      obtain ⟨j, hj⟩ := hall'
      refine ⟨j, fun h0 => hj ?_⟩
      rw [← hγ j]
      simp only [γ, if_neg hall] at h0 ⊢
      rw [h0, map_zero]
  set g : F := ∑ j, (γ j : L) • b j with hg
  have hgi : ∀ i, g ∈ (C i).integers := fun i => sum_smul_mem (C i) γ b (fun j => hbi j i)
  have hgD : g ∈ riemannRochSpace D := (riemannRochSpace D).sum_mem (fun j _ => (riemannRochSpace D).smul_mem _ (hbD j))
  have hred_g : ∀ i, (C i).residue ⟨g, hgi i⟩ = sbar i := by
    intro i
    rw [← red_of_mem, hg, red_sum_smul (C i) γ b (fun j => hbi j i)]
    have := congrFun hcc i
    simp only [Finset.sum_apply, Pi.smul_apply] at this
    rw [← this]
    apply Finset.sum_congr rfl
    intro j _
    rw [hγ, red_of_mem (C i) (hbi j i)]

  have hg0 : g ≠ 0 := by
    intro hg0
    obtain ⟨j₁, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun j => A.valuation (γ j : L))
      ⟨j₀, Finset.mem_univ _⟩
    obtain ⟨j₂, hj₂⟩ := hγne
    have hγ₁0 : (γ j₁ : L) ≠ 0 := by
      intro h0
      have := hmax j₂ (Finset.mem_univ _)
      rw [h0, Valuation.map_zero, le_zero_iff, Valuation.zero_iff] at this
      exact hj₂ (Subtype.ext this)

    have hα : ∀ j, (γ j : L) / γ j₁ ∈ A := by
      intro j
      rw [← A.valuation_le_one_iff, Valuation.map_div]
      have hv1 : A.valuation (γ j₁ : L) ≠ 0 := by rwa [Ne, Valuation.zero_iff]
      rw [div_le_one₀ (lt_of_le_of_ne zero_le' hv1.symm)]
      exact hmax j (Finset.mem_univ j)
    set α : Fin k → A := fun j => ⟨(γ j : L) / γ j₁, hα j⟩ with hαdef
    have hα₁ : α j₁ = 1 := Subtype.ext (div_self hγ₁0)
    have hsum0 : ∑ j, (α j : L) • b j = 0 := by
      have : ∑ j, (α j : L) • b j = (γ j₁ : L)⁻¹ • g := by
        rw [hg, Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [smul_smul]
        congr 1
        show (γ j : L) / γ j₁ = _
        rw [div_eq_inv_mul]
      rw [this, hg0, smul_zero]
    have hrel : ∑ j, (residue A (α j)) • ρ j = 0 := by
      funext i
      rw [Finset.sum_apply, Pi.zero_apply]
      have h1 := red_sum_smul (C i) α b (fun j => hbi j i)
      rw [hsum0, red_zero] at h1
      rw [h1]
      apply Finset.sum_congr rfl
      intro j _
      rw [Pi.smul_apply, hρ, red_of_mem (C i) (hbi j i)]
    have := (Fintype.linearIndependent_iff.mp hli) (fun j => residue A (α j)) hrel j₁
    rw [hα₁, map_one] at this
    exact one_ne_zero this
  exact ⟨g, hg0, hgD, fun i => ⟨hgi i, hred_g i⟩⟩

end

end S_AlgebraicCurve_SemistableCovering_exists_mem_riemannRochSpace_forall_residue_eq_of_glued_of_rankOne
end P2MW
export P2MW.S_AlgebraicCurve_SemistableCovering_exists_mem_riemannRochSpace_forall_residue_eq_of_glued_of_rankOne (solution)
