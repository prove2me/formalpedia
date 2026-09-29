-- Prove2me | solution 1 for AlgebraicCurve.SemistableCovering.finiteDimensional_and_finrank_graded_glued_riemannRochSpace_eq_finrank_of_width_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/b083c3a9-3068-567a-b67c-e59580a37cdc

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_AlgebraicCurve_ell_eq_degree_add_one_sub_genusFF_of_isAlgClosed_of_isSeparable
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_finiteDimensional_lSpace_zero_of_constantsAreBase
import Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_evalAt_eq_zero_iff_one_le_ord
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_nonempty_place_of_transcendental_of_finiteDimensional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_SemistableCovering_finiteDimensional_and_finrank_graded_glued_riemannRochSpace_eq_finrank_of_width_one
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Gamma0Pair.isElliptic"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.gamma0PairMap_gen"
p2m_attr_erase "simp" "ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero"

set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve~genus IsLocalRing"

namespace BDescK9

section PlaceFacts

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem evalAt_zero' (v : Place K F) : v.evalAt (0 : F) = 0 := by
  rw [← map_zero (algebraMap K F), AlgebraicCurve.Place.evalAt_algebraMap]

theorem evalAt_add (v : Place K F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_add, v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg,
    v.algebraMap_evalAt hv (add_mem hf hg), ← map_add]
  rfl

theorem evalAt_const_smul (v : Place K F) (hv : v.IsRational) (c : K) {f : F}
    (hf : f ∈ v.toValuationSubring) : v.evalAt (c • f) = c * v.evalAt f := by
  rw [Algebra.smul_def, AlgebraicCurve.Place.evalAt_mul v hv (v.algebraMap_mem' c) hf,
    AlgebraicCurve.Place.evalAt_algebraMap]

end PlaceFacts

section RR

variable {k F : Type*} [Field k] [IsAlgClosed k] [Field F] [Algebra k F]
variable [IsCurveOver k F] [Algebra.EssFiniteType k F]

theorem rr_package :
    (∀ D : Divisor k F, FiniteDimensional k (LSpace D)) ∧
    ∀ D : Divisor k F, 2 * (genusFF k F : ℤ) - 1 ≤ D.degree →
      (ell D : ℤ) = D.degree + 1 - (genusFF k F : ℤ) := by
  haveI : PerfectField k := IsAlgClosed.perfectField k
  obtain ⟨t, ht, hfd, hsep⟩ := IsCurveOver.exists_separating_transcendental (K := k) (F := F)
  haveI := hfd
  have hC : ConstantsAreBase k F := constantsAreBase_of_isAlgClosed_of_transcendental t ht
  haveI hL0 : FiniteDimensional k (LSpace (0 : Divisor k F)) :=
    RationalFunctionField.finiteDimensional_lSpace_zero_of_constantsAreBase k F hC
  exact ⟨fun D => finiteDimensional_lSpace D,
    fun D hD => ell_eq_degree_add_one_sub_genusFF_of_isAlgClosed_of_isSeparable k t ht hfd hsep D hD⟩

omit [Algebra.EssFiniteType k F] in

theorem isRational (v : Place k F) : v.IsRational :=
  (AlgebraicCurve.Place.isRational_iff_deg_eq_one v).mpr (IsCurveOver.deg_eq_one_of_isAlgClosed v)

omit [Algebra.EssFiniteType k F] in

theorem degree_sum_single (S : Finset (Place k F)) :
    Divisor.degree (∑ x ∈ S, Finsupp.single x (1 : ℤ) : Divisor k F) = S.card := by
  rw [map_sum]
  simp [Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed]

omit [IsAlgClosed k] [IsCurveOver k F] [Algebra.EssFiniteType k F] in
theorem sum_single_apply [DecidableEq (Place k F)] (S : Finset (Place k F)) (v : Place k F) :
    (∑ x ∈ S, Finsupp.single x (1 : ℤ) : Divisor k F) v = if v ∈ S then 1 else 0 := by
  rw [Finsupp.finsetSum_apply]
  have : ∀ x ∈ S, (Finsupp.single x (1 : ℤ) : Divisor k F) v = if x = v then 1 else 0 :=
    fun x _ => by rw [Finsupp.single_apply]
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']

theorem interpolate (D : Divisor k F) (S : Finset (Place k F)) (hS : ∀ x ∈ S, D x = 0)
    (hdeg : 2 * (genusFF k F : ℤ) - 1 + (S.card : ℤ) ≤ D.degree) (val : Place k F → k) :
    ∃ h ∈ riemannRochSpace D, ∀ x ∈ S, x.evalAt h = val x := by
  classical
  obtain ⟨hfin, hRR⟩ := rr_package (k := k) (F := F)
  haveI := hfin D
  have hrat : ∀ v : Place k F, v.IsRational := isRational

  have hregS : ∀ h ∈ LSpace D, ∀ x ∈ S, h ∈ x.toValuationSubring := by
    intro h hh x hx
    rcases eq_or_ne h 0 with rfl | h0
    · exact zero_mem _
    · have hord := (mem_lSpace_iff_ord.mp hh).resolve_left h0 x
      rw [hS x hx, neg_zero] at hord
      exact (AlgebraicCurve.Place.mem_iff_ord_nonneg x h0).mpr hord

  let ev : LSpace D →ₗ[k] (↥S → k) :=
    { toFun := fun h x => (x : Place k F).evalAt (h : F)
      map_add' := fun h₁ h₂ => funext fun x =>
        evalAt_add _ (hrat _) (hregS _ h₁.2 _ x.2) (hregS _ h₂.2 _ x.2)
      map_smul' := fun c h => funext fun x =>
        evalAt_const_smul _ (hrat _) c (hregS _ h.2 _ x.2) }

  set NS : Divisor k F := ∑ x ∈ S, Finsupp.single x (1 : ℤ) with hNSdef
  have hNS : ∀ v, NS v = if v ∈ S then 1 else 0 := fun v => sum_single_apply S v
  have hker : Submodule.map (LSpace D).subtype (LinearMap.ker ev) = LSpace (D - NS) := by
    ext h
    constructor
    · rintro ⟨⟨h, hh⟩, hk, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker] at hk
      show h ∈ LSpace (D - NS)
      rw [mem_lSpace_iff_ord]
      rcases eq_or_ne h 0 with rfl | h0
      · exact Or.inl rfl
      right
      intro v
      rw [Finsupp.sub_apply, hNS]
      by_cases hv : v ∈ S
      · have hval : v.evalAt h = 0 := congr_fun hk ⟨v, hv⟩
        have h1 := (AlgebraicCurve.Place.evalAt_eq_zero_iff_one_le_ord v (hrat v) h0 (hregS h hh v hv)).mp hval
        rw [if_pos hv, hS v hv]
        omega
      · rw [if_neg hv, sub_zero]
        exact (mem_lSpace_iff_ord.mp hh).resolve_left h0 v
    · intro hh
      have hle : D - NS ≤ D := by
        intro v
        rw [Finsupp.sub_apply, hNS]
        split_ifs <;> omega
      have hhD : h ∈ LSpace D := lSpace_mono hle hh
      refine ⟨⟨h, hhD⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      funext x
      show (x : Place k F).evalAt h = 0
      rcases eq_or_ne h 0 with rfl | h0
      · exact evalAt_zero' _
      · apply (AlgebraicCurve.Place.evalAt_eq_zero_iff_one_le_ord _ (hrat _) h0 (hregS h hhD _ x.2)).mpr
        have := (mem_lSpace_iff_ord.mp hh).resolve_left h0 x
        rw [Finsupp.sub_apply, hNS, if_pos x.2, hS _ x.2] at this
        omega

  have hdegNS : NS.degree = S.card := degree_sum_single S
  have hRR1 : (ell D : ℤ) = D.degree + 1 - (genusFF k F : ℤ) := hRR D (by linarith [Nat.cast_nonneg (α := ℤ) S.card])
  have hRR2 : (ell (D - NS) : ℤ) = D.degree - S.card + 1 - (genusFF k F : ℤ) := by
    rw [hRR (D - NS) (by rw [map_sub, hdegNS]; linarith), map_sub, hdegNS]
  have hkerdim : Module.finrank k (LinearMap.ker ev) = ell (D - NS) := by
    rw [← Submodule.finrank_map_subtype_eq (LSpace D) (LinearMap.ker ev), hker]
  have hrn := LinearMap.finrank_range_add_finrank_ker ev
  have hrange : Module.finrank k (LinearMap.range ev) = S.card := by
    have h1 : (Module.finrank k (LinearMap.range ev) : ℤ) + ell (D - NS) = ell D := by
      rw [← hkerdim]; exact_mod_cast hrn
    have h2 : (Module.finrank k (LinearMap.range ev) : ℤ) = S.card := by linarith
    exact_mod_cast h2
  have htop : LinearMap.range ev = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [hrange, Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  have hsurj : Function.Surjective ev := LinearMap.range_eq_top.mp htop
  obtain ⟨⟨h, hh⟩, hev⟩ := hsurj (fun x => val x)
  exact ⟨h, hh, fun x hx => congr_fun hev ⟨x, hx⟩⟩

end RR

section GInterp

variable {k F : Type*} [Field k] [IsAlgClosed k] [Field F] [Algebra k F]
variable [IsCurveOver k F] [Algebra.EssFiniteType k F]

omit [IsAlgClosed k] [IsCurveOver k F] [Algebra.EssFiniteType k F] in

theorem mul_zpow_mem_of_mem_lSpace (D : Divisor k F) (x : Place k F) (z : F) (hz : x.ord z = 1)
    {h : F} (hh : h ∈ LSpace D) : h * z ^ (D x) ∈ x.toValuationSubring := by
  rcases eq_or_ne h 0 with rfl | h0
  · rw [zero_mul]; exact zero_mem _
  have hz0 : z ≠ 0 := by
    intro hz0; rw [hz0, x.ord_zero] at hz; exact zero_ne_one hz
  have hzp0 : z ^ (D x) ≠ 0 := zpow_ne_zero _ hz0
  rw [AlgebraicCurve.Place.mem_iff_ord_nonneg x (mul_ne_zero h0 hzp0), x.ord_mul h0 hzp0,
    x.ord_zpow, hz, mul_one]
  have := (mem_lSpace_iff_ord.mp hh).resolve_left h0 x
  omega

omit [IsAlgClosed k] [IsCurveOver k F] [Algebra.EssFiniteType k F] in

theorem evalAt_mul_zpow_eq_zero_iff (D : Divisor k F) (x : Place k F) (hx : x.IsRational) (z : F) (hz : x.ord z = 1)
    {h : F} (hh : h ∈ LSpace D) (h0 : h ≠ 0) : x.evalAt (h * z ^ (D x)) = 0 ↔ 1 - D x ≤ x.ord h := by
  have hz0 : z ≠ 0 := by
    intro hz0; rw [hz0, x.ord_zero] at hz; exact zero_ne_one hz
  have hzp0 : z ^ (D x) ≠ 0 := zpow_ne_zero _ hz0
  rw [AlgebraicCurve.Place.evalAt_eq_zero_iff_one_le_ord x hx (mul_ne_zero h0 hzp0) (mul_zpow_mem_of_mem_lSpace D x z hz hh),
    x.ord_mul h0 hzp0, x.ord_zpow, hz, mul_one]
  omega

theorem ginterpolate (D : Divisor k F) (S : Finset (Place k F)) (z : Place k F → F) (hz : ∀ x ∈ S, x.ord (z x) = 1)
    (hdeg : 2 * (genusFF k F : ℤ) - 1 + (S.card : ℤ) ≤ D.degree) (val : Place k F → k) :
    ∃ h ∈ riemannRochSpace D, ∀ x ∈ S, x.evalAt (h * z x ^ (D x)) = val x := by
  classical
  obtain ⟨hfin, hRR⟩ := rr_package (k := k) (F := F)
  haveI := hfin D
  have hrat : ∀ v : Place k F, v.IsRational := isRational
  have hregS : ∀ h ∈ LSpace D, ∀ x ∈ S, h * z x ^ (D x) ∈ x.toValuationSubring :=
    fun h hh x hx => mul_zpow_mem_of_mem_lSpace D x (z x) (hz x hx) hh

  let ev : LSpace D →ₗ[k] (↥S → k) :=
    { toFun := fun h x => (x : Place k F).evalAt ((h : F) * z x ^ (D x))
      map_add' := fun h₁ h₂ => funext fun x => by
        show (x : Place k F).evalAt (((h₁ : F) + h₂) * z x ^ (D x)) = _
        rw [add_mul, evalAt_add _ (hrat _) (hregS _ h₁.2 _ x.2) (hregS _ h₂.2 _ x.2)]
        rfl
      map_smul' := fun c h => funext fun x => by
        show (x : Place k F).evalAt ((c • (h : F)) * z x ^ (D x)) = _
        rw [smul_mul_assoc, evalAt_const_smul _ (hrat _) c (hregS _ h.2 _ x.2)]
        rfl }

  set NS : Divisor k F := ∑ x ∈ S, Finsupp.single x (1 : ℤ) with hNSdef
  have hNS : ∀ v, NS v = if v ∈ S then 1 else 0 := fun v => sum_single_apply S v
  have hker : Submodule.map (LSpace D).subtype (LinearMap.ker ev) = LSpace (D - NS) := by
    ext h
    constructor
    · rintro ⟨⟨h, hh⟩, hk, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker] at hk
      show h ∈ LSpace (D - NS)
      rw [mem_lSpace_iff_ord]
      rcases eq_or_ne h 0 with rfl | h0
      · exact Or.inl rfl
      right
      intro v
      rw [Finsupp.sub_apply, hNS]
      by_cases hv : v ∈ S
      · have hval : v.evalAt (h * z v ^ (D v)) = 0 := congr_fun hk ⟨v, hv⟩
        have h1 := (evalAt_mul_zpow_eq_zero_iff D v (hrat v) (z v) (hz v hv) hh h0).mp hval
        rw [if_pos hv]
        omega
      · rw [if_neg hv, sub_zero]
        exact (mem_lSpace_iff_ord.mp hh).resolve_left h0 v
    · intro hh
      have hle : D - NS ≤ D := by
        intro v
        rw [Finsupp.sub_apply, hNS]
        split_ifs <;> omega
      have hhD : h ∈ LSpace D := lSpace_mono hle hh
      refine ⟨⟨h, hhD⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      funext x
      show (x : Place k F).evalAt (h * z x ^ (D x)) = 0
      rcases eq_or_ne h 0 with rfl | h0
      · rw [zero_mul]; exact evalAt_zero' _
      · apply (evalAt_mul_zpow_eq_zero_iff D x (hrat _) (z x) (hz _ x.2) hhD h0).mpr
        have := (mem_lSpace_iff_ord.mp hh).resolve_left h0 x
        rw [Finsupp.sub_apply, hNS, if_pos x.2] at this
        omega

  have hdegNS : NS.degree = S.card := degree_sum_single S
  have hRR1 : (ell D : ℤ) = D.degree + 1 - (genusFF k F : ℤ) := hRR D (by linarith [Nat.cast_nonneg (α := ℤ) S.card])
  have hRR2 : (ell (D - NS) : ℤ) = D.degree - S.card + 1 - (genusFF k F : ℤ) := by
    rw [hRR (D - NS) (by rw [map_sub, hdegNS]; linarith), map_sub, hdegNS]
  have hkerdim : Module.finrank k (LinearMap.ker ev) = ell (D - NS) := by
    rw [← Submodule.finrank_map_subtype_eq (LSpace D) (LinearMap.ker ev), hker]
  have hrn := LinearMap.finrank_range_add_finrank_ker ev
  have hrange : Module.finrank k (LinearMap.range ev) = S.card := by
    have h1 : (Module.finrank k (LinearMap.range ev) : ℤ) + ell (D - NS) = ell D := by
      rw [← hkerdim]; exact_mod_cast hrn
    have h2 : (Module.finrank k (LinearMap.range ev) : ℤ) = S.card := by linarith
    exact_mod_cast h2
  have htop : LinearMap.range ev = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [hrange, Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  have hsurj : Function.Surjective ev := LinearMap.range_eq_top.mp htop
  obtain ⟨⟨h, hh⟩, hev⟩ := hsurj (fun x => val x)
  exact ⟨h, hh, fun x hx => congr_fun hev ⟨x, hx⟩⟩

end GInterp

theorem gmain {k : Type*} [Field k] [IsAlgClosed k]
    {n m : ℕ} (Fb : Fin n → Type*) [∀ i, Field (Fb i)] [∀ i, Algebra k (Fb i)]
    [∀ i, IsCurveOver k (Fb i)] [∀ i, Algebra.EssFiniteType k (Fb i)]
    (N : ∀ i, Finset (Place k (Fb i)))
    (src tgt : Fin m → Fin n) (xs : ∀ e, Place k (Fb (src e))) (xt : ∀ e, Place k (Fb (tgt e)))
    (hxs : ∀ e, xs e ∈ N (src e)) (hxt : ∀ e, xt e ∈ N (tgt e))
    (hN₁ : ∀ i, ∀ x ∈ N i, ∃ e,
        (⟨src e, xs e⟩ : Σ j, Place k (Fb j)) = ⟨i, x⟩ ∨ (⟨tgt e, xt e⟩ : Σ j, Place k (Fb j)) = ⟨i, x⟩)
    (hN₂ : ∀ i, ∀ x ∈ N i, ∀ E E' : Fin m ⊕ Fin m,
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place k (Fb j))) (fun e => ⟨tgt e, xt e⟩) E = ⟨i, x⟩ →
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place k (Fb j))) (fun e => ⟨tgt e, xt e⟩) E' = ⟨i, x⟩ →
          E = E')
    (D : ∀ i, Divisor k (Fb i))
    (hdeg : ∀ i, 2 * (genusFF k (Fb i) : ℤ) - 1 + ((N i).card : ℤ) ≤ (D i).degree)
    (zs : ∀ e, Fb (src e)) (zt : ∀ e, Fb (tgt e))
    (hzs : ∀ e, (xs e).ord (zs e) = 1) (hzt : ∀ e, (xt e).ord (zt e) = 1)
    (c : Fin m → k) :
    ∃ W : Submodule k (∀ i, Fb i),
      (∀ h, h ∈ W ↔ (∀ i, h i ∈ riemannRochSpace (D i)) ∧
        ∀ e, (xs e).evalAt (h (src e) * zs e ^ (D (src e) (xs e))) * c e =
          (xt e).evalAt (h (tgt e) * zt e ^ (D (tgt e) (xt e)))) ∧
      FiniteDimensional k W ∧
      (Module.finrank k W : ℤ) + m = ∑ i, ((D i).degree + 1 - (genusFF k (Fb i) : ℤ)) := by
  classical

  have hfin : ∀ i, ∀ D' : Divisor k (Fb i), FiniteDimensional k (LSpace D') :=
    fun i => (rr_package (k := k) (F := Fb i)).1
  have hRR : ∀ i, ∀ D' : Divisor k (Fb i), 2 * (genusFF k (Fb i) : ℤ) - 1 ≤ D'.degree →
      (ell D' : ℤ) = D'.degree + 1 - (genusFF k (Fb i) : ℤ) :=
    fun i => (rr_package (k := k) (F := Fb i)).2
  have hrat : ∀ i, ∀ v : Place k (Fb i), v.IsRational := fun i v => isRational v
  haveI hfinD : ∀ i, FiniteDimensional k (LSpace (D i)) := fun i => hfin i (D i)

  have hregS : ∀ e, ∀ h ∈ LSpace (D (src e)), h * zs e ^ (D (src e) (xs e)) ∈ (xs e).toValuationSubring :=
    fun e h hh => mul_zpow_mem_of_mem_lSpace (D (src e)) (xs e) (zs e) (hzs e) hh
  have hregT : ∀ e, ∀ h ∈ LSpace (D (tgt e)), h * zt e ^ (D (tgt e) (xt e)) ∈ (xt e).toValuationSubring :=
    fun e h hh => mul_zpow_mem_of_mem_lSpace (D (tgt e)) (xt e) (zt e) (hzt e) hh

  let Φ : (∀ i, ↥(LSpace (D i))) →ₗ[k] (Fin m → k) :=
    { toFun := fun h e => (xs e).evalAt ((h (src e) : Fb (src e)) * zs e ^ (D (src e) (xs e))) * c e -
        (xt e).evalAt ((h (tgt e) : Fb (tgt e)) * zt e ^ (D (tgt e) (xt e)))
      map_add' := fun h₁ h₂ => by
        funext e
        show (xs e).evalAt (((h₁ (src e) : Fb (src e)) + h₂ (src e)) * zs e ^ (D (src e) (xs e))) * c e -
            (xt e).evalAt (((h₁ (tgt e) : Fb (tgt e)) + h₂ (tgt e)) * zt e ^ (D (tgt e) (xt e))) = _
        rw [add_mul, add_mul, evalAt_add _ (hrat _ _) (hregS e _ (h₁ (src e)).2) (hregS e _ (h₂ (src e)).2),
          evalAt_add _ (hrat _ _) (hregT e _ (h₁ (tgt e)).2) (hregT e _ (h₂ (tgt e)).2)]
        simp only [Pi.add_apply]
        ring
      map_smul' := fun a h => by
        funext e
        show (xs e).evalAt ((a • (h (src e) : Fb (src e))) * zs e ^ (D (src e) (xs e))) * c e -
            (xt e).evalAt ((a • (h (tgt e) : Fb (tgt e))) * zt e ^ (D (tgt e) (xt e))) = _
        rw [smul_mul_assoc, smul_mul_assoc, evalAt_const_smul _ (hrat _ _) a (hregS e _ (h (src e)).2),
          evalAt_const_smul _ (hrat _ _) a (hregT e _ (h (tgt e)).2)]
        simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
        ring }
  let ι : (∀ i, ↥(LSpace (D i))) →ₗ[k] (∀ i, Fb i) :=
    LinearMap.pi fun i => (LSpace (D i)).subtype ∘ₗ LinearMap.proj i
  have hιapp : ∀ h i, ι h i = (h i : Fb i) := fun _ _ => rfl
  have hι : Function.Injective ι := by
    intro h h' hh
    funext i
    apply Subtype.ext
    have := congr_fun hh i
    rwa [hιapp, hιapp] at this
  refine ⟨(LinearMap.ker Φ).map ι, ?_, ?_, ?_⟩
  ·
    intro h
    constructor
    · rintro ⟨g, hg, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker] at hg
      refine ⟨fun i => (g i).2, fun e => ?_⟩
      have := congr_fun hg e
      exact sub_eq_zero.mp this
    · rintro ⟨hmem, hagree⟩
      refine ⟨fun i => ⟨h i, hmem i⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      funext e
      exact sub_eq_zero.mpr (hagree e)
  ·
    exact Module.Finite.map _ _
  ·
    have hdimW : Module.finrank k ((LinearMap.ker Φ).map ι) = Module.finrank k (LinearMap.ker Φ) :=
      (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective ι hι _)).symm
    have hV : Module.finrank k (∀ i, ↥(LSpace (D i))) = ∑ i, ell (D i) := Module.finrank_pi_fintype k

    have hsurj : Function.Surjective Φ := by
      intro t
      have hend : ∀ i, ∀ x ∈ N i, ∃ E : Fin m ⊕ Fin m,
          Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place k (Fb j))) (fun e => ⟨tgt e, xt e⟩) E = ⟨i, x⟩ := by
        intro i x hx
        obtain ⟨e, h | h⟩ := hN₁ i x hx
        exacts [⟨Sum.inl e, h⟩, ⟨Sum.inr e, h⟩]
      let val : ∀ i, Place k (Fb i) → k := fun i x =>
        if hx : x ∈ N i then Sum.elim (fun _ => (0 : k)) (fun e => -t e) (Classical.choose (hend i x hx)) else 0

      have hzN : ∀ i, ∀ x ∈ N i, ∃ z : Fb i, x.ord z = 1 ∧
          (∀ e (he : (⟨src e, xs e⟩ : Σ j, Place k (Fb j)) = ⟨i, x⟩), z = cast (congrArg (fun p : (Σ j, Place k (Fb j)) => Fb p.1) he) (zs e)) ∧
          (∀ e (he : (⟨tgt e, xt e⟩ : Σ j, Place k (Fb j)) = ⟨i, x⟩), z = cast (congrArg (fun p : (Σ j, Place k (Fb j)) => Fb p.1) he) (zt e)) := by
        intro i x hx
        obtain ⟨E, hE⟩ := hend i x hx
        rcases E with e | e
        · simp only [Sum.elim_inl] at hE
          obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.mp hE
          have hx' : xs e = x := eq_of_heq h2
          subst hx'
          refine ⟨zs e, hzs e, fun e' he' => ?_, fun e' he' => ?_⟩
          · have := hN₂ _ _ (hxs e) (Sum.inl e') (Sum.inl e) he' rfl
            cases this; rfl
          · have := hN₂ _ _ (hxs e) (Sum.inr e') (Sum.inl e) he' rfl
            cases this
        · simp only [Sum.elim_inr] at hE
          obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.mp hE
          have hx' : xt e = x := eq_of_heq h2
          subst hx'
          refine ⟨zt e, hzt e, fun e' he' => ?_, fun e' he' => ?_⟩
          · have := hN₂ _ _ (hxt e) (Sum.inl e') (Sum.inr e) he' rfl
            cases this
          · have := hN₂ _ _ (hxt e) (Sum.inr e') (Sum.inr e) he' rfl
            cases this; rfl
      let zN : ∀ i, Place k (Fb i) → Fb i := fun i x => if hx : x ∈ N i then (hzN i x hx).choose else 1
      have hzNord : ∀ i, ∀ x ∈ N i, x.ord (zN i x) = 1 := by
        intro i x hx; simp only [zN, dif_pos hx]; exact (hzN i x hx).choose_spec.1
      have hzNs : ∀ e, zN (src e) (xs e) = zs e := by
        intro e; simp only [zN, dif_pos (hxs e)]
        exact (hzN _ _ (hxs e)).choose_spec.2.1 e rfl
      have hzNt : ∀ e, zN (tgt e) (xt e) = zt e := by
        intro e; simp only [zN, dif_pos (hxt e)]
        exact (hzN _ _ (hxt e)).choose_spec.2.2 e rfl
      have hval_s : ∀ e, val (src e) (xs e) = 0 := by
        intro e
        have hE := Classical.choose_spec (hend (src e) (xs e) (hxs e))
        have hinl : Classical.choose (hend (src e) (xs e) (hxs e)) = Sum.inl e :=
          hN₂ _ _ (hxs e) _ _ hE rfl
        simp only [val, dif_pos (hxs e), hinl, Sum.elim_inl]
      have hval_t : ∀ e, val (tgt e) (xt e) = -t e := by
        intro e
        have hE := Classical.choose_spec (hend (tgt e) (xt e) (hxt e))
        have hinr : Classical.choose (hend (tgt e) (xt e) (hxt e)) = Sum.inr e :=
          hN₂ _ _ (hxt e) _ _ hE rfl
        simp only [val, dif_pos (hxt e), hinr, Sum.elim_inr]
      have hcomp : ∀ i, ∃ h ∈ riemannRochSpace (D i), ∀ x ∈ N i, x.evalAt (h * zN i x ^ (D i x)) = val i x :=
        fun i => ginterpolate (D i) (N i) (zN i) (hzNord i) (hdeg i) (val i)
      choose h hh hhv using hcomp
      refine ⟨fun i => ⟨h i, hh i⟩, ?_⟩
      funext e
      show (xs e).evalAt (h (src e) * zs e ^ (D (src e) (xs e))) * c e - (xt e).evalAt (h (tgt e) * zt e ^ (D (tgt e) (xt e))) = t e
      rw [← hzNs e, ← hzNt e, hhv _ _ (hxs e), hhv _ _ (hxt e), hval_s, hval_t, zero_mul, zero_sub, neg_neg]
    have hrangeΦ : Module.finrank k (LinearMap.range Φ) = m := by
      rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    have hrn := LinearMap.finrank_range_add_finrank_ker Φ
    rw [hrangeΦ, hV] at hrn

    have hnat : Module.finrank k ((LinearMap.ker Φ).map ι) + m = ∑ i, ell (D i) := by
      rw [hdimW]; omega
    have hint : (Module.finrank k ((LinearMap.ker Φ).map ι) : ℤ) + m = ∑ i, (ell (D i) : ℤ) := by
      exact_mod_cast hnat
    rw [hint]
    refine Finset.sum_congr rfl fun i _ => hRR i (D i) ?_
    linarith [hdeg i, Nat.cast_nonneg (α := ℤ) (N i).card]

section Helpers

theorem degree_mapDomain_of_deg_eq_one {K F K' F' : Type*} [Field K] [Field F] [Algebra K F]
    [Field K'] [Field F'] [Algebra K' F']
    (hdeg : ∀ v : Place K F, v.deg = 1) (hdeg' : ∀ w : Place K' F', w.deg = 1)
    (r : Place K F → Place K' F') (E : Divisor K F) :
    Divisor.degree (Finsupp.mapDomain r E) = E.degree := by
  induction E using Finsupp.induction_linear with
  | zero => simp [Finsupp.mapDomain]
  | add f g hf hg => rw [Finsupp.mapDomain_add, map_add, map_add, hf, hg]
  | single v n => rw [Finsupp.mapDomain_single, Divisor.degree_single, Divisor.degree_single, hdeg, hdeg']

theorem mapDomain_apply_eq_zero_of_forall {α β M : Type*} [AddCommMonoid M] (f : α → β) (v : α →₀ M)
    (b : β) (h : ∀ a ∈ v.support, f a ≠ b) : Finsupp.mapDomain f v b = 0 := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  exact Finset.sum_eq_zero fun a ha => by
    show Finsupp.single (f a) (v a) b = 0
    rw [Finsupp.single_apply, if_neg (h a ha)]

theorem sum_lap_eq_zero {n m : ℕ} (src tgt : Fin m → Fin n) (φ : Fin n → ℤ) :
    ∑ i : Fin n, ∑ e : Fin m, ((if src e = i then φ i - φ (tgt e) else 0) + (if tgt e = i then φ i - φ (src e) else 0)) = 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro e _
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq]
  simp

open Classical in

theorem sum_degree_mapDomain_filter_eq_degree
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    {n : ℕ} {K' : Type*} [Field K'] (F' : Fin n → Type*) [∀ i, Field (F' i)] [∀ i, Algebra K' (F' i)]
    (hdeg : ∀ v : Place K F, v.deg = 1) (hdeg' : ∀ i, ∀ w : Place K' (F' i), w.deg = 1)
    (r : ∀ i, Place K F → Place K' (F' i)) (dom : Fin n → Set (Place K F))
    (hdisj : ∀ P i j, P ∈ dom i → P ∈ dom j → i = j)
    (D : Divisor K F) (hD : ∀ P ∈ D.support, ∃ i, P ∈ dom i) :
    ∑ i, Divisor.degree (Finsupp.mapDomain (r i) (D.filter fun P => P ∈ dom i) : Divisor K' (F' i)) = D.degree := by
  classical
  have hmap : ∀ i (E : Divisor K F), Divisor.degree (Finsupp.mapDomain (r i) E : Divisor K' (F' i)) = E.degree :=
    fun i E => degree_mapDomain_of_deg_eq_one hdeg (hdeg' i) (r i) E
  simp_rw [hmap]
  rw [← map_sum]
  congr 1
  ext P
  rw [Finsupp.finsetSum_apply]
  simp_rw [Finsupp.filter_apply]
  by_cases hP : P ∈ D.support
  · obtain ⟨i, hi⟩ := hD P hP
    rw [Finset.sum_eq_single i]
    · rw [if_pos hi]
    · intro j _ hji
      rw [if_neg]
      exact fun hj => hji (hdisj P j i hj hi)
    · intro h
      exact absurd (Finset.mem_univ i) h
  · have : D P = 0 := Finsupp.notMem_support_iff.mp hP
    rw [this]
    simp

noncomputable def splitAddHom {ι M : Type*} [AddCommMonoid M] (α : ι → Type*) (i : ι) :
    ((Σ j, α j) →₀ M) →+ (α i →₀ M) where
  toFun l := l.split i
  map_zero' := by ext x; rw [Finsupp.split_apply]; rfl
  map_add' l₁ l₂ := by ext x; simp only [Finsupp.split_apply, Finsupp.add_apply]

theorem splitAddHom_apply {ι M : Type*} [AddCommMonoid M] (α : ι → Type*) (i : ι) (l : (Σ j, α j) →₀ M) :
    splitAddHom α i l = l.split i := rfl

open Classical in
theorem degree_split_single {K' : Type*} [Field K'] {n : ℕ} (F' : Fin n → Type*) [∀ i, Field (F' i)]
    [∀ i, Algebra K' (F' i)] (hdeg' : ∀ i, ∀ w : Place K' (F' i), w.deg = 1)
    (j : Fin n) (y : Place K' (F' j)) (c : ℤ) (i : Fin n) :
    Divisor.degree (Finsupp.split (Finsupp.single (⟨j, y⟩ : Σ l, Place K' (F' l)) c) i : Divisor K' (F' i)) =
      if j = i then c else 0 := by
  by_cases hji : j = i
  · subst hji
    have : (Finsupp.split (Finsupp.single (⟨j, y⟩ : Σ l, Place K' (F' l)) c) j : Divisor K' (F' j)) = Finsupp.single y c := by
      ext x
      rw [Finsupp.split_apply, Finsupp.single_apply, Finsupp.single_apply]
      by_cases hyx : y = x
      · subst hyx; simp
      · rw [if_neg, if_neg hyx]
        intro h
        exact hyx (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
    rw [this, Divisor.degree_single, hdeg', if_pos rfl]
    simp
  · have : (Finsupp.split (Finsupp.single (⟨j, y⟩ : Σ l, Place K' (F' l)) c) i : Divisor K' (F' i)) = 0 := by
      ext x
      rw [Finsupp.split_apply, Finsupp.single_apply, if_neg, Finsupp.zero_apply]
      intro h
      exact hji (Sigma.mk.inj_iff.mp h).1
    rw [this, map_zero, if_neg hji]

end Helpers

end BDescK9

open BDescK9 in
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
    (hw1 : ∀ e, w e = 1)
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
    (φ : Fin n → ℤ)
    (D : Divisor L F) (hD : ∀ P ∈ D.support, ∃ i, P ∈ (C i).dom)
    (hdegD : ∀ i, 2 * (genusFF (IsLocalRing.ResidueField A) (Fbar i) : ℤ) - 1 + ((C i).nodes.card : ℤ) ≤
      Divisor.degree (Finsupp.mapDomain (C i).placeMap (D.filter fun P => P ∈ (C i).dom) :
        Divisor (IsLocalRing.ResidueField A) (Fbar i)) +
      ∑ e, ((if src e = i then φ i - φ (tgt e) else 0) + (if tgt e = i then φ i - φ (src e) else 0)))
    :
    let Dbar : ∀ i, Divisor (IsLocalRing.ResidueField A) (Fbar i) := fun i =>
      Finsupp.mapDomain (C i).placeMap (D.filter fun P => P ∈ (C i).dom)
    let k : Fin m → ℤ := fun e => φ (tgt e) - φ (src e)
    let zs : ∀ e, Fbar (src e) := fun e => (C (src e)).residue ⟨(An e).param, (hatt e).1.2.choose⟩
    let zt : ∀ e, Fbar (tgt e) := fun e => (C (tgt e)).residue ⟨(An' e).param, (hatt e).2.2.choose⟩
    let ubar : Fin m → IsLocalRing.ResidueField A := fun e => IsLocalRing.residue A ((hw e).choose : A)
    let Kdiv : ∀ i, Divisor (IsLocalRing.ResidueField A) (Fbar i) := fun i =>
      Finsupp.split (∑ e, (Finsupp.single (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) (-k e) +
        Finsupp.single (⟨tgt e, xt e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) (k e))) i
    FiniteDimensional (IsLocalRing.ResidueField A)
        (Submodule.span (IsLocalRing.ResidueField A)
          {h : ∀ i, Fbar i |
            (∀ i, h i ∈ riemannRochSpace (Dbar i + Kdiv i)) ∧
            ∀ e, (xs e).evalAt (h (src e) * zs e ^ (-k e)) * ubar e ^ (k e) = (xt e).evalAt (h (tgt e) * zt e ^ (k e))}) ∧
    Module.finrank (IsLocalRing.ResidueField A)
        (Submodule.span (IsLocalRing.ResidueField A)
          {h : ∀ i, Fbar i |
            (∀ i, h i ∈ riemannRochSpace (Dbar i + Kdiv i)) ∧
            ∀ e, (xs e).evalAt (h (src e) * zs e ^ (-k e)) * ubar e ^ (k e) = (xt e).evalAt (h (tgt e) * zt e ^ (k e))}) =
      Module.finrank L (riemannRochSpace D) := by

  intro Dbar k zs zt ubar Kdiv
  classical
  haveI hκ : IsAlgClosed (IsLocalRing.ResidueField ↥A) :=
    ValuationSubring.isAlgClosed_residueField_of_isAlgClosed A
  have hxs : ∀ e, xs e ∈ (C (src e)).nodes := fun e => (hatt e).1.1
  have hxt : ∀ e, xt e ∈ (C (tgt e)).nodes := fun e => (hatt e).2.1
  have hzs : ∀ e, (xs e).ord (zs e) = 1 := fun e => (hatt e).1.2.choose_spec.1
  have hzt : ∀ e, (xt e).ord (zt e) = 1 := fun e => (hatt e).2.2.choose_spec.1

  have hss : ∀ e e', (⟨src e', xs e'⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)) = ⟨src e, xs e⟩ → e' = e := by
    intro e e' h
    have := hnodes.2 _ _ (hxs e) (Sum.inl e') (Sum.inl e) h rfl
    cases this; rfl
  have hts : ∀ e e', (⟨tgt e', xt e'⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)) ≠ ⟨src e, xs e⟩ := by
    intro e e' h
    have := hnodes.2 _ _ (hxs e) (Sum.inr e') (Sum.inl e) h rfl
    cases this
  have hst : ∀ e e', (⟨src e', xs e'⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)) ≠ ⟨tgt e, xt e⟩ := by
    intro e e' h
    have := hnodes.2 _ _ (hxt e) (Sum.inl e') (Sum.inr e) h rfl
    cases this
  have htt : ∀ e e', (⟨tgt e', xt e'⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)) = ⟨tgt e, xt e⟩ → e' = e := by
    intro e e' h
    have := hnodes.2 _ _ (hxt e) (Sum.inr e') (Sum.inr e) h rfl
    cases this; rfl

  have hKs : ∀ e, Kdiv (src e) (xs e) = -k e := by
    intro e
    simp only [Kdiv]
    rw [Finsupp.split_apply, Finsupp.finsetSum_apply]
    rw [Finset.sum_eq_single e]
    · rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply, if_pos rfl, if_neg (hts e e), add_zero]
    · intro e' _ hne
      rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply, if_neg (fun h => hne (hss e e' h)),
        if_neg (hts e e'), add_zero]
    · intro h; exact absurd (Finset.mem_univ e) h
  have hKt : ∀ e, Kdiv (tgt e) (xt e) = k e := by
    intro e
    simp only [Kdiv]
    rw [Finsupp.split_apply, Finsupp.finsetSum_apply]
    rw [Finset.sum_eq_single e]
    · rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply, if_neg (hst e e), if_pos rfl, zero_add]
    · intro e' _ hne
      rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply, if_neg (hst e e'),
        if_neg (fun h => hne (htt e e' h)), add_zero]
    · intro h; exact absurd (Finset.mem_univ e) h

  have hDbarN : ∀ i, ∀ x ∈ (C i).nodes, Dbar i x = 0 := by
    intro i x hx
    simp only [Dbar]
    apply mapDomain_apply_eq_zero_of_forall
    intro Q hQ hQx
    have hQdom : Q ∈ (C i).dom := by
      rw [Finsupp.mem_support_iff, Finsupp.filter_apply] at hQ
      by_contra hnd; exact hQ (if_neg hnd)
    exact (C i).placeMap_not_mem_nodes Q hQdom (hQx ▸ hx)
  set D' : ∀ i, Divisor (IsLocalRing.ResidueField ↥A) (Fbar i) := fun i => Dbar i + Kdiv i with hD'
  have hD's : ∀ e, D' (src e) (xs e) = -k e := by
    intro e; rw [hD', Finsupp.add_apply, hDbarN _ _ (hxs e), hKs, zero_add]
  have hD't : ∀ e, D' (tgt e) (xt e) = k e := by
    intro e; rw [hD', Finsupp.add_apply, hDbarN _ _ (hxt e), hKt, zero_add]

  have hdeg1 : ∀ v : Place L F, v.deg = 1 := fun v => IsCurveOver.deg_eq_one_of_isAlgClosed v
  have hdeg1' : ∀ i, ∀ w : Place (IsLocalRing.ResidueField ↥A) (Fbar i), w.deg = 1 :=
    fun i w => IsCurveOver.deg_eq_one_of_isAlgClosed w
  have hdegK : ∀ i, (Kdiv i).degree =
      ∑ e, ((if src e = i then φ i - φ (tgt e) else 0) + (if tgt e = i then φ i - φ (src e) else 0)) := by
    intro i
    simp only [Kdiv]
    rw [← splitAddHom_apply, map_sum, map_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [map_add, map_add, splitAddHom_apply, splitAddHom_apply,
      degree_split_single Fbar hdeg1', degree_split_single Fbar hdeg1']
    congr 1
    · by_cases h : src e = i
      · subst h
        simp only [if_pos rfl, k]
        ring
      · rw [if_neg h, if_neg h]
    · by_cases h : tgt e = i
      · subst h
        simp only [if_pos rfl, k]
      · rw [if_neg h, if_neg h]
  have hdegD' : ∀ i, 2 * (genusFF (IsLocalRing.ResidueField ↥A) (Fbar i) : ℤ) - 1 + ((C i).nodes.card : ℤ) ≤
      (D' i).degree := by
    intro i
    rw [hD', map_add, hdegK]
    exact hdegD i

  obtain ⟨W, hW, hWfin, hWdim⟩ :=
    gmain Fbar (fun i => (C i).nodes) src tgt xs xt hxs hxt hnodes.1 hnodes.2 D' hdegD' zs zt hzs hzt
      (fun e => ubar e ^ (k e))

  have hSW : {h : ∀ i, Fbar i |
      (∀ i, h i ∈ riemannRochSpace (Dbar i + Kdiv i)) ∧
      ∀ e, (xs e).evalAt (h (src e) * zs e ^ (-k e)) * ubar e ^ (k e) = (xt e).evalAt (h (tgt e) * zt e ^ (k e))} =
      (W : Set (∀ i, Fbar i)) := by
    ext h
    rw [Set.mem_setOf_eq, SetLike.mem_coe, hW]
    simp only [hD's, hD't]
    exact Iff.rfl
  have hspan : Submodule.span (IsLocalRing.ResidueField ↥A) {h : ∀ i, Fbar i |
      (∀ i, h i ∈ riemannRochSpace (Dbar i + Kdiv i)) ∧
      ∀ e, (xs e).evalAt (h (src e) * zs e ^ (-k e)) * ubar e ^ (k e) = (xt e).evalAt (h (tgt e) * zt e ^ (k e))} = W := by
    rw [hSW]; exact Submodule.span_eq W

  have hdisj : ∀ (P : Place L F) (i j : Fin n), P ∈ (C i).dom → P ∈ (C j).dom → i = j := by
    intro P i j hi hj
    rcases hcover P with ⟨i₀, -, huniq, -⟩ | ⟨e, -, -, hnone⟩
    · rw [huniq i hi, huniq j hj]
    · exact absurd hi (hnone i)
  have hsumDbar : ∑ i, (Dbar i).degree = D.degree := by
    simp only [Dbar]
    exact sum_degree_mapDomain_filter_eq_degree Fbar hdeg1 hdeg1' (fun i => (C i).placeMap) (fun i => (C i).dom) hdisj D hD
  have hsumlap := sum_lap_eq_zero src tgt φ
  have hnodecount : 2 * m ≤ ∑ i, (C i).nodes.card := by
    let f : Fin m ⊕ Fin m → (Σ i, ↥(C i).nodes) :=
      Sum.elim (fun e => ⟨src e, ⟨xs e, hxs e⟩⟩) (fun e => ⟨tgt e, ⟨xt e, hxt e⟩⟩)
    have key : ∀ E : Fin m ⊕ Fin m,
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E = ⟨(f E).1, ((f E).2 : Place _ _)⟩ := by
      rintro (e | e) <;> rfl
    have hf : Function.Injective f := by
      intro E E' hEE'
      apply hnodes.2 (f E).1 (f E).2 (f E).2.2 E E' (key E)
      rw [key E', hEE']
    have := Fintype.card_le_of_injective f hf
    simpa [Fintype.card_sum, Fintype.card_fin, Fintype.card_sigma, Fintype.card_coe, two_mul] using this
  have hn : 0 < n := by
    obtain ⟨t, ht, hfd, hsep⟩ := IsCurveOver.exists_separating_transcendental (K := L) (F := F)
    haveI := hsep
    obtain ⟨P⟩ := AlgebraicCurve.nonempty_place_of_transcendental_of_finiteDimensional L t ht hfd
    rcases hcover P with ⟨i, -⟩ | ⟨e, -⟩
    · exact Fin.pos i
    · exact Fin.pos (src e)

  obtain ⟨hfinF, hRRF⟩ := rr_package (k := L) (F := F)
  have hg : (genusFF L F : ℤ) + n = (∑ i, (genusFF (IsLocalRing.ResidueField ↥A) (Fbar i) : ℤ)) + m + 1 := by
    exact_mod_cast hgenus
  have hc2 : (2 * m : ℤ) ≤ ∑ i, ((C i).nodes.card : ℤ) := by exact_mod_cast hnodecount
  have hn' : (1 : ℤ) ≤ n := by exact_mod_cast hn
  have hsumD' : ∑ i, (D' i).degree = D.degree := by
    have : ∀ i, (D' i).degree = (Dbar i).degree + (Kdiv i).degree := fun i => by rw [hD', map_add]
    simp_rw [this, Finset.sum_add_distrib, hsumDbar, hdegK, hsumlap, add_zero]
  have hsum1 : ∑ i, (2 * (genusFF (IsLocalRing.ResidueField ↥A) (Fbar i) : ℤ) - 1 + ((C i).nodes.card : ℤ)) ≤
      ∑ i, (D' i).degree := Finset.sum_le_sum fun i _ => hdegD' i
  have hsum1' : ∑ i, (2 * (genusFF (IsLocalRing.ResidueField ↥A) (Fbar i) : ℤ) - 1 + ((C i).nodes.card : ℤ)) =
      2 * (∑ i, (genusFF (IsLocalRing.ResidueField ↥A) (Fbar i) : ℤ)) - n + ∑ i, ((C i).nodes.card : ℤ) := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp
  have hdegD2 : 2 * (genusFF L F : ℤ) - 1 ≤ D.degree := by
    rw [← hsumD']; linarith
  have hellZ : (ell D : ℤ) = D.degree + 1 - (genusFF L F : ℤ) := hRRF D hdegD2
  have hWZ : (Module.finrank (IsLocalRing.ResidueField ↥A) W : ℤ) =
      D.degree + n - (∑ i, (genusFF (IsLocalRing.ResidueField ↥A) (Fbar i) : ℤ)) - m := by
    have h1 : ∑ i, ((D' i).degree + 1 - (genusFF (IsLocalRing.ResidueField ↥A) (Fbar i) : ℤ)) =
        D.degree + n - ∑ i, (genusFF (IsLocalRing.ResidueField ↥A) (Fbar i) : ℤ) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hsumD']
      simp
    linarith [hWdim, h1]
  have hWell : (Module.finrank (IsLocalRing.ResidueField ↥A) W : ℤ) = (ell D : ℤ) := by
    rw [hWZ, hellZ]; linarith
  have hfinrank : Module.finrank (IsLocalRing.ResidueField ↥A) W = Module.finrank L (riemannRochSpace D) := by
    exact_mod_cast hWell
  refine ⟨?_, ?_⟩
  · rw [hspan]; exact hWfin
  · rw [hspan]; exact hfinrank

end
end S_AlgebraicCurve_SemistableCovering_finiteDimensional_and_finrank_graded_glued_riemannRochSpace_eq_finrank_of_width_one
end P2MW
export P2MW.S_AlgebraicCurve_SemistableCovering_finiteDimensional_and_finrank_graded_glued_riemannRochSpace_eq_finrank_of_width_one (solution)
