-- Prove2me | solution 1 for AlgebraicCurve.SemistableCovering.finiteDimensional_and_finrank_glued_riemannRochSpace_eq_finrank_of_rankOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/d29c685a-de81-50ad-9948-fe6fbd667b83

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Theorems.Thm_AlgebraicCurve_ell_eq_degree_add_one_sub_genusFF_of_isAlgClosed_of_isSeparable
import Theorems.Thm_AlgebraicCurve_exists_transcendental_isSeparable_of_finrank_kaehlerDifferential_eq_one
import Theorems.Thm_AlgebraicCurve_Place_evalAt_eq_zero_iff_one_le_ord
import Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_SemistableCovering_finiteDimensional_and_finrank_glued_riemannRochSpace_eq_finrank_of_rankOne
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue"
p2m_attr_erase "instance" "AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Gamma0Pair.isElliptic"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X"
p2m_attr_erase "simp" "ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply"
p2m_attr_erase "simp" "ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero"

set_option autoImplicit false

p2m_open "AlgebraicCurve~genus"
open scoped IntermediateField

namespace Ws22
namespace DIM

section Eval

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem evalAt_eq_of_algebraMap_eq (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) {a : K}
    (h : algebraMap K v.ResidueField a = IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩) : v.evalAt f = a := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv hf, h]

theorem evalAt_add (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply evalAt_eq_of_algebraMap_eq v hv (add_mem hf hg)
  rw [map_add, v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg, ← map_add]
  rfl

theorem evalAt_algebraMap (hv : v.IsRational) (a : K) : v.evalAt (algebraMap K F a) = a := by
  have ha : algebraMap K F a ∈ v.toValuationSubring := (algebraMap K v.toValuationSubring a).2
  apply evalAt_eq_of_algebraMap_eq v hv ha
  rw [IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField]
  rfl

theorem evalAt_smul (hv : v.IsRational) (a : K) {f : F} (hf : f ∈ v.toValuationSubring) :
    v.evalAt (a • f) = a * v.evalAt f := by
  have ha : algebraMap K F a ∈ v.toValuationSubring := (algebraMap K v.toValuationSubring a).2
  rw [Algebra.smul_def, Place.evalAt_mul v hv ha hf, evalAt_algebraMap v hv]

theorem evalAt_zero' : v.evalAt (0 : F) = 0 := by
  by_cases hv : v.IsRational
  · have := evalAt_algebraMap v hv 0
    rwa [map_zero] at this
  · rw [v.evalAt_of_mem (zero_mem _)]
    have h0 : (⟨(0 : F), zero_mem _⟩ : v.toValuationSubring) = 0 := rfl
    rw [h0, map_zero, ← map_zero (algebraMap K v.ResidueField), v.residueInv_algebraMap]

theorem mem_toValuationSubring_of_ord_nonneg {f : F} (h : 0 ≤ v.ord f) : f ∈ v.toValuationSubring := by
  rcases eq_or_ne f 0 with rfl | hf
  · exact zero_mem _
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu]
  refine mul_mem (u : v.toValuationSubring).2 ?_
  lift v.ord f to ℕ using h with n hn
  rw [zpow_natCast]
  exact pow_mem π.2 n

theorem mem_toValuationSubring_of_mem_lSpace {D : Divisor K F} {f : F} (hf : f ∈ LSpace D) (hD : D v ≤ 0) :
    f ∈ v.toValuationSubring := by
  rcases mem_lSpace_iff_ord.mp hf with h0 | h
  · rw [h0]; exact zero_mem _
  · have := h v
    exact mem_toValuationSubring_of_ord_nonneg v (by omega)

end Eval

section RR

variable (k : Type*) [Field k] [IsAlgClosed k] (F : Type*) [Field F] [Algebra k F] [IsCurveOver k F]
  [Algebra.EssFiniteType k F]

theorem algebra_transcendental : Algebra.Transcendental k F := by
  rw [Algebra.transcendental_iff_not_isAlgebraic]
  intro halg
  have hsurj : Function.Surjective (algebraMap k F) := IsSepClosed.algebraMap_surjective k F
  have hbot : (⊤ : Submodule F Ω[F⁄k]) = ⊥ := by
    rw [← KaehlerDifferential.span_range_derivation, Submodule.span_eq_bot]
    rintro _ ⟨s, rfl⟩
    obtain ⟨r, rfl⟩ := hsurj s
    exact Derivation.map_algebraMap _ r
  have h0 : Module.finrank F Ω[F⁄k] = 0 := by
    rw [← finrank_top, hbot, finrank_bot]
  have h1 := IsCurveOver.finrank_kaehler (K := k) (F := F)
  omega

theorem riemannRoch (D : Divisor k F) (hD : 2 * (genusFF k F : ℤ) - 1 ≤ D.degree) :
    (ell D : ℤ) = D.degree + 1 - (genusFF k F : ℤ) := by
  haveI := algebra_transcendental k F
  obtain ⟨t, ht, hfin, hsep⟩ := exists_transcendental_isSeparable_of_finrank_kaehlerDifferential_eq_one (K := k) (F := F)
    (IsCurveOver.finrank_kaehler (K := k) (F := F))
  exact ell_eq_degree_add_one_sub_genusFF_of_isAlgClosed_of_isSeparable k t ht hfin hsep D hD

theorem finiteDimensional_lSpace (D : Divisor k F) (hD : 2 * (genusFF k F : ℤ) - 1 ≤ D.degree) :
    FiniteDimensional k (LSpace D) := by
  have hRR := riemannRoch k F D hD
  by_cases hpos : 0 < D.degree + 1 - (genusFF k F : ℤ)
  · have : 0 < Module.finrank k (LSpace D) := by
      have h : (0 : ℤ) < (ell D : ℤ) := by rw [hRR]; exact hpos
      exact_mod_cast h
    exact Module.finite_of_finrank_pos this
  ·
    have hdeg : D.degree = -1 := by omega
    have hD0 : D ≠ 0 := fun h0 => by rw [h0, map_zero] at hdeg; exact absurd hdeg (by norm_num)
    have hsupp : D.support.Nonempty := Finset.nonempty_iff_ne_empty.2 (by rwa [Ne, Finsupp.support_eq_empty])
    obtain ⟨P, -⟩ := hsupp
    by_contra hinf
    have h1 := riemannRoch k F (D + Finsupp.single P 1) (by
      rw [map_add, Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed (K := k) (F := F) P]; push_cast; omega)
    have hle : LSpace D ≤ LSpace (D + Finsupp.single P 1) :=
      lSpace_mono (le_add_of_nonneg_right (Finsupp.single_nonneg.2 zero_le_one))
    by_cases hfin : FiniteDimensional k (LSpace (D + Finsupp.single P 1))
    · exact hinf (Submodule.finiteDimensional_of_le hle)
    · have : ell (D + Finsupp.single P 1) = 0 := Module.finrank_of_not_finite hfin
      rw [this, map_add, Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed (K := k) (F := F) P] at h1
      push_cast at h1
      have : ell D = 0 := Module.finrank_of_not_finite hinf
      rw [this] at hRR
      push_cast at hRR
      omega

theorem degree_eq_sum (D : Divisor k F) : D.degree = D.sum fun _ n => n := by
  show Finsupp.liftAddHom (fun v : Place k F => AddMonoidHom.mulRight (v.deg : ℤ)) D = _
  rw [Finsupp.liftAddHom_apply]
  refine Finsupp.sum_congr fun v _ => ?_
  rw [AddMonoidHom.mulRight_apply, IsCurveOver.deg_eq_one_of_isAlgClosed (K := k) (F := F) v, Nat.cast_one, mul_one]

end RR

section NodeEval

variable (k : Type*) [Field k] [IsAlgClosed k] (F : Type*) [Field F] [Algebra k F] [IsCurveOver k F]
  [Algebra.EssFiniteType k F]

noncomputable def nodeDivisor (N : Finset (Place k F)) : Divisor k F := ∑ x ∈ N, Finsupp.single x 1

omit [IsAlgClosed k] [IsCurveOver k F] [Algebra.EssFiniteType k F] in
theorem nodeDivisor_apply [DecidableEq (Place k F)] (N : Finset (Place k F)) (v : Place k F) :
    nodeDivisor k F N v = if v ∈ N then 1 else 0 := by
  rw [nodeDivisor, Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_ite_eq' N v (fun _ => (1 : ℤ))]

omit [Algebra.EssFiniteType k F] in
theorem degree_nodeDivisor (N : Finset (Place k F)) : (nodeDivisor k F N).degree = N.card := by
  rw [nodeDivisor, map_sum]
  simp only [Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed (K := k) (F := F), Nat.cast_one, mul_one]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]

variable {k F} in
omit [IsAlgClosed k] [IsCurveOver k F] [Algebra.EssFiniteType k F] in
theorem mem_toValuationSubring_of_mem_lSpace_of_apply_eq_zero {D : Divisor k F} {f : F} (hf : f ∈ LSpace D)
    {x : Place k F} (hx : D x = 0) : f ∈ x.toValuationSubring :=
  mem_toValuationSubring_of_mem_lSpace x hf hx.le

noncomputable def nodeEval (D : Divisor k F) (N : Finset (Place k F)) (hN : ∀ x ∈ N, D x = 0)
    (hrat : ∀ x ∈ N, x.IsRational) : LSpace D →ₗ[k] (↥N → k) where
  toFun f x := x.1.evalAt (f : F)
  map_add' f g := by
    funext x
    exact evalAt_add x.1 (hrat x.1 x.2) (mem_toValuationSubring_of_mem_lSpace_of_apply_eq_zero f.2 (hN x.1 x.2))
      (mem_toValuationSubring_of_mem_lSpace_of_apply_eq_zero g.2 (hN x.1 x.2))
  map_smul' a f := by
    funext x
    exact evalAt_smul x.1 (hrat x.1 x.2) a (mem_toValuationSubring_of_mem_lSpace_of_apply_eq_zero f.2 (hN x.1 x.2))

theorem nodeEval_apply (D : Divisor k F) (N : Finset (Place k F)) (hN : ∀ x ∈ N, D x = 0)
    (hrat : ∀ x ∈ N, x.IsRational) (f : LSpace D) (x : ↥N) : nodeEval k F D N hN hrat f x = x.1.evalAt (f : F) := rfl

theorem mem_ker_nodeEval_iff (D : Divisor k F) (N : Finset (Place k F)) (hN : ∀ x ∈ N, D x = 0)
    (hrat : ∀ x ∈ N, x.IsRational) (f : LSpace D) :
    f ∈ LinearMap.ker (nodeEval k F D N hN hrat) ↔ (f : F) ∈ LSpace (D - nodeDivisor k F N) := by
  classical
  rw [LinearMap.mem_ker]
  constructor
  · intro h0
    have hx : ∀ x : ↥N, x.1.evalAt (f : F) = 0 := fun x => by rw [← nodeEval_apply k F D N hN hrat f x, h0]; rfl
    rw [mem_lSpace_iff_ord]
    rcases eq_or_ne (f : F) 0 with hf0 | hf0
    · exact Or.inl hf0
    right
    intro v
    rw [Finsupp.sub_apply, nodeDivisor_apply]
    rcases mem_lSpace_iff_ord.mp f.2 with h | h
    · exact absurd h hf0
    by_cases hv : v ∈ N
    · rw [if_pos hv, hN v hv]
      have hmem : (f : F) ∈ v.toValuationSubring := mem_toValuationSubring_of_mem_lSpace_of_apply_eq_zero f.2 (hN v hv)
      have := (Place.evalAt_eq_zero_iff_one_le_ord v (hrat v hv) hf0 hmem).1 (hx ⟨v, hv⟩)
      omega
    · rw [if_neg hv, sub_zero]
      exact h v
  · intro hf
    funext x
    rw [nodeEval_apply]
    show x.1.evalAt (f : F) = 0
    rcases eq_or_ne (f : F) 0 with hf0 | hf0
    · rw [hf0]; exact evalAt_zero' x.1
    rcases mem_lSpace_iff_ord.mp hf with h | h
    · exact absurd h hf0
    have hmem : (f : F) ∈ x.1.toValuationSubring := mem_toValuationSubring_of_mem_lSpace_of_apply_eq_zero f.2 (hN x.1 x.2)
    refine (Place.evalAt_eq_zero_iff_one_le_ord x.1 (hrat x.1 x.2) hf0 hmem).2 ?_
    have := h x.1
    rw [Finsupp.sub_apply, nodeDivisor_apply, if_pos x.2, hN x.1 x.2] at this
    omega

theorem lSpace_sub_nodeDivisor_le (D : Divisor k F) (N : Finset (Place k F)) : LSpace (D - nodeDivisor k F N) ≤ LSpace D := by
  classical
  refine lSpace_mono ?_
  intro v
  rw [Finsupp.sub_apply, nodeDivisor_apply]
  split_ifs <;> omega

theorem finrank_and_nodeEval_surjective (D : Divisor k F) (N : Finset (Place k F)) (hN : ∀ x ∈ N, D x = 0)
    (hrat : ∀ x ∈ N, x.IsRational) (hdeg : 2 * (genusFF k F : ℤ) - 1 + N.card ≤ D.degree) :
    FiniteDimensional k (LSpace D) ∧ (Module.finrank k (LSpace D) : ℤ) = D.degree + 1 - genusFF k F ∧
      Function.Surjective (nodeEval k F D N hN hrat) := by
  have hdegD : 2 * (genusFF k F : ℤ) - 1 ≤ D.degree := by
    have : (0 : ℤ) ≤ N.card := Nat.cast_nonneg _
    omega
  haveI hfd : FiniteDimensional k (LSpace D) := finiteDimensional_lSpace k F D hdegD
  have hRR : (Module.finrank k (LSpace D) : ℤ) = D.degree + 1 - genusFF k F := riemannRoch k F D hdegD
  refine ⟨hfd, hRR, ?_⟩

  have hdeg' : (D - nodeDivisor k F N).degree = D.degree - N.card := by rw [map_sub, degree_nodeDivisor]
  have hRR' : (ell (D - nodeDivisor k F N) : ℤ) = D.degree - N.card + 1 - genusFF k F := by
    rw [← hdeg']; exact riemannRoch k F _ (by rw [hdeg']; omega)
  let e := Submodule.comapSubtypeEquivOfLe (lSpace_sub_nodeDivisor_le k F D N)
  have hker : LinearMap.ker (nodeEval k F D N hN hrat) = (LSpace (D - nodeDivisor k F N)).comap (LSpace D).subtype := by
    ext f
    rw [mem_ker_nodeEval_iff, Submodule.mem_comap]
    rfl
  have hkerrk : (Module.finrank k (LinearMap.ker (nodeEval k F D N hN hrat)) : ℤ) = D.degree - N.card + 1 - genusFF k F := by
    rw [hker, LinearEquiv.finrank_eq e]
    exact hRR'
  have hrn := LinearMap.finrank_range_add_finrank_ker (nodeEval k F D N hN hrat)
  have hrange : Module.finrank k (LinearMap.range (nodeEval k F D N hN hrat)) = N.card := by
    have h1 : (Module.finrank k (LinearMap.range (nodeEval k F D N hN hrat)) : ℤ) +
        Module.finrank k (LinearMap.ker (nodeEval k F D N hN hrat)) = Module.finrank k (LSpace D) := by exact_mod_cast hrn
    rw [hkerrk, hRR] at h1
    have : (Module.finrank k (LinearMap.range (nodeEval k F D N hN hrat)) : ℤ) = N.card := by omega
    exact_mod_cast this
  have htop : LinearMap.range (nodeEval k F D N hN hrat) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [hrange, Module.finrank_pi k, Fintype.card_coe]
  exact LinearMap.range_eq_top.1 htop

end NodeEval

end Ws22.DIM

namespace Ws22
namespace DIM

p2m_open "AlgebraicCurve~genus"

noncomputable def coeffSum {ι : Type*} : (ι →₀ ℤ) →+ ℤ := Finsupp.liftAddHom fun _ => AddMonoidHom.id ℤ

theorem coeffSum_apply {ι : Type*} (D : ι →₀ ℤ) : coeffSum D = D.sum fun _ n => n := by
  show Finsupp.liftAddHom (fun _ : ι => AddMonoidHom.id ℤ) D = _
  rw [Finsupp.liftAddHom_apply]
  rfl

theorem coeffSum_mapDomain {ι ι' : Type*} (f : ι → ι') (D : ι →₀ ℤ) : coeffSum (Finsupp.mapDomain f D) = coeffSum D := by
  rw [coeffSum_apply, coeffSum_apply]
  exact Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)

end Ws22.DIM

open Classical in
open Ws22.DIM in
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
    (D : Divisor L F) (hD : ∀ P ∈ D.support, ∃ i, P ∈ (C i).dom)
    (hdegD : ∀ i, 2 * (genusFF (IsLocalRing.ResidueField A) (Fbar i) : ℤ) - 1 + ((C i).nodes.card : ℤ) ≤
      Divisor.degree (Finsupp.mapDomain (C i).placeMap (D.filter fun P => P ∈ (C i).dom) :
        Divisor (IsLocalRing.ResidueField A) (Fbar i)))
    :
    FiniteDimensional (IsLocalRing.ResidueField A)
        (Submodule.span (IsLocalRing.ResidueField A)
          {h : ∀ i, Fbar i |
            (∀ i, h i ∈ riemannRochSpace (Finsupp.mapDomain (C i).placeMap (D.filter fun P => P ∈ (C i).dom) :
              Divisor (IsLocalRing.ResidueField A) (Fbar i))) ∧
            ∀ e, (xs e).evalAt (h (src e)) = (xt e).evalAt (h (tgt e))}) ∧
    Module.finrank (IsLocalRing.ResidueField A)
        (Submodule.span (IsLocalRing.ResidueField A)
          {h : ∀ i, Fbar i |
            (∀ i, h i ∈ riemannRochSpace (Finsupp.mapDomain (C i).placeMap (D.filter fun P => P ∈ (C i).dom) :
              Divisor (IsLocalRing.ResidueField A) (Fbar i))) ∧
            ∀ e, (xs e).evalAt (h (src e)) = (xt e).evalAt (h (tgt e))}) =
      Module.finrank L (riemannRochSpace D) := by
  classical
  haveI hκ : IsAlgClosed (IsLocalRing.ResidueField A) := ValuationSubring.isAlgClosed_residueField_of_isAlgClosed A

  set Dbar : ∀ i, Divisor (IsLocalRing.ResidueField A) (Fbar i) :=
    fun i => (Finsupp.mapDomain (C i).placeMap (D.filter fun P => P ∈ (C i).dom) : Divisor (IsLocalRing.ResidueField A) (Fbar i)) with hDbar
  have hN : ∀ i, ∀ x ∈ (C i).nodes, Dbar i x = 0 := by
    intro i x hx
    rw [← Finsupp.notMem_support_iff]
    intro hmem
    have := Finsupp.mapDomain_support hmem
    rw [Finset.mem_image] at this
    obtain ⟨P, hP, rfl⟩ := this
    rw [Finsupp.support_filter, Finset.mem_filter] at hP
    exact (C i).placeMap_not_mem_nodes P hP.2 hx

  have E2 := fun i => finrank_and_nodeEval_surjective (IsLocalRing.ResidueField A) (Fbar i) (Dbar i) (C i).nodes (hN i)
    (fun x _ => hratBar i x) (hdegD i)
  haveI hfdV : ∀ i, FiniteDimensional (IsLocalRing.ResidueField A) (LSpace (Dbar i)) := fun i => (E2 i).1

  have hsrc : ∀ e, xs e ∈ (C (src e)).nodes := fun e => (hatt e).1.1
  have htgt : ∀ e, xt e ∈ (C (tgt e)).nodes := fun e => (hatt e).2.1
  let Ψ : (∀ i, LSpace (Dbar i)) →ₗ[(IsLocalRing.ResidueField A)] (Fin m → (IsLocalRing.ResidueField A)) :=
    { toFun := fun h e => nodeEval (IsLocalRing.ResidueField A) (Fbar (src e)) (Dbar (src e)) (C (src e)).nodes (hN (src e))
          (fun x _ => hratBar (src e) x) (h (src e)) ⟨xs e, hsrc e⟩ -
        nodeEval (IsLocalRing.ResidueField A) (Fbar (tgt e)) (Dbar (tgt e)) (C (tgt e)).nodes (hN (tgt e))
          (fun x _ => hratBar (tgt e) x) (h (tgt e)) ⟨xt e, htgt e⟩
      map_add' := fun h h' => by
        funext e
        simp only [Pi.add_apply, map_add]
        ring
      map_smul' := fun a h => by
        funext e
        simp only [Pi.smul_apply, map_smul, smul_eq_mul, RingHom.id_apply]
        ring }
  have hΨ : ∀ (h : (∀ i, LSpace (Dbar i))) (e : Fin m), Ψ h e = (xs e).evalAt ((h (src e) : Fbar (src e))) - (xt e).evalAt ((h (tgt e) : Fbar (tgt e))) :=
    fun h e => rfl

  let ι : (∀ i, LSpace (Dbar i)) →ₗ[(IsLocalRing.ResidueField A)] (∀ i, Fbar i) :=
    { toFun := fun h i => (h i : Fbar i)
      map_add' := fun h h' => rfl
      map_smul' := fun a h => rfl }
  have hι : Function.Injective ι := by
    intro h h' hh
    funext i
    exact Subtype.ext (congr_fun hh i)

  have hset : {h : ∀ i, Fbar i |
      (∀ i, h i ∈ riemannRochSpace (Finsupp.mapDomain (C i).placeMap (D.filter fun P => P ∈ (C i).dom) :
        Divisor (IsLocalRing.ResidueField A) (Fbar i))) ∧
      ∀ e, (xs e).evalAt (h (src e)) = (xt e).evalAt (h (tgt e))} = ((LinearMap.ker Ψ).map ι : Set (∀ i, Fbar i)) := by
    ext h
    simp only [Set.mem_setOf_eq, Submodule.map_coe, Set.mem_image, SetLike.mem_coe, LinearMap.mem_ker]
    constructor
    · rintro ⟨hmem, hagree⟩
      refine ⟨fun i => ⟨h i, hmem i⟩, ?_, rfl⟩
      funext e
      rw [hΨ, Pi.zero_apply, sub_eq_zero]
      exact hagree e
    · rintro ⟨g, hg, rfl⟩
      refine ⟨fun i => (g i).2, fun e => ?_⟩
      have := congr_fun hg e
      rw [hΨ, Pi.zero_apply, sub_eq_zero] at this
      exact this
  have hspan : Submodule.span (IsLocalRing.ResidueField A) {h : ∀ i, Fbar i |
      (∀ i, h i ∈ riemannRochSpace (Finsupp.mapDomain (C i).placeMap (D.filter fun P => P ∈ (C i).dom) :
        Divisor (IsLocalRing.ResidueField A) (Fbar i))) ∧
      ∀ e, (xs e).evalAt (h (src e)) = (xt e).evalAt (h (tgt e))} = (LinearMap.ker Ψ).map ι := by
    rw [hset, Submodule.span_eq]
  rw [hspan]
  haveI : FiniteDimensional (IsLocalRing.ResidueField A) (∀ i, LSpace (Dbar i)) := inferInstance
  refine ⟨inferInstance, ?_⟩
  rw [← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective ι hι (LinearMap.ker Ψ))]

  have hΨsurj : Function.Surjective Ψ := by
    intro c

    have hlab : ∀ i (x : ↥(C i).nodes), ∃ E : Fin m ⊕ Fin m,
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j))) (fun e => ⟨tgt e, xt e⟩) E = ⟨i, x.1⟩ := by
      intro i x
      obtain ⟨e, he | he⟩ := hnodes.1 i x.1 x.2
      · exact ⟨Sum.inl e, he⟩
      · exact ⟨Sum.inr e, he⟩
    choose lab hlab' using hlab
    let val : ∀ i, ↥(C i).nodes → (IsLocalRing.ResidueField A) := fun i x => Sum.elim c (fun _ => 0) (lab i x)
    have hval_src : ∀ e, val (src e) ⟨xs e, hsrc e⟩ = c e := by
      intro e
      have hE : lab (src e) ⟨xs e, hsrc e⟩ = Sum.inl e :=
        hnodes.2 (src e) (xs e) (hsrc e) _ _ (hlab' (src e) ⟨xs e, hsrc e⟩) rfl
      simp only [val, hE, Sum.elim_inl]
    have hval_tgt : ∀ e, val (tgt e) ⟨xt e, htgt e⟩ = 0 := by
      intro e
      have hE : lab (tgt e) ⟨xt e, htgt e⟩ = Sum.inr e :=
        hnodes.2 (tgt e) (xt e) (htgt e) _ _ (hlab' (tgt e) ⟨xt e, htgt e⟩) rfl
      simp only [val, hE, Sum.elim_inr]
    choose h hh using fun i => (E2 i).2.2 (val i)
    refine ⟨h, funext fun e => ?_⟩
    show nodeEval _ _ _ _ _ _ (h (src e)) ⟨xs e, hsrc e⟩ - nodeEval _ _ _ _ _ _ (h (tgt e)) ⟨xt e, htgt e⟩ = c e
    rw [hh (src e), hh (tgt e), hval_src, hval_tgt, sub_zero]

  have hrn := LinearMap.finrank_range_add_finrank_ker Ψ
  rw [LinearMap.range_eq_top.2 hΨsurj, finrank_top, Module.finrank_pi (IsLocalRing.ResidueField A), Fintype.card_fin] at hrn
  have hW0 : Module.finrank (IsLocalRing.ResidueField A) (∀ i, LSpace (Dbar i)) = ∑ i, Module.finrank (IsLocalRing.ResidueField A) (LSpace (Dbar i)) := Module.finrank_pi_fintype (IsLocalRing.ResidueField A)

  have hdegsum : ∑ i, (Dbar i).degree = D.degree := by
    have h1 : ∀ i, (Dbar i).degree = coeffSum (D.filter fun P => P ∈ (C i).dom) := by
      intro i
      rw [degree_eq_sum (IsLocalRing.ResidueField A) (Fbar i), ← coeffSum_apply]
      exact coeffSum_mapDomain (C i).placeMap _
    simp only [h1]
    rw [← map_sum, degree_eq_sum L F, ← coeffSum_apply]
    congr 1
    ext P
    rw [Finsupp.finsetSum_apply]
    simp only [Finsupp.filter_apply]
    by_cases hP : D P = 0
    · simp [hP]
    · obtain ⟨i, hi⟩ := hD P (Finsupp.mem_support_iff.2 hP)
      have huniq : ∀ j, P ∈ (C j).dom → j = i := by
        rcases hcover P with ⟨i', hi', huni, -⟩ | ⟨e, -, -, hnot⟩
        · have := huni i hi
          subst this
          exact huni
        · exact absurd hi (hnot i)
      rw [Finset.sum_eq_single i (fun j _ hji => if_neg (fun hj => hji (huniq j hj))) (fun h => absurd (Finset.mem_univ i) h),
        if_pos hi]
  by_cases hn : n = 0
  ·
    subst hn
    have hE : IsEmpty (Place L F) := ⟨fun P => by
      rcases hcover P with ⟨i, -⟩ | ⟨e, -⟩
      · exact i.elim0
      · exact (src e).elim0⟩
    have htop : riemannRochSpace D = ⊤ := by
      ext f; simp only [Submodule.mem_top, iff_true]; intro v; exact hE.elim v
    have hnotfin : ¬ Module.Finite L F := by
      intro hfin
      haveI := hfin
      have : Algebra.IsAlgebraic L F := Algebra.IsIntegral.isAlgebraic
      exact (Algebra.transcendental_iff_not_isAlgebraic.1 (algebra_transcendental L F)) this
    have hR : Module.finrank L (riemannRochSpace D) = 0 := by
      rw [htop, finrank_top]; exact Module.finrank_of_not_finite hnotfin
    have hL : Module.finrank (IsLocalRing.ResidueField A) (LinearMap.ker Ψ) = 0 := by
      haveI : Subsingleton (∀ i, LSpace (Dbar i)) := inferInstance
      exact Module.finrank_zero_of_subsingleton
    rw [hR, hL]
  ·
    have hcard : ∑ i, ((C i).nodes.card : ℤ) = 2 * m := by

      let Φ : Fin m ⊕ Fin m → Σ i, ↥(C i).nodes := Sum.elim (fun e => ⟨src e, ⟨xs e, hsrc e⟩⟩) (fun e => ⟨tgt e, ⟨xt e, htgt e⟩⟩)
      have hΦ : Function.Bijective Φ := by
        constructor
        · intro E E' hEE'
          apply hnodes.2 (Φ E).1 (Φ E).2.1 (Φ E).2.2
          · rcases E with e | e <;> rfl
          · rw [hEE']
            rcases E' with e' | e' <;> rfl
        · rintro ⟨i, x⟩
          obtain ⟨e, he | he⟩ := hnodes.1 i x.1 x.2
          · refine ⟨Sum.inl e, ?_⟩
            obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.1 he
            subst h1
            simp only [heq_eq_eq] at h2
            simp only [Φ, Sum.elim_inl]
            congr 1
            exact Subtype.ext h2
          · refine ⟨Sum.inr e, ?_⟩
            obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.1 he
            subst h1
            simp only [heq_eq_eq] at h2
            simp only [Φ, Sum.elim_inr]
            congr 1
            exact Subtype.ext h2
      have := Fintype.card_congr (Equiv.ofBijective Φ hΦ)
      rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_sigma] at this
      simp only [Fintype.card_coe] at this
      push_cast
      rw [← Nat.cast_sum]
      omega
    have hdegF : 2 * (genusFF L F : ℤ) - 1 ≤ D.degree := by
      rw [← hdegsum]
      have h1 : ∑ i, (2 * (genusFF (IsLocalRing.ResidueField A) (Fbar i) : ℤ) - 1 + ((C i).nodes.card : ℤ)) ≤ ∑ i, (Dbar i).degree :=
        Finset.sum_le_sum fun i _ => hdegD i
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one, hcard, ← Finset.mul_sum] at h1
      have hn1 : (1 : ℤ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
      have hg := hgenus
      zify at hg
      push_cast at hg h1 ⊢
      nlinarith
    have hRRF := riemannRoch L F D hdegF
    haveI := finiteDimensional_lSpace L F D hdegF
    have hker : (Module.finrank (IsLocalRing.ResidueField A) (LinearMap.ker Ψ) : ℤ) = Module.finrank (IsLocalRing.ResidueField A) (∀ i, LSpace (Dbar i)) - m := by
      have : (m : ℤ) + Module.finrank (IsLocalRing.ResidueField A) (LinearMap.ker Ψ) = Module.finrank (IsLocalRing.ResidueField A) (∀ i, LSpace (Dbar i)) := by exact_mod_cast hrn
      omega
    have hW0' : (Module.finrank (IsLocalRing.ResidueField A) (∀ i, LSpace (Dbar i)) : ℤ) = ∑ i, ((Dbar i).degree + 1 - genusFF (IsLocalRing.ResidueField A) (Fbar i)) := by
      rw [hW0]; push_cast
      exact Finset.sum_congr rfl fun i _ => (E2 i).2.1
    have key : (Module.finrank (IsLocalRing.ResidueField A) (LinearMap.ker Ψ) : ℤ) = Module.finrank L (riemannRochSpace D) := by
      rw [hker, hW0', show (Module.finrank L (riemannRochSpace D) : ℤ) = (ell D : ℤ) from rfl, hRRF,
        Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_one, hdegsum]
      have hg := hgenus
      zify at hg
      push_cast at hg ⊢
      linarith
    exact_mod_cast key

end S_AlgebraicCurve_SemistableCovering_finiteDimensional_and_finrank_glued_riemannRochSpace_eq_finrank_of_rankOne
end P2MW
export P2MW.S_AlgebraicCurve_SemistableCovering_finiteDimensional_and_finrank_glued_riemannRochSpace_eq_finrank_of_rankOne (solution)
