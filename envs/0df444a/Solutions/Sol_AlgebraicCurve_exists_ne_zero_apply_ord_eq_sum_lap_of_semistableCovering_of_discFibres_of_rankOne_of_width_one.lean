-- Prove2me | solution 1 for AlgebraicCurve.exists_ne_zero_apply_ord_eq_sum_lap_of_semistableCovering_of_discFibres_of_rankOne_of_width_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/5acb3136-2514-502a-8d68-135e426b6681

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_AlgebraicCurve_SemistableCovering_exists_forall_residue_smul_eq_of_forall_ord_ge_of_forall_evalAt_mul_eq_of_width_one
import Theorems.Thm_AlgebraicCurve_SemistableCovering_forall_ord_eq_zero_and_sum_eq_lap_of_ord_residue_smul_eq_of_width_one
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Theorems.Thm_AlgebraicCurve_ell_eq_degree_add_one_sub_genusFF_of_isAlgClosed_of_isSeparable
import Theorems.Thm_AlgebraicCurve_degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental
import Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_ord_smul_of_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_ne_zero_apply_ord_eq_sum_lap_of_semistableCovering_of_discFibres_of_rankOne_of_width_one
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.Gamma0Pair.isElliptic AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply"
p2m_attr_erase "simp" "ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open AlgebraicCurve IsLocalRing

namespace AF8PotentialViaLift

section Eval

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

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

theorem evalAt_zero' (v : Place K E) : v.evalAt (0 : E) = 0 := by
  rw [← map_zero (algebraMap K E), AlgebraicCurve.Place.evalAt_algebraMap]

end Eval

section MapDomain

theorem mapDomain_apply_eq_sum {α β : Type*} [DecidableEq β] (φ : α → β) (D : α →₀ ℤ) (b : β) :
    Finsupp.mapDomain φ D b = ∑ a ∈ D.support, if φ a = b then D a else 0 := by
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  show (Finsupp.single (φ a) (D a)) b = _
  rw [Finsupp.single_apply]

end MapDomain

end AF8PotentialViaLift

namespace AF8PotentialViaLift

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

theorem evalAt_add' (v : Place K F) (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring)
    (hg : g ∈ v.toValuationSubring) : v.evalAt (f + g) = v.evalAt f + v.evalAt g :=
  AF8PotentialViaLift.evalAt_add v hv hf hg

theorem evalAt_smul' (v : Place K F) (hv : v.IsRational) (c : K) {f : F} (hf : f ∈ v.toValuationSubring) :
    v.evalAt (c • f) = c * v.evalAt f :=
  AF8PotentialViaLift.evalAt_smul v hv c hf

theorem isUnit_mk_of_ord_eq_zero' (v : Place K F) {f : F} (hf : f ≠ 0) (h : v.ord f = 0)
    (hmem : f ∈ v.toValuationSubring) : IsUnit (⟨f, hmem⟩ : v.toValuationSubring) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hϖ
  rw [h, zpow_zero, mul_one] at hu
  have : (⟨f, hmem⟩ : v.toValuationSubring) = (u : v.toValuationSubring) := Subtype.ext hu
  rw [this]; exact u.isUnit

theorem evalAt_eq_zero_iff (v : Place K F) (hv : v.IsRational) {f : F} (hf0 : f ≠ 0)
    (hf : f ∈ v.toValuationSubring) : v.evalAt f = 0 ↔ 1 ≤ v.ord f := by
  have h0 : 0 ≤ v.ord f := (Place.mem_iff_ord_nonneg v hf0).mp hf
  constructor
  · intro h
    by_contra hlt
    have hz : v.ord f = 0 := by omega
    have hu := isUnit_mk_of_ord_eq_zero' v hf0 hz hf
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

end RR

end AF8PotentialViaLift

open AF8PotentialViaLift in
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
    :
    let V := Fin n ⊕ (Σ e : Fin m, Fin (w e - 1))
    let ends : (Σ e : Fin m, Fin (w e)) → V × V := fun ε =>
      (if h0 : ε.2.1 = 0 then Sum.inl (src ε.1)
        else Sum.inr ⟨ε.1, ⟨ε.2.1 - 1, by have := ε.2.2; omega⟩⟩,
       if h1 : ε.2.1 + 1 = w ε.1 then Sum.inl (tgt ε.1)
        else Sum.inr ⟨ε.1, ⟨ε.2.1, by have := ε.2.2; omega⟩⟩)
    let lap : V → (V → ℤ) := fun v => ∑ ε : Σ e : Fin m, Fin (w e),
      ((if (ends ε).1 = v then (Pi.single v 1 : V → ℤ) - (Pi.single (ends ε).2 1 : V → ℤ) else 0) +
       (if (ends ε).2 = v then (Pi.single v 1 : V → ℤ) - (Pi.single (ends ε).1 1 : V → ℤ) else 0))
    ∀ μ : Divisor L F →+ (V → ℤ),
      (∀ i, ∀ P ∈ (C i).dom, μ (Finsupp.single P 1) = Pi.single (Sum.inl i) 1) →
      (∀ e, ∀ P ∈ (An e).dom, ∀ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
        (⟨P.evalAt (An e).param, h⟩ : A) = u * π ^ d → ∀ (hd0 : 0 < d) (hdw : d < w e),
          μ (Finsupp.single P 1) = Pi.single (Sum.inr ⟨e, ⟨d - 1, by omega⟩⟩) 1) →
      (∀ e, ∀ P ∈ (An e).dom,
        (¬ ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
          (⟨P.evalAt (An e).param, h⟩ : A) = u * π ^ d) → μ (Finsupp.single P 1) = 0) →
      ∀ c : V → ℤ, ∃ (g : F) (Dg : Divisor L F), g ≠ 0 ∧ (∀ P, Dg P = P.ord g) ∧
        (∀ P ∈ Dg.support, (∃ i, P ∈ (C i).dom) ∨
          ∃ e, P ∈ (An e).dom ∧ ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
            (⟨P.evalAt (An e).param, h⟩ : A) = u * π ^ d) ∧
        μ Dg = ∑ u, c u • lap u := by
  intro V ends lap μ hμC hμA hμN c
  classical
  haveI hκ : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A

  set φ : Fin n → ℤ := fun i => c (Sum.inl i) with hφ
  set k : Fin m → ℤ := fun e => φ (tgt e) - φ (src e) with hk_def
  have hk : ∀ e, k e = φ (tgt e) - φ (src e) := fun e => rfl
  set wt : Fin n → L := fun i => (((π : A) : L) ^ (φ i))⁻¹ with hwt_def
  have hwt : ∀ i, wt i = (((π : A) : L) ^ (φ i))⁻¹ := fun i => rfl
  set zs : ∀ e, Fbar (src e) := fun e => (C (src e)).residue ⟨(An e).param, (hatt e).1.2.choose⟩ with hzs_def
  set zt : ∀ e, Fbar (tgt e) := fun e => (C (tgt e)).residue ⟨(An' e).param, (hatt e).2.2.choose⟩ with hzt_def
  set ubar : Fin m → ResidueField A := fun e => IsLocalRing.residue A ((hw e).choose : A) with hubar_def
  have hπL : ((π : A) : L) ≠ 0 := fun h0 => hπ0 (Subtype.ext h0)
  have hwt0 : ∀ i, wt i ≠ 0 := fun i => by rw [hwt]; exact inv_ne_zero (zpow_ne_zero _ hπL)
  have hordzs : ∀ e, (xs e).ord (zs e) = 1 := fun e => (hatt e).1.2.choose_spec.1
  have hordzt : ∀ e, (xt e).ord (zt e) = 1 := fun e => (hatt e).2.2.choose_spec.1
  have hzs0 : ∀ e, zs e ≠ 0 := fun e h0 => by
    have := hordzs e; rw [h0, Place.ord_zero] at this; exact zero_ne_one this
  have hzt0 : ∀ e, zt e ≠ 0 := fun e h0 => by
    have := hordzt e; rw [h0, Place.ord_zero] at this; exact zero_ne_one this
  have hubar0 : ∀ e, ubar e ≠ 0 := by
    intro e
    show IsLocalRing.residue A ((hw e).choose : A) ≠ 0
    exact (residue_ne_zero_iff_isUnit _).mpr (Units.isUnit (hw e).choose)

  have hend_src : ∀ e e', (⟨src e', xs e'⟩ : Σ j, Place (ResidueField A) (Fbar j)) = ⟨src e, xs e⟩ → e' = e := by
    intro e e' he
    have := hnodes.2 (src e) (xs e) (hatt e).1.1 (Sum.inl e') (Sum.inl e) he rfl
    exact Sum.inl_injective this
  have hend_tgt : ∀ e e', (⟨tgt e', xt e'⟩ : Σ j, Place (ResidueField A) (Fbar j)) = ⟨tgt e, xt e⟩ → e' = e := by
    intro e e' he
    have := hnodes.2 (tgt e) (xt e) (hatt e).2.1 (Sum.inr e') (Sum.inr e) he rfl
    exact Sum.inr_injective this
  have hend_mix : ∀ e e', (⟨src e', xs e'⟩ : Σ j, Place (ResidueField A) (Fbar j)) ≠ ⟨tgt e, xt e⟩ := by
    intro e e' he
    have := hnodes.2 (tgt e) (xt e) (hatt e).2.1 (Sum.inl e') (Sum.inr e) he rfl
    exact Sum.inl_ne_inr this
  have hend_mix' : ∀ e e', (⟨tgt e', xt e'⟩ : Σ j, Place (ResidueField A) (Fbar j)) ≠ ⟨src e, xs e⟩ := by
    intro e e' he
    have := hnodes.2 (src e) (xs e) (hatt e).1.1 (Sum.inr e') (Sum.inl e) he rfl
    exact Sum.inr_ne_inl this

  have dom_unique : ∀ {v : Place L F} {i j : Fin n}, v ∈ (C i).dom → v ∈ (C j).dom → j = i := by
    intro v i j hi hj
    rcases hcover v with ⟨l, -, huniq, -⟩ | ⟨e, -, -, hnot⟩
    · rw [huniq i hi, huniq j hj]
    · exact absurd hi (hnot i)
  have ann_not_dom : ∀ {v : Place L F} (e : Fin m), v ∈ (An e).dom → ∀ i, v ∉ (C i).dom := by
    intro v e he i hi
    rcases hcover v with ⟨j, -, -, hno⟩ | ⟨e', -, -, hnot⟩
    · exact hno e he
    · exact hnot i hi
  have hfib : ∀ i, ∀ Q : Place (ResidueField A) (Fbar i), Q ∉ (C i).nodes →
      ∃ P ∈ (C i).dom, (C i).placeMap P = Q := by
    intro i Q hQ
    obtain ⟨T, hT, -, -, -, huniq⟩ := hdisc i Q hQ
    obtain ⟨P, ⟨hP1, hP2, -⟩, -⟩ := huniq 0 (Ideal.zero_mem _)
    exact ⟨P, hP1, hP2⟩
  haveI hinf : ∀ i, Infinite (Place (ResidueField A) (Fbar i)) := fun i => infinite_place

  set lapφ : Fin n → ℤ := fun i =>
    ∑ e, ((if src e = i then φ i - φ (tgt e) else 0) + (if tgt e = i then φ i - φ (src e) else 0)) with hlapφ_def
  have hlapφ : ∀ i, lapφ i =
      ∑ e, ((if src e = i then φ i - φ (tgt e) else 0) + (if tgt e = i then φ i - φ (src e) else 0)) := fun i => rfl

  have hQP : ∀ i, ∃ (Q : Place (ResidueField A) (Fbar i)) (P : Place L F),
      Q ∉ (C i).nodes ∧ P ∈ (C i).dom ∧ (C i).placeMap P = Q := by
    intro i
    obtain ⟨Q, hQ⟩ := Infinite.exists_notMem_finset (C i).nodes
    obtain ⟨P, hP, hPQ⟩ := hfib i Q hQ
    exact ⟨Q, P, hQ, hP, hPQ⟩
  choose Qc Pc hQc hPc hPQc using hQP
  set N : Fin n → ℕ := fun i =>
    (2 * (genusFF (ResidueField A) (Fbar i) : ℤ) - 1 + ((C i).nodes.card : ℤ) - lapφ i).toNat with hN_def
  have hN : ∀ i, 2 * (genusFF (ResidueField A) (Fbar i) : ℤ) - 1 + ((C i).nodes.card : ℤ) - lapφ i ≤ (N i : ℤ) :=
    fun i => Int.self_le_toNat _
  set D : Divisor L F := ∑ i, Finsupp.single (Pc i) (N i : ℤ) with hD_def
  have hD_apply : ∀ v, D v = ∑ i, if Pc i = v then (N i : ℤ) else 0 := by
    intro v; rw [hD_def, Finsupp.finsetSum_apply]
    apply Finset.sum_congr rfl; intro i _; rw [Finsupp.single_apply]
  have hD_filter : ∀ i, D.filter (fun P => P ∈ (C i).dom) = Finsupp.single (Pc i) (N i : ℤ) := by
    intro i
    ext v
    by_cases hv : v ∈ (C i).dom
    · rw [Finsupp.filter_apply_pos _ _ hv, hD_apply, Finsupp.single_apply]
      rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
      intro j _ hji
      rw [if_neg]
      intro hjv
      exact hji (dom_unique hv (hjv ▸ hPc j))
    · rw [Finsupp.filter_apply_neg _ _ hv, Finsupp.single_apply, if_neg]
      intro h; exact hv (h ▸ hPc i)
  have hDbar : ∀ i, (Finsupp.mapDomain (C i).placeMap (D.filter fun P => P ∈ (C i).dom) :
      Divisor (ResidueField A) (Fbar i)) = Finsupp.single (Qc i) (N i : ℤ) := by
    intro i; rw [hD_filter, Finsupp.mapDomain_single, hPQc]
  have hD_supp : ∀ P ∈ D.support, ∃ i, P ∈ (C i).dom := by
    intro P hP
    have hne : D P ≠ 0 := Finsupp.mem_support_iff.mp hP
    rw [hD_apply] at hne
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    refine ⟨i, ?_⟩
    by_cases h : Pc i = P
    · exact h ▸ hPc i
    · rw [if_neg h] at hi; exact absurd rfl hi
  have hD_nonneg : ∀ v, 0 ≤ D v := by
    intro v; rw [hD_apply]
    exact Finset.sum_nonneg fun i _ => by split_ifs <;> simp
  have hD_ann : ∀ e, ∀ v ∈ (An e).dom, D v = 0 := by
    intro e v hv
    by_contra hne
    obtain ⟨i, hi⟩ := hD_supp v (Finsupp.mem_support_iff.mpr hne)
    exact ann_not_dom e hv i hi
  have hdegD : ∀ i, 2 * (genusFF (ResidueField A) (Fbar i) : ℤ) - 1 + ((C i).nodes.card : ℤ) ≤
      Divisor.degree (Finsupp.mapDomain (C i).placeMap (D.filter fun P => P ∈ (C i).dom) :
        Divisor (ResidueField A) (Fbar i)) +
      ∑ e, ((if src e = i then φ i - φ (tgt e) else 0) + (if tgt e = i then φ i - φ (src e) else 0)) := by
    intro i
    rw [hDbar, degree_single_eq, ← hlapφ]
    have := hN i
    linarith
  set Dbar : ∀ i, Divisor (ResidueField A) (Fbar i) := fun i =>
    Finsupp.mapDomain (C i).placeMap (D.filter fun P => P ∈ (C i).dom) with hDbar_def
  have hDbar_eq : ∀ i, Dbar i = Finsupp.single (Qc i) (N i : ℤ) := fun i => hDbar i
  have hDbar_nonneg : ∀ i Q, 0 ≤ Dbar i Q := by
    intro i Q; rw [hDbar_eq, Finsupp.single_apply]; split_ifs <;> simp
  have hDbar_node : ∀ i, ∀ x ∈ (C i).nodes, Dbar i x = 0 := by
    intro i x hx
    rw [hDbar_eq, Finsupp.single_apply, if_neg]
    intro h; exact hQc i (h ▸ hx)

  have hONTO : ∀ h : ∀ i, Fbar i,
      (∀ i, ∀ Q, Q ∉ (C i).nodes → h i ≠ 0 → 0 ≤ Q.ord (h i) + Dbar i Q) →
      (∀ e, h (src e) ≠ 0 → k e ≤ (xs e).ord (h (src e))) →
      (∀ e, h (tgt e) ≠ 0 → -k e ≤ (xt e).ord (h (tgt e))) →
      (∀ e, (xs e).evalAt (h (src e) * zs e ^ (-k e)) * ubar e ^ (k e) = (xt e).evalAt (h (tgt e) * zt e ^ (k e))) →
      ∃ (g : F) (hg : ∀ i, wt i • g ∈ (C i).integers), (g = 0 ∨ ∀ P, 0 ≤ P.ord g + D P) ∧
        ∀ i, (C i).residue ⟨wt i • g, hg i⟩ = h i := by
    have hT1 :=
      AlgebraicCurve.SemistableCovering.exists_forall_residue_smul_eq_of_forall_ord_ge_of_forall_evalAt_mul_eq_of_width_one
        A π hπ hπ0 hrk F n m Fbar hratBar C hratF An An' src tgt xs xt w hpair hw hw1 hatt hnodes hcover hdisc hgenus
        φ D hD_supp hdegD
    exact hT1.2
  have hEXACT : ∀ (g : F) (hg : ∀ i, wt i • g ∈ (C i).integers),
      (∀ i, (C i).residue ⟨wt i • g, hg i⟩ ≠ 0) →
      (∀ e, ∀ P ∈ (An e).dom, 0 ≤ P.ord g) →
      (∀ e, (xs e).ord ((C (src e)).residue ⟨wt (src e) • g, hg (src e)⟩) = k e) →
      (∀ e, (xt e).ord ((C (tgt e)).residue ⟨wt (tgt e) • g, hg (tgt e)⟩) = -k e) →
      (∀ e, ∀ P ∈ (An e).dom, P.ord g = 0) ∧
      (∀ i (Dg : Divisor L F), (∀ P ∈ (C i).dom, Dg P = P.ord g) → (∀ P, P ∉ (C i).dom → Dg P = 0) →
        (Dg.sum fun _ l => l) = lapφ i) := by
    have hEX :=
      AlgebraicCurve.SemistableCovering.forall_ord_eq_zero_and_sum_eq_lap_of_ord_residue_smul_eq_of_width_one
        A π hπ hπ0 hrk F n m Fbar hratBar C hratF An An' src tgt xs xt w hpair hw hw1 hatt hnodes hcover hdisc hgenus φ
    exact hEX

  let β : ∀ i, Place (ResidueField A) (Fbar i) → ℤ := fun i x =>
    ∑ e, ((if (⟨src e, xs e⟩ : Σ j, Place (ResidueField A) (Fbar j)) = ⟨i, x⟩ then -k e else 0) +
      (if (⟨tgt e, xt e⟩ : Σ j, Place (ResidueField A) (Fbar j)) = ⟨i, x⟩ then k e else 0))
  have hβ_def : ∀ i x, β i x =
      ∑ e, ((if (⟨src e, xs e⟩ : Σ j, Place (ResidueField A) (Fbar j)) = ⟨i, x⟩ then -k e else 0) +
        (if (⟨tgt e, xt e⟩ : Σ j, Place (ResidueField A) (Fbar j)) = ⟨i, x⟩ then k e else 0)) := fun _ _ => rfl
  have hβ_src : ∀ e, β (src e) (xs e) = -k e := by
    intro e
    rw [hβ_def, Finset.sum_add_distrib, Finset.sum_eq_single_of_mem e (Finset.mem_univ e), if_pos rfl,
      Finset.sum_eq_zero, add_zero]
    · intro e' _; rw [if_neg (hend_mix' e e')]
    · intro e' _ hne; rw [if_neg]; exact fun he => hne (hend_src e e' he)
  have hβ_tgt : ∀ e, β (tgt e) (xt e) = k e := by
    intro e
    rw [hβ_def, Finset.sum_add_distrib, Finset.sum_eq_zero, zero_add,
      Finset.sum_eq_single_of_mem e (Finset.mem_univ e), if_pos rfl]
    · intro e' _ hne; rw [if_neg]; exact fun he => hne (hend_tgt e e' he)
    · intro e' _; rw [if_neg (hend_mix e e')]
  have hβ_sum : ∀ i, ∑ x ∈ (C i).nodes, β i x = lapφ i := by
    intro i
    simp_rw [hβ_def]
    rw [Finset.sum_comm, hlapφ]
    apply Finset.sum_congr rfl
    intro e _
    rw [Finset.sum_add_distrib]
    congr 1
    · by_cases hi : src e = i
      · subst hi
        rw [if_pos rfl, Finset.sum_eq_single_of_mem (xs e) (hatt e).1.1, if_pos rfl, hk]
        · ring
        · intro x _ hx
          rw [if_neg]
          intro heq
          apply hx
          obtain ⟨-, h2⟩ := Sigma.mk.inj_iff.mp heq
          exact (eq_of_heq h2).symm
      · rw [if_neg hi]
        apply Finset.sum_eq_zero
        intro x _
        rw [if_neg]
        intro heq
        exact hi (Sigma.mk.inj_iff.mp heq).1
    · by_cases hi : tgt e = i
      · subst hi
        rw [if_pos rfl, Finset.sum_eq_single_of_mem (xt e) (hatt e).2.1, if_pos rfl, hk]
        intro x _ hx
        rw [if_neg]
        intro heq
        apply hx
        obtain ⟨-, h2⟩ := Sigma.mk.inj_iff.mp heq
        exact (eq_of_heq h2).symm
      · rw [if_neg hi]
        apply Finset.sum_eq_zero
        intro x _
        rw [if_neg]
        intro heq
        exact hi (Sigma.mk.inj_iff.mp heq).1
  set E : ∀ i, Divisor (ResidueField A) (Fbar i) := fun i =>
    Dbar i + ∑ x ∈ (C i).nodes, Finsupp.single x (β i x) with hE
  have hK_apply : ∀ i y, (∑ x ∈ (C i).nodes, Finsupp.single x (β i x) : Divisor (ResidueField A) (Fbar i)) y =
      if y ∈ (C i).nodes then β i y else 0 := by
    intro i y
    rw [Finsupp.finsetSum_apply]
    split_ifs with hy
    · rw [Finset.sum_eq_single_of_mem y hy]
      · simp
      · intro b _ hb; simp [hb]
    · apply Finset.sum_eq_zero
      intro x hx
      have : x ≠ y := fun hxy => hy (hxy ▸ hx)
      simp [this]
  have hE_node : ∀ i, ∀ x ∈ (C i).nodes, E i x = β i x := by
    intro i x hx
    rw [hE]; dsimp only; rw [Finsupp.add_apply, hDbar_node i x hx, hK_apply, if_pos hx, zero_add]
  have hE_off : ∀ i x, x ∉ (C i).nodes → E i x = Dbar i x := by
    intro i x hx
    rw [hE]; dsimp only; rw [Finsupp.add_apply, hK_apply, if_neg hx, add_zero]
  have hE_src : ∀ e, E (src e) (xs e) = -k e := fun e => by rw [hE_node _ _ (hatt e).1.1, hβ_src]
  have hE_tgt : ∀ e, E (tgt e) (xt e) = k e := fun e => by rw [hE_node _ _ (hatt e).2.1, hβ_tgt]
  have hE_deg : ∀ i, (E i).degree = (Dbar i).degree + lapφ i := by
    intro i
    rw [hE]; dsimp only; rw [map_add, map_sum, ← hβ_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    exact degree_single_eq x _
  have hE_deg_ge : ∀ i, 2 * (genusFF (ResidueField A) (Fbar i) : ℤ) - 1 + ((C i).nodes.card : ℤ) ≤ (E i).degree := by
    intro i
    have := hdegD i
    rw [← hlapφ] at this
    rw [hE_deg]; exact this

  have hE_nonneg_of_empty : ∀ i, (C i).nodes = ∅ → ∀ Q, 0 ≤ E i Q := by
    intro i hi Q
    rw [hE_off i Q (by rw [hi]; exact Finset.notMem_empty Q)]
    exact hDbar_nonneg i Q

  have hregS : ∀ e (t : Fbar (src e)), t ∈ LSpace (E (src e)) → t * zs e ^ (-k e) ∈ (xs e).toValuationSubring := by
    intro e t ht
    rcases eq_or_ne t 0 with rfl | ht0
    · rw [zero_mul]; exact zero_mem _
    rw [Place.mem_iff_ord_nonneg _ (mul_ne_zero ht0 (zpow_ne_zero _ (hzs0 e))),
      Place.ord_mul _ ht0 (zpow_ne_zero _ (hzs0 e)), Place.ord_zpow, hordzs]
    have := ord_ge_of_mem_lSpace ht ht0 (xs e)
    rw [hE_src] at this
    omega
  have hregT : ∀ e (t : Fbar (tgt e)), t ∈ LSpace (E (tgt e)) → t * zt e ^ (k e) ∈ (xt e).toValuationSubring := by
    intro e t ht
    rcases eq_or_ne t 0 with rfl | ht0
    · rw [zero_mul]; exact zero_mem _
    rw [Place.mem_iff_ord_nonneg _ (mul_ne_zero ht0 (zpow_ne_zero _ (hzt0 e))),
      Place.ord_mul _ ht0 (zpow_ne_zero _ (hzt0 e)), Place.ord_zpow, hordzt]
    have := ord_ge_of_mem_lSpace ht ht0 (xt e)
    rw [hE_tgt] at this
    omega

  have hRR : ∀ (i : Fin n) (x₀ : Place (ResidueField A) (Fbar i)), x₀ ∈ (C i).nodes →
      ∃ σ : Fbar i, σ ≠ 0 ∧ σ ∈ LSpace (E i) ∧ x₀.ord σ = -(E i x₀) ∧
        ∀ x ∈ (C i).nodes, x ≠ x₀ → -(E i x) + 1 ≤ x.ord σ := by
    intro a x₀ hx₀N
    set N' := (C a).nodes with hN'
    set E' : Divisor (ResidueField A) (Fbar a) := E a - ∑ x ∈ N'.erase x₀, Finsupp.single x 1 with hE'
    have hsum_apply : ∀ (T : Finset (Place (ResidueField A) (Fbar a))) y,
        (∑ x ∈ T, Finsupp.single x (1 : ℤ) : Divisor (ResidueField A) (Fbar a)) y = if y ∈ T then 1 else 0 := by
      intro T y
      rw [Finsupp.finsetSum_apply]
      split_ifs with hy
      · rw [Finset.sum_eq_single_of_mem y hy]
        · simp
        · intro b _ hb; simp [hb]
      · apply Finset.sum_eq_zero
        intro x hx
        have : x ≠ y := fun hxy => hy (hxy ▸ hx)
        simp [this]
    have hE'_apply : ∀ y, E' y = E a y - if y ∈ N'.erase x₀ then 1 else 0 := by
      intro y; rw [hE', Finsupp.sub_apply, hsum_apply]
    have hE'x₀ : E' x₀ = E a x₀ := by
      rw [hE'_apply, if_neg (Finset.notMem_erase x₀ N'), sub_zero]
    have hdegsum : ∀ (T : Finset (Place (ResidueField A) (Fbar a))),
        Divisor.degree (∑ x ∈ T, Finsupp.single x (1 : ℤ) : Divisor (ResidueField A) (Fbar a)) = T.card := by
      intro T
      rw [map_sum]; simp_rw [degree_single_eq]; simp
    have hEa_deg := hE_deg_ge a
    have hE'_deg : E'.degree = (E a).degree - (N'.card - 1 : ℕ) := by
      rw [hE', map_sub, hdegsum, Finset.card_erase_of_mem hx₀N]
    have hcardpos : 1 ≤ N'.card := Finset.card_pos.mpr ⟨x₀, hx₀N⟩
    have hE'_deg' : 2 * (genusFF (ResidueField A) (Fbar a) : ℤ) ≤ E'.degree := by
      rw [hE'_deg]; push_cast [hcardpos]; linarith
    have hE'x_deg : (E' - Finsupp.single x₀ 1).degree = E'.degree - 1 := by
      rw [map_sub, degree_single_eq]
    have hell1 := ell_eq E' (by linarith)
    have hell2 := ell_eq (E' - Finsupp.single x₀ 1) (by rw [hE'x_deg]; linarith)
    have hlt : LSpace (E' - Finsupp.single x₀ 1) < LSpace E' := by
      refine lt_of_le_of_ne (lSpace_mono ?_) ?_
      · intro y
        rw [Finsupp.sub_apply, Finsupp.single_apply]
        split_ifs <;> omega
      · intro heq
        have : (ell (E' - Finsupp.single x₀ 1) : ℤ) = ell E' := by
          unfold ell; rw [heq]
        rw [hell1, hell2, hE'x_deg] at this
        linarith
    obtain ⟨σ, hσE', hσnot⟩ := SetLike.exists_of_lt hlt
    have hσ0 : σ ≠ 0 := by rintro rfl; exact hσnot (Submodule.zero_mem _)
    have hσE : σ ∈ LSpace (E a) := lSpace_mono (fun y => by
      rw [hE'_apply]; split_ifs <;> omega) hσE'
    have hσx₀ : x₀.ord σ = -(E a x₀) := by
      have hge := ord_ge_of_mem_lSpace hσE' hσ0 x₀
      rw [hE'x₀] at hge
      by_contra hne
      apply hσnot
      rw [mem_lSpace_iff_ord]
      refine Or.inr fun y => ?_
      rw [Finsupp.sub_apply, Finsupp.single_apply]
      by_cases hy : x₀ = y
      · subst hy; rw [if_pos rfl, hE'x₀]; omega
      · rw [if_neg hy, sub_zero]; exact ord_ge_of_mem_lSpace hσE' hσ0 y
    have hσx : ∀ x ∈ N', x ≠ x₀ → -(E a x) + 1 ≤ x.ord σ := by
      intro x hx hxx
      have := ord_ge_of_mem_lSpace hσE' hσ0 x
      rw [hE'_apply, if_pos (Finset.mem_erase.mpr ⟨hxx, hx⟩)] at this
      omega
    exact ⟨σ, hσ0, hσE, hσx₀, hσx⟩

  have hRRs : ∀ e, ∃ σ : Fbar (src e), σ ≠ 0 ∧ σ ∈ LSpace (E (src e)) ∧ (xs e).ord σ = k e ∧
      ∀ x ∈ (C (src e)).nodes, x ≠ xs e → -(E (src e) x) + 1 ≤ x.ord σ := by
    intro e
    obtain ⟨σ, h0, h1, h2, h3⟩ := hRR (src e) (xs e) (hatt e).1.1
    exact ⟨σ, h0, h1, by rw [h2, hE_src, neg_neg], h3⟩
  have hRRt : ∀ e, ∃ σ : Fbar (tgt e), σ ≠ 0 ∧ σ ∈ LSpace (E (tgt e)) ∧ (xt e).ord σ = -k e ∧
      ∀ x ∈ (C (tgt e)).nodes, x ≠ xt e → -(E (tgt e) x) + 1 ≤ x.ord σ := by
    intro e
    obtain ⟨σ, h0, h1, h2, h3⟩ := hRR (tgt e) (xt e) (hatt e).2.1
    exact ⟨σ, h0, h1, by rw [h2, hE_tgt], h3⟩
  choose σs hσs0 hσsE hσs_ord hσs_other using hRRs
  choose σt hσt0 hσtE hσt_ord hσt_other using hRRt

  set cs : ∀ e, ResidueField A := fun e => (xs e).evalAt (σs e * zs e ^ (-k e)) with hcs
  set ct : ∀ e, ResidueField A := fun e => (xt e).evalAt (σt e * zt e ^ (k e)) with hct
  have hcs0 : ∀ e, cs e ≠ 0 := by
    intro e
    have hprod0 : σs e * zs e ^ (-k e) ≠ 0 := mul_ne_zero (hσs0 e) (zpow_ne_zero _ (hzs0 e))
    have hord : (xs e).ord (σs e * zs e ^ (-k e)) = 0 := by
      rw [Place.ord_mul _ (hσs0 e) (zpow_ne_zero _ (hzs0 e)), Place.ord_zpow, hσs_ord, hordzs]; ring
    intro h0
    have := (evalAt_eq_zero_iff (xs e) (hratBar _ _) hprod0 (hregS e _ (hσsE e))).mp h0
    omega
  have hct0 : ∀ e, ct e ≠ 0 := by
    intro e
    have hprod0 : σt e * zt e ^ (k e) ≠ 0 := mul_ne_zero (hσt0 e) (zpow_ne_zero _ (hzt0 e))
    have hord : (xt e).ord (σt e * zt e ^ (k e)) = 0 := by
      rw [Place.ord_mul _ (hσt0 e) (zpow_ne_zero _ (hzt0 e)), Place.ord_zpow, hσt_ord, hordzt]; ring
    intro h0
    have := (evalAt_eq_zero_iff (xt e) (hratBar _ _) hprod0 (hregT e _ (hσtE e))).mp h0
    omega

  set as_ : Fin m → ResidueField A := fun e => ubar e ^ (-k e) * (cs e)⁻¹ with has_
  set at_ : Fin m → ResidueField A := fun e => (ct e)⁻¹ with hat_
  have has0 : ∀ e, as_ e ≠ 0 := fun e => mul_ne_zero (zpow_ne_zero _ (hubar0 e)) (inv_ne_zero (hcs0 e))
  have hat0 : ∀ e, at_ e ≠ 0 := fun e => inv_ne_zero (hct0 e)
  set h₀ : ∀ i, Fbar i := fun i => if (C i).nodes = ∅ then 1 else 0 with hh₀
  set h : ∀ i, Fbar i := h₀ + ∑ e, ((Pi.single (src e) (as_ e • σs e) : ∀ i, Fbar i) +
      (Pi.single (tgt e) (at_ e • σt e) : ∀ i, Fbar i)) with hh

  have hsingle_mem : ∀ (j : Fin n) (y : Fbar j), y ∈ LSpace (E j) → ∀ i, (Pi.single j y : ∀ i, Fbar i) i ∈ LSpace (E i) := by
    intro j y hy i
    by_cases hij : i = j
    · subst hij; rw [Pi.single_eq_same]; exact hy
    · rw [Pi.single_eq_of_ne hij]; exact Submodule.zero_mem _
  have hh₀_mem : ∀ i, h₀ i ∈ LSpace (E i) := by
    intro i
    show (if (C i).nodes = ∅ then (1 : Fbar i) else 0) ∈ LSpace (E i)
    split_ifs with hi
    · rw [mem_lSpace_iff_ord]
      refine Or.inr fun Q => ?_
      rw [Place.ord_one]; have := hE_nonneg_of_empty i hi Q; omega
    · exact Submodule.zero_mem _
  have hh_mem : ∀ i, h i ∈ LSpace (E i) := by
    intro i
    rw [hh, Pi.add_apply, Finset.sum_apply]
    refine Submodule.add_mem _ (hh₀_mem i) (Submodule.sum_mem _ fun e _ => ?_)
    rw [Pi.add_apply]
    exact Submodule.add_mem _ (hsingle_mem _ _ (Submodule.smul_mem _ _ (hσsE e)) i)
      (hsingle_mem _ _ (Submodule.smul_mem _ _ (hσtE e)) i)

  have hvan : ∀ (j : Fin n) (x₀ : Place (ResidueField A) (Fbar j)) (y : Fbar j),
      (∀ x ∈ (C j).nodes, x ≠ x₀ → y ≠ 0 → -(E j x) + 1 ≤ x.ord y) →
      ∀ (i : Fin n) (x : Place (ResidueField A) (Fbar i)) (τ : Fbar i), x ∈ (C i).nodes →
        (⟨i, x⟩ : Σ l, Place (ResidueField A) (Fbar l)) ≠ ⟨j, x₀⟩ → τ ≠ 0 → x.ord τ = E i x →
        x.evalAt ((Pi.single j y : ∀ i, Fbar i) i * τ) = 0 := by
    intro j x₀ y hy i x τ hx hne hτ hordτ
    by_cases hij : i = j
    · subst hij
      have hxx : x ≠ x₀ := fun hxx => hne (by rw [hxx])
      rw [Pi.single_eq_same]
      rcases eq_or_ne y 0 with rfl | hy0
      · rw [zero_mul, evalAt_zero']
      have hprod0 : y * τ ≠ 0 := mul_ne_zero hy0 hτ
      have hord : 1 ≤ x.ord (y * τ) := by
        rw [Place.ord_mul _ hy0 hτ, hordτ]; have := hy x hx hxx hy0; omega
      have hmem : y * τ ∈ x.toValuationSubring := by
        rw [Place.mem_iff_ord_nonneg _ hprod0]; omega
      exact (evalAt_eq_zero_iff x (hratBar _ _) hprod0 hmem).mpr hord
    · rw [Pi.single_eq_of_ne hij, zero_mul, evalAt_zero']
  have hbound_s : ∀ e, ∀ x ∈ (C (src e)).nodes, x ≠ xs e → as_ e • σs e ≠ 0 → -(E (src e) x) + 1 ≤ x.ord (as_ e • σs e) :=
    fun e x hx hxx _ => by rw [Place.ord_smul_of_ne_zero _ (has0 e)]; exact hσs_other e x hx hxx
  have hbound_t : ∀ e, ∀ x ∈ (C (tgt e)).nodes, x ≠ xt e → at_ e • σt e ≠ 0 → -(E (tgt e) x) + 1 ≤ x.ord (at_ e • σt e) :=
    fun e x hx hxx _ => by rw [Place.ord_smul_of_ne_zero _ (hat0 e)]; exact hσt_other e x hx hxx

  set CS : Fin m → (∀ i, Fbar i) → ResidueField A := fun e t => (xs e).evalAt (t (src e) * zs e ^ (-k e)) with hCS
  set CT : Fin m → (∀ i, Fbar i) → ResidueField A := fun e t => (xt e).evalAt (t (tgt e) * zt e ^ (k e)) with hCT
  have hCS_add : ∀ e (t t' : ∀ i, Fbar i), (∀ i, t i ∈ LSpace (E i)) → (∀ i, t' i ∈ LSpace (E i)) →
      CS e (t + t') = CS e t + CS e t' := by
    intro e t t' ht ht'
    show (xs e).evalAt ((t + t') (src e) * zs e ^ (-k e)) =
      (xs e).evalAt (t (src e) * zs e ^ (-k e)) + (xs e).evalAt (t' (src e) * zs e ^ (-k e))
    rw [Pi.add_apply, add_mul, evalAt_add' _ (hratBar _ _) (hregS e _ (ht _)) (hregS e _ (ht' _))]
  have hCT_add : ∀ e (t t' : ∀ i, Fbar i), (∀ i, t i ∈ LSpace (E i)) → (∀ i, t' i ∈ LSpace (E i)) →
      CT e (t + t') = CT e t + CT e t' := by
    intro e t t' ht ht'
    show (xt e).evalAt ((t + t') (tgt e) * zt e ^ (k e)) =
      (xt e).evalAt (t (tgt e) * zt e ^ (k e)) + (xt e).evalAt (t' (tgt e) * zt e ^ (k e))
    rw [Pi.add_apply, add_mul, evalAt_add' _ (hratBar _ _) (hregT e _ (ht _)) (hregT e _ (ht' _))]
  have hCS_sum : ∀ e (s : Finset (Fin m)) (t : Fin m → ∀ i, Fbar i), (∀ e' i, t e' i ∈ LSpace (E i)) →
      CS e (∑ e' ∈ s, t e') = ∑ e' ∈ s, CS e (t e') := by
    intro e s t ht
    induction s using Finset.induction_on with
    | empty =>
      show (xs e).evalAt ((∑ e' ∈ (∅ : Finset (Fin m)), t e') (src e) * zs e ^ (-k e)) = _
      rw [Finset.sum_empty, Finset.sum_empty, Pi.zero_apply, zero_mul, evalAt_zero']
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, hCS_add e _ _ (ht a)
        (fun i => by rw [Finset.sum_apply]; exact Submodule.sum_mem _ fun e' _ => ht e' i), ih]
  have hCT_sum : ∀ e (s : Finset (Fin m)) (t : Fin m → ∀ i, Fbar i), (∀ e' i, t e' i ∈ LSpace (E i)) →
      CT e (∑ e' ∈ s, t e') = ∑ e' ∈ s, CT e (t e') := by
    intro e s t ht
    induction s using Finset.induction_on with
    | empty =>
      show (xt e).evalAt ((∑ e' ∈ (∅ : Finset (Fin m)), t e') (tgt e) * zt e ^ (k e)) = _
      rw [Finset.sum_empty, Finset.sum_empty, Pi.zero_apply, zero_mul, evalAt_zero']
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, hCT_add e _ _ (ht a)
        (fun i => by rw [Finset.sum_apply]; exact Submodule.sum_mem _ fun e' _ => ht e' i), ih]

  set trm : Fin m → ∀ i, Fbar i := fun e => (Pi.single (src e) (as_ e • σs e) : ∀ i, Fbar i) +
      (Pi.single (tgt e) (at_ e • σt e) : ∀ i, Fbar i) with htrm
  have htrm_mem : ∀ e i, trm e i ∈ LSpace (E i) := by
    intro e i
    rw [htrm]; dsimp only; rw [Pi.add_apply]
    exact Submodule.add_mem _ (hsingle_mem _ _ (Submodule.smul_mem _ _ (hσsE e)) i)
      (hsingle_mem _ _ (Submodule.smul_mem _ _ (hσtE e)) i)
  have hh_eq : h = h₀ + ∑ e, trm e := rfl

  have hh₀_src : ∀ e, h₀ (src e) = 0 := by
    intro e
    show (if (C (src e)).nodes = ∅ then (1 : Fbar (src e)) else 0) = 0
    rw [if_neg]; exact Finset.ne_empty_of_mem (hatt e).1.1
  have hh₀_tgt : ∀ e, h₀ (tgt e) = 0 := by
    intro e
    show (if (C (tgt e)).nodes = ∅ then (1 : Fbar (tgt e)) else 0) = 0
    rw [if_neg]; exact Finset.ne_empty_of_mem (hatt e).2.1

  have hCS_trm : ∀ e e', CS e (trm e') = if e' = e then ubar e ^ (-k e) else 0 := by
    intro e e'
    have hmem1 : ∀ i, (Pi.single (src e') (as_ e' • σs e') : ∀ i, Fbar i) i ∈ LSpace (E i) :=
      hsingle_mem _ _ (Submodule.smul_mem _ _ (hσsE e'))
    have hmem2 : ∀ i, (Pi.single (tgt e') (at_ e' • σt e') : ∀ i, Fbar i) i ∈ LSpace (E i) :=
      hsingle_mem _ _ (Submodule.smul_mem _ _ (hσtE e'))
    rw [htrm]; dsimp only; rw [hCS_add e _ _ hmem1 hmem2]
    have h2 : CS e (Pi.single (tgt e') (at_ e' • σt e')) = 0 :=
      hvan (tgt e') (xt e') _ (hbound_t e') (src e) (xs e) (zs e ^ (-k e)) (hatt e).1.1
        (Ne.symm (hend_mix' e e')) (zpow_ne_zero _ (hzs0 e)) (by rw [Place.ord_zpow, hordzs, hE_src, mul_one])
    rw [h2, add_zero]
    by_cases hee : e' = e
    · subst hee
      rw [if_pos rfl]
      show (xs e').evalAt ((Pi.single (src e') (as_ e' • σs e') : ∀ i, Fbar i) (src e') * zs e' ^ (-k e')) = _
      rw [Pi.single_eq_same, smul_mul_assoc, evalAt_smul' _ (hratBar _ _) _ (hregS e' _ (hσsE e'))]
      show ubar e' ^ (-k e') * (cs e')⁻¹ * cs e' = ubar e' ^ (-k e')
      rw [inv_mul_cancel_right₀ (hcs0 e')]
    · rw [if_neg hee]
      exact hvan (src e') (xs e') _ (hbound_s e') (src e) (xs e) (zs e ^ (-k e)) (hatt e).1.1
        (fun heq => hee (hend_src e e' heq.symm)) (zpow_ne_zero _ (hzs0 e))
        (by rw [Place.ord_zpow, hordzs, hE_src, mul_one])
  have hCT_trm : ∀ e e', CT e (trm e') = if e' = e then 1 else 0 := by
    intro e e'
    have hmem1 : ∀ i, (Pi.single (src e') (as_ e' • σs e') : ∀ i, Fbar i) i ∈ LSpace (E i) :=
      hsingle_mem _ _ (Submodule.smul_mem _ _ (hσsE e'))
    have hmem2 : ∀ i, (Pi.single (tgt e') (at_ e' • σt e') : ∀ i, Fbar i) i ∈ LSpace (E i) :=
      hsingle_mem _ _ (Submodule.smul_mem _ _ (hσtE e'))
    rw [htrm]; dsimp only; rw [hCT_add e _ _ hmem1 hmem2]
    have h1 : CT e (Pi.single (src e') (as_ e' • σs e')) = 0 :=
      hvan (src e') (xs e') _ (hbound_s e') (tgt e) (xt e) (zt e ^ (k e)) (hatt e).2.1
        (Ne.symm (hend_mix e e')) (zpow_ne_zero _ (hzt0 e)) (by rw [Place.ord_zpow, hordzt, hE_tgt, mul_one])
    rw [h1, zero_add]
    by_cases hee : e' = e
    · subst hee
      rw [if_pos rfl]
      show (xt e').evalAt ((Pi.single (tgt e') (at_ e' • σt e') : ∀ i, Fbar i) (tgt e') * zt e' ^ (k e')) = _
      rw [Pi.single_eq_same, smul_mul_assoc, evalAt_smul' _ (hratBar _ _) _ (hregT e' _ (hσtE e'))]
      show (ct e')⁻¹ * ct e' = 1
      rw [inv_mul_cancel₀ (hct0 e')]
    · rw [if_neg hee]
      exact hvan (tgt e') (xt e') _ (hbound_t e') (tgt e) (xt e) (zt e ^ (k e)) (hatt e).2.1
        (fun heq => hee (hend_tgt e e' heq.symm)) (zpow_ne_zero _ (hzt0 e))
        (by rw [Place.ord_zpow, hordzt, hE_tgt, mul_one])
  have hCS_h : ∀ e, CS e h = ubar e ^ (-k e) := by
    intro e
    rw [hh_eq, hCS_add e _ _ hh₀_mem (fun i => by rw [Finset.sum_apply]; exact Submodule.sum_mem _ fun e' _ => htrm_mem e' i),
      hCS_sum e _ _ htrm_mem]
    have h0 : CS e h₀ = 0 := by
      show (xs e).evalAt (h₀ (src e) * zs e ^ (-k e)) = 0
      rw [hh₀_src, zero_mul, evalAt_zero']
    rw [h0, zero_add, Finset.sum_congr rfl (fun e' _ => hCS_trm e e'), Finset.sum_ite_eq' Finset.univ e]
    simp
  have hCT_h : ∀ e, CT e h = 1 := by
    intro e
    rw [hh_eq, hCT_add e _ _ hh₀_mem (fun i => by rw [Finset.sum_apply]; exact Submodule.sum_mem _ fun e' _ => htrm_mem e' i),
      hCT_sum e _ _ htrm_mem]
    have h0 : CT e h₀ = 0 := by
      show (xt e).evalAt (h₀ (tgt e) * zt e ^ (k e)) = 0
      rw [hh₀_tgt, zero_mul, evalAt_zero']
    rw [h0, zero_add, Finset.sum_congr rfl (fun e' _ => hCT_trm e e'), Finset.sum_ite_eq' Finset.univ e]
    simp

  have hh_src_ord : ∀ e, h (src e) ≠ 0 ∧ (xs e).ord (h (src e)) = k e := by
    intro e
    have hval : (xs e).evalAt (h (src e) * zs e ^ (-k e)) ≠ 0 := by
      show CS e h ≠ 0
      rw [hCS_h]; exact zpow_ne_zero _ (hubar0 e)
    have hh0 : h (src e) ≠ 0 := by
      intro h0; apply hval; rw [h0, zero_mul, evalAt_zero']
    refine ⟨hh0, ?_⟩
    have hprod0 : h (src e) * zs e ^ (-k e) ≠ 0 := mul_ne_zero hh0 (zpow_ne_zero _ (hzs0 e))
    have hmem := hregS e _ (hh_mem (src e))
    have h0 : (xs e).ord (h (src e) * zs e ^ (-k e)) = 0 := by
      have hge : 0 ≤ (xs e).ord (h (src e) * zs e ^ (-k e)) := (Place.mem_iff_ord_nonneg _ hprod0).mp hmem
      have hlt : ¬ 1 ≤ (xs e).ord (h (src e) * zs e ^ (-k e)) := fun h1 =>
        hval ((evalAt_eq_zero_iff (xs e) (hratBar _ _) hprod0 hmem).mpr h1)
      omega
    rw [Place.ord_mul _ hh0 (zpow_ne_zero _ (hzs0 e)), Place.ord_zpow, hordzs] at h0
    omega
  have hh_tgt_ord : ∀ e, h (tgt e) ≠ 0 ∧ (xt e).ord (h (tgt e)) = -k e := by
    intro e
    have hval : (xt e).evalAt (h (tgt e) * zt e ^ (k e)) ≠ 0 := by
      show CT e h ≠ 0
      rw [hCT_h]; exact one_ne_zero
    have hh0 : h (tgt e) ≠ 0 := by
      intro h0; apply hval; rw [h0, zero_mul, evalAt_zero']
    refine ⟨hh0, ?_⟩
    have hprod0 : h (tgt e) * zt e ^ (k e) ≠ 0 := mul_ne_zero hh0 (zpow_ne_zero _ (hzt0 e))
    have hmem := hregT e _ (hh_mem (tgt e))
    have h0 : (xt e).ord (h (tgt e) * zt e ^ (k e)) = 0 := by
      have hge : 0 ≤ (xt e).ord (h (tgt e) * zt e ^ (k e)) := (Place.mem_iff_ord_nonneg _ hprod0).mp hmem
      have hlt : ¬ 1 ≤ (xt e).ord (h (tgt e) * zt e ^ (k e)) := fun h1 =>
        hval ((evalAt_eq_zero_iff (xt e) (hratBar _ _) hprod0 hmem).mpr h1)
      omega
    rw [Place.ord_mul _ hh0 (zpow_ne_zero _ (hzt0 e)), Place.ord_zpow, hordzt] at h0
    omega
  have hh_ne : ∀ i, h i ≠ 0 := by
    intro i
    by_cases hi : (C i).nodes = ∅
    ·
      have hsum0 : (∑ e, trm e) i = 0 := by
        rw [Finset.sum_apply]
        apply Finset.sum_eq_zero
        intro e _
        rw [htrm]; dsimp only; rw [Pi.add_apply, Pi.single_eq_of_ne, Pi.single_eq_of_ne, add_zero]
        · intro h'; apply Finset.ne_empty_of_mem (hatt e).2.1; rw [← h']; exact hi
        · intro h'; apply Finset.ne_empty_of_mem (hatt e).1.1; rw [← h']; exact hi
      rw [hh_eq, Pi.add_apply, hsum0, add_zero]
      show (if (C i).nodes = ∅ then (1 : Fbar i) else 0) ≠ 0
      rw [if_pos hi]; exact one_ne_zero
    · obtain ⟨x, hx⟩ := Finset.nonempty_of_ne_empty hi
      obtain ⟨e, he | he⟩ := hnodes.1 i x hx
      · obtain ⟨h1, -⟩ := Sigma.mk.inj_iff.mp he
        subst h1; exact (hh_src_ord e).1
      · obtain ⟨h1, -⟩ := Sigma.mk.inj_iff.mp he
        subst h1; exact (hh_tgt_ord e).1

  obtain ⟨g, hg, hgD, hres⟩ := hONTO h
    (fun i Q hQ hi0 => by
      have := ord_ge_of_mem_lSpace (hh_mem i) hi0 Q
      rw [hE_off i Q hQ] at this; omega)
    (fun e _ => by rw [(hh_src_ord e).2])
    (fun e _ => by rw [(hh_tgt_ord e).2])
    (fun e => by
      show CS e h * ubar e ^ (k e) = CT e h
      rw [hCS_h, hCT_h, ← zpow_add₀ (hubar0 e), neg_add_cancel, zpow_zero])
  have hres_ne : ∀ i, (C i).residue ⟨wt i • g, hg i⟩ ≠ 0 := fun i => by rw [hres i]; exact hh_ne i
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  ·
    subst hn0
    refine ⟨1, 0, one_ne_zero, fun P => by simp [Place.ord_one], fun P hP => by simp at hP, ?_⟩
    rw [map_zero]
    symm
    funext v
    rcases v with i | ⟨e, d⟩
    · exact i.elim0
    · exact (src e).elim0
  haveI : Nonempty (Fin n) := ⟨⟨0, hnpos⟩⟩
  have hg0 : g ≠ 0 := by
    intro h0
    apply hres_ne (Classical.arbitrary (Fin n))
    have : (⟨wt _ • g, hg (Classical.arbitrary (Fin n))⟩ : (C (Classical.arbitrary (Fin n))).integers) = 0 :=
      Subtype.ext (by simp [h0])
    rw [this, map_zero]
  have hgD' : ∀ P, 0 ≤ P.ord g + D P := by
    rcases hgD with h0 | h1
    · exact absurd h0 hg0
    · exact h1
  have hreg : ∀ e, ∀ P ∈ (An e).dom, 0 ≤ P.ord g := by
    intro e P hP
    have := hgD' P
    rw [hD_ann e P hP] at this; omega
  obtain ⟨hann, hdeg⟩ := hEXACT g hg hres_ne hreg
    (fun e => by rw [hres]; exact (hh_src_ord e).2) (fun e => by rw [hres]; exact (hh_tgt_ord e).2)

  obtain ⟨Dg, hDg, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) g hg0
  have hDg_chart : ∀ P ∈ Dg.support, ∃ i, P ∈ (C i).dom := by
    intro P hP
    have hne : P.ord g ≠ 0 := by rw [← hDg P]; exact Finsupp.mem_support_iff.mp hP
    rcases hcover P with ⟨i, hi, -, -⟩ | ⟨e, he, -, -⟩
    · exact ⟨i, hi⟩
    · exact absurd (hann e P he) hne
  refine ⟨g, Dg, hg0, hDg, fun P hP => Or.inl (hDg_chart P hP), ?_⟩

  have hDg_split : Dg = ∑ i, Dg.filter fun P => P ∈ (C i).dom := by
    ext v
    rw [Finsupp.finsetSum_apply]
    by_cases hv : ∃ i, v ∈ (C i).dom
    · obtain ⟨i, hi⟩ := hv
      rw [Finset.sum_eq_single i]
      · rw [Finsupp.filter_apply_pos _ _ hi]
      · intro j _ hji
        rw [Finsupp.filter_apply_neg]
        intro hj
        exact hji (dom_unique hi hj)
      · intro hh'; exact absurd (Finset.mem_univ i) hh'
    · push Not at hv
      have hD0 : Dg v = 0 := by
        by_contra hne
        obtain ⟨i, hi⟩ := hDg_chart v (Finsupp.mem_support_iff.mpr hne)
        exact hv i hi
      rw [hD0]
      symm
      apply Finset.sum_eq_zero
      intro i _
      rw [Finsupp.filter_apply_neg _ _ (hv i)]
  have hμ_chart : ∀ i, μ (Dg.filter fun P => P ∈ (C i).dom) = (lapφ i) • (Pi.single (Sum.inl i) 1 : V → ℤ) := by
    intro i
    set G := Dg.filter fun P => P ∈ (C i).dom with hG
    have hGsupp : ∀ P ∈ G.support, P ∈ (C i).dom := by
      intro P hP
      rw [hG, Finsupp.support_filter, Finset.mem_filter] at hP
      exact hP.2
    have h1 : μ G = G.sum fun P l => l • μ (Finsupp.single P 1) := by
      conv_lhs => rw [← Finsupp.sum_single G]
      rw [map_finsuppSum]
      apply Finsupp.sum_congr
      intro P _
      rw [← Finsupp.smul_single_one, map_zsmul]
    rw [h1]
    have h2 : (G.sum fun P l => l • μ (Finsupp.single P 1)) = G.sum fun _ l => l • (Pi.single (Sum.inl i) 1 : V → ℤ) := by
      apply Finsupp.sum_congr
      intro P hP
      rw [hμC i P (hGsupp P hP)]
    rw [h2, Finsupp.sum, ← Finset.sum_smul]
    congr 1
    have h3 : (G.sum fun _ l => l) = lapφ i := hdeg i G
      (fun P hP => by rw [hG, Finsupp.filter_apply_pos _ _ hP, hDg P])
      (fun P hP => by rw [hG, Finsupp.filter_apply_neg _ _ hP])
    exact h3
  have hμDg : μ Dg = ∑ i, (lapφ i) • (Pi.single (Sum.inl i) 1 : V → ℤ) := by
    conv_lhs => rw [hDg_split]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => hμ_chart i
  rw [hμDg]

  have hends : ∀ ε : Σ e : Fin m, Fin (w e), ends ε = (Sum.inl (src ε.1), Sum.inl (tgt ε.1)) := by
    intro ε
    have h0 : ε.2.1 = 0 := by have := ε.2.2; have := hw1 ε.1; omega
    have h1 : ε.2.1 + 1 = w ε.1 := by have := hw1 ε.1; omega
    simp only [ends]
    rw [dif_pos h0, dif_pos h1]
  have hlap : ∀ v, lap v = ∑ e : Fin m,
      ((if Sum.inl (src e) = v then (Pi.single v 1 : V → ℤ) - Pi.single (Sum.inl (tgt e)) 1 else 0) +
       (if Sum.inl (tgt e) = v then (Pi.single v 1 : V → ℤ) - Pi.single (Sum.inl (src e)) 1 else 0)) := by
    intro v
    simp only [lap]
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro e _
    have hcard : (Finset.univ : Finset (Fin (w e))).card = 1 := by rw [Finset.card_univ, Fintype.card_fin, hw1]
    have hterm : ∀ j : Fin (w e),
        ((if (ends ⟨e, j⟩).1 = v then (Pi.single v 1 : V → ℤ) - Pi.single (ends ⟨e, j⟩).2 1 else 0) +
          (if (ends ⟨e, j⟩).2 = v then (Pi.single v 1 : V → ℤ) - Pi.single (ends ⟨e, j⟩).1 1 else 0)) =
        ((if Sum.inl (src e) = v then (Pi.single v 1 : V → ℤ) - Pi.single (Sum.inl (tgt e)) 1 else 0) +
          (if Sum.inl (tgt e) = v then (Pi.single v 1 : V → ℤ) - Pi.single (Sum.inl (src e)) 1 else 0)) := by
      intro j; rw [hends ⟨e, j⟩]
    rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_const, hcard, one_smul]

  have hRHS : ∑ u, c u • lap u = ∑ e : Fin m,
      ((c (Sum.inl (src e)) - c (Sum.inl (tgt e))) • (Pi.single (Sum.inl (src e)) 1 : V → ℤ) +
        (c (Sum.inl (tgt e)) - c (Sum.inl (src e))) • (Pi.single (Sum.inl (tgt e)) 1 : V → ℤ)) := by
    simp_rw [hlap, Finset.smul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    simp_rw [smul_add]
    rw [Finset.sum_add_distrib]
    have h1 : ∑ u, c u • (if Sum.inl (src e) = u then (Pi.single u 1 : V → ℤ) - Pi.single (Sum.inl (tgt e)) 1 else 0) =
        c (Sum.inl (src e)) • ((Pi.single (Sum.inl (src e)) 1 : V → ℤ) - Pi.single (Sum.inl (tgt e)) 1) := by
      rw [Finset.sum_eq_single_of_mem (Sum.inl (src e) : V) (Finset.mem_univ _), if_pos rfl]
      intro u _ hu; rw [if_neg (Ne.symm hu), smul_zero]
    have h2 : ∑ u, c u • (if Sum.inl (tgt e) = u then (Pi.single u 1 : V → ℤ) - Pi.single (Sum.inl (src e)) 1 else 0) =
        c (Sum.inl (tgt e)) • ((Pi.single (Sum.inl (tgt e)) 1 : V → ℤ) - Pi.single (Sum.inl (src e)) 1) := by
      rw [Finset.sum_eq_single_of_mem (Sum.inl (tgt e) : V) (Finset.mem_univ _), if_pos rfl]
      intro u _ hu; rw [if_neg (Ne.symm hu), smul_zero]
    rw [h1, h2]
    module

  have hLHS : ∑ i, (lapφ i) • (Pi.single (Sum.inl i) 1 : V → ℤ) = ∑ e : Fin m,
      ((φ (src e) - φ (tgt e)) • (Pi.single (Sum.inl (src e)) 1 : V → ℤ) +
        (φ (tgt e) - φ (src e)) • (Pi.single (Sum.inl (tgt e)) 1 : V → ℤ)) := by
    simp_rw [hlapφ, Finset.sum_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    simp_rw [add_smul]
    rw [Finset.sum_add_distrib]
    have h1 : ∑ i, (if src e = i then φ i - φ (tgt e) else 0) • (Pi.single (Sum.inl i) 1 : V → ℤ) =
        (φ (src e) - φ (tgt e)) • (Pi.single (Sum.inl (src e)) 1 : V → ℤ) := by
      rw [Finset.sum_eq_single_of_mem (src e) (Finset.mem_univ _), if_pos rfl]
      intro i _ hi; rw [if_neg (Ne.symm hi), zero_smul]
    have h2 : ∑ i, (if tgt e = i then φ i - φ (src e) else 0) • (Pi.single (Sum.inl i) 1 : V → ℤ) =
        (φ (tgt e) - φ (src e)) • (Pi.single (Sum.inl (tgt e)) 1 : V → ℤ) := by
      rw [Finset.sum_eq_single_of_mem (tgt e) (Finset.mem_univ _), if_pos rfl]
      intro i _ hi; rw [if_neg (Ne.symm hi), zero_smul]
    rw [h1, h2]
  rw [hLHS, hRHS]

end
end S_AlgebraicCurve_exists_ne_zero_apply_ord_eq_sum_lap_of_semistableCovering_of_discFibres_of_rankOne_of_width_one
end P2MW
export P2MW.S_AlgebraicCurve_exists_ne_zero_apply_ord_eq_sum_lap_of_semistableCovering_of_discFibres_of_rankOne_of_width_one (solution)
