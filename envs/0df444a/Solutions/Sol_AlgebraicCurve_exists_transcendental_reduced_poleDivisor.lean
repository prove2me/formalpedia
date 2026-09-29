-- Prove2me | solution 1 for AlgebraicCurve.exists_transcendental_reduced_poleDivisor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/efdfa696-7277-540d-8c2c-065358ae19d2

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_exists_separating_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_ell_eq_degree_add_one_sub_genusFF_of_isAlgClosed_of_isSeparable
import Theorems.Thm_AlgebraicCurve_exists_poleDivisor_of_transcendental
import Theorems.Thm_AlgebraicCurve_exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental
import Theorems.Thm_AlgebraicCurve_degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_transcendental_reduced_poleDivisor
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_exists_transcendental_reduced_poleDivisor.AlgebraicCurve Polynomial"

universe u v

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor Divisor.degree Divisor.degree_single genusFF LSpace ell mem_lSpace_iff_ord one_mem_lSpace_zero IsCurveOver IsCurveOver.deg_eq_one_of_isAlgClosed ConstantReduction ConstantReduction.ord_algebraMap isCurveOver_of_isAlgClosed_of_transcendental exists_separating_transcendental_of_perfectField ell_eq_degree_add_one_sub_genusFF_of_isAlgClosed_of_isSeparable exists_poleDivisor_of_transcendental exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental finiteDimensional_adjoin_of_transcendental degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental"
namespace ReducedPoleDivisor
p2m_open "AlgebraicCurve"

variable {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]

theorem ord_pos_iff (v : Place K F) {f : F} (hf : f ≠ 0) : 0 < v.ord f ↔ v.adicValuation f < 1 := by
  rw [v.adicValuation_eq_exp_neg_ord hf, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  omega

theorem exists_eq_algebraMap_of_isAlgebraic [IsAlgClosed K] {x : F} (hx : IsAlgebraic K x) :
    ∃ c : K, x = algebraMap K F c := by
  have hint : IsIntegral K x := hx.isIntegral
  have hdeg : (minpoly K x).degree = 1 := IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hint)
  have hmonic := minpoly.monic hint
  have hform : minpoly K x = X + C ((minpoly K x).coeff 0) := by
    rw [Polynomial.eq_X_add_C_of_degree_le_one hdeg.le]
    have hlc : (minpoly K x).coeff 1 = 1 := by
      have := hmonic.leadingCoeff
      rwa [Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_degree_eq_some hdeg] at this
    rw [hlc, C_1, one_mul]
    simp
  have h0 := minpoly.aeval K x
  rw [hform] at h0
  simp only [map_add, aeval_X, aeval_C] at h0
  exact ⟨-(minpoly K x).coeff 0, by rw [map_neg]; exact eq_neg_of_add_eq_zero_left h0⟩

end AlgebraicCurve.ReducedPoleDivisor

open AlgebraicCurve.ReducedPoleDivisor in
theorem solution
    (K : Type u) (F : Type v) [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (hF : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (m : ℕ) (hm : 2 * genusFF K F + 1 ≤ m) :
    ∃ (x : F) (P : Fin m → Place K F),
      Function.Injective P ∧ Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F ∧
      Module.finrank (IntermediateField.adjoin K ({x} : Set F)) F = m ∧
      (∀ j, (P j).ord x = -1) ∧
      (∀ v : Place K F, v ∉ Set.range P → 0 ≤ v.ord x) := by
  classical
  obtain ⟨x₀, hx₀, hfd₀⟩ := hF
  haveI := hfd₀
  haveI : IsCurveOver K F := isCurveOver_of_isAlgClosed_of_transcendental x₀ hx₀
  haveI : PerfectField K := IsAlgClosed.perfectField K
  set g : ℕ := genusFF K F with hg

  obtain ⟨t, ht, hfint, hsept⟩ := exists_separating_transcendental_of_perfectField hx₀ hfd₀
  have hRR : ∀ D : Divisor K F, 2 * (g : ℤ) - 1 ≤ D.degree → (ell D : ℤ) = D.degree + 1 - g :=
    fun D hD => ell_eq_degree_add_one_sub_genusFF_of_isAlgClosed_of_isSeparable K t ht hfint hsept D hD
  haveI := hfint
  obtain ⟨Dt, hDt⟩ := exists_poleDivisor_of_transcendental t ht
  obtain ⟨hell0, -⟩ := exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental t ht Dt hDt

  have hL0 : ∀ f : F, f ∈ LSpace (0 : Divisor K F) → ∃ c : K, f = algebraMap K F c := by
    intro f hf
    haveI : Module.Finite K (LSpace (0 : Divisor K F)) := Module.finite_of_finrank_eq_succ hell0
    have hone : (1 : F) ∈ LSpace (0 : Divisor K F) := one_mem_lSpace_zero
    have hspan : Submodule.span K {(1 : F)} = LSpace (0 : Divisor K F) := by
      apply Submodule.eq_of_le_of_finrank_eq
      · rw [Submodule.span_le, Set.singleton_subset_iff]; exact hone
      · rw [finrank_span_singleton one_ne_zero]; exact hell0.symm
    have hf' : f ∈ Submodule.span K {(1 : F)} := by rw [hspan]; exact hf
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hf'
    exact ⟨c, by rw [← hc, Algebra.smul_def, mul_one]⟩
  have hordconst : ∀ (v : Place K F) (c : K), c ≠ 0 → v.ord (algebraMap K F c) = 0 :=
    fun v c hc => ConstantReduction.ord_algebraMap v hc

  have htconst : ∀ c : K, t ≠ algebraMap K F c := by
    intro c h
    apply ht
    rw [h]; exact isAlgebraic_algebraMap c

  have hzero : ∀ a : K, ∃ v : Place K F, 0 < v.ord (t - algebraMap K F a) := by
    intro a
    have hta : t - algebraMap K F a ≠ 0 := sub_ne_zero.mpr (htconst a)
    by_contra hall
    push Not at hall
    have hmem : (t - algebraMap K F a)⁻¹ ∈ LSpace (0 : Divisor K F) := by
      rw [mem_lSpace_iff_ord]
      right
      intro v
      rw [Finsupp.coe_zero, Pi.zero_apply, neg_zero, v.ord_inv]
      have := hall v
      omega
    obtain ⟨c, hc⟩ := hL0 _ hmem
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [map_zero, inv_eq_zero] at hc
      exact hta hc
    apply htconst (a + c⁻¹)
    have : t - algebraMap K F a = algebraMap K F c⁻¹ := by
      rw [map_inv₀, ← hc, inv_inv]
    rw [map_add, ← this]; ring
  choose Pl hPl using hzero
  have hPlinj : Function.Injective Pl := by
    intro a b hab
    by_contra hne
    set v := Pl a
    have h1 : 0 < v.ord (t - algebraMap K F a) := hPl a
    have h2 : 0 < v.ord (t - algebraMap K F b) := by rw [show v = Pl b from hab]; exact hPl b
    have hta : t - algebraMap K F a ≠ 0 := sub_ne_zero.mpr (htconst a)
    have htb : t - algebraMap K F b ≠ 0 := sub_ne_zero.mpr (htconst b)
    rw [ord_pos_iff v hta] at h1
    rw [ord_pos_iff v htb] at h2
    have hba : algebraMap K F (b - a) = (t - algebraMap K F a) - (t - algebraMap K F b) := by
      rw [map_sub]; ring
    have hlt : v.adicValuation (algebraMap K F (b - a)) < 1 := by
      rw [hba]
      exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt h1 h2)
    have hne' : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have h0 : v.ord (algebraMap K F (b - a)) = 0 := hordconst v _ hne'
    have := (ord_pos_iff v ((_root_.map_ne_zero _).mpr hne')).mpr hlt
    omega

  let P : Fin m → Place K F := fun j => Pl (Infinite.natEmbedding K j)
  have hPinj : Function.Injective P := fun i j h =>
    Fin.ext ((Infinite.natEmbedding K).injective (hPlinj h))
  have hdeg1 : ∀ v : Place K F, (v.deg : ℤ) = 1 := fun v => by
    rw [IsCurveOver.deg_eq_one_of_isAlgClosed v]; rfl
  let D : Divisor K F := ∑ j, Finsupp.single (P j) 1
  have hDapply : ∀ v, D v = ∑ j, (Finsupp.single (P j) (1 : ℤ)) v := fun v =>
    Finsupp.finsetSum_apply _ _ v
  have hDP : ∀ j, D (P j) = 1 := by
    intro j
    rw [hDapply, Finset.sum_eq_single j]
    · exact Finsupp.single_eq_same
    · intro i _ hij
      exact Finsupp.single_eq_of_ne (fun h => hij (hPinj h).symm)
    · intro h; exact absurd (Finset.mem_univ j) h
  have hDout : ∀ v, v ∉ Set.range P → D v = 0 := by
    intro v hv
    rw [hDapply]
    refine Finset.sum_eq_zero fun j _ => Finsupp.single_eq_of_ne ?_
    rintro rfl
    exact hv ⟨j, rfl⟩
  have hDnn : ∀ v, 0 ≤ D v := by
    intro v
    by_cases hv : v ∈ Set.range P
    · obtain ⟨j, rfl⟩ := hv; rw [hDP]; exact zero_le_one
    · rw [hDout v hv]
  have hdegD : D.degree = m := by
    show Divisor.degree (∑ j, Finsupp.single (P j) 1) = m
    rw [map_sum]
    simp only [Divisor.degree_single, hdeg1, one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp

  let Dj : Fin m → Divisor K F := fun j => D - Finsupp.single (P j) 1
  have hDjP : ∀ j, Dj j (P j) = 0 := fun j => by
    show D (P j) - Finsupp.single (P j) (1 : ℤ) (P j) = 0
    rw [hDP, Finsupp.single_eq_same, sub_self]
  have hDjne : ∀ j v, v ≠ P j → Dj j v = D v := fun j v hv => by
    show D v - Finsupp.single (P j) (1 : ℤ) v = D v
    rw [Finsupp.single_apply, if_neg (Ne.symm hv), sub_zero]
  have hDjle : ∀ j, Dj j ≤ D := fun j v => by
    show D v - Finsupp.single (P j) (1 : ℤ) v ≤ D v
    have : 0 ≤ Finsupp.single (P j) (1 : ℤ) v := by
      rw [Finsupp.single_apply]
      split_ifs
      · exact zero_le_one
      · exact le_rfl
    omega
  have hdegDj : ∀ j, (Dj j).degree = m - 1 := fun j => by
    show Divisor.degree (D - Finsupp.single (P j) 1) = _
    rw [map_sub, hdegD, Divisor.degree_single, hdeg1, one_mul]

  have hmZ : 2 * (g : ℤ) + 1 ≤ m := by exact_mod_cast hm
  have hellD : (ell D : ℤ) = m + 1 - g := by
    rw [hRR D (by rw [hdegD]; omega), hdegD]
  have hellDj : ∀ j, (ell (Dj j) : ℤ) = m - g := fun j => by
    rw [hRR (Dj j) (by rw [hdegDj]; omega), hdegDj]; ring
  haveI hfinD : Module.Finite K (LSpace D) := by
    apply Module.finite_of_finrank_pos
    have : (0 : ℤ) < ell D := by rw [hellD]; omega
    exact_mod_cast this

  let p : Fin m → Submodule K (LSpace D) := fun j => (LSpace (Dj j)).comap (LSpace D).subtype
  have hp : ∀ j, p j ≠ ⊤ := by
    intro j htop
    have hle : LSpace D ≤ LSpace (Dj j) := by
      intro f hf
      have : (⟨f, hf⟩ : LSpace D) ∈ p j := by rw [htop]; exact Submodule.mem_top
      exact this
    have h1 : Module.finrank K (LSpace D) ≤ Module.finrank K (LSpace (Dj j)) := by
      haveI : Module.Finite K (LSpace (Dj j)) := by
        apply Module.finite_of_finrank_pos
        have : (0 : ℤ) < ell (Dj j) := by rw [hellDj]; omega
        exact_mod_cast this
      exact Submodule.finrank_mono hle
    have h2 : (ell D : ℤ) ≤ ell (Dj j) := by exact_mod_cast h1
    rw [hellD, hellDj] at h2
    omega
  obtain ⟨x', hx'⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
  set x : F := (x' : F) with hxdef
  have hxD : x ∈ LSpace D := x'.2
  have hxDj : ∀ j, x ∉ LSpace (Dj j) := fun j h => hx' j h

  have hx0 : x ≠ 0 := by
    intro h
    exact hxDj ⟨0, by omega⟩ (by rw [h]; exact Submodule.zero_mem _)
  have hordD : ∀ v, -D v ≤ v.ord x := fun v =>
    (((mem_lSpace_iff_ord).mp hxD).resolve_left hx0) v
  have hordout : ∀ v : Place K F, v ∉ Set.range P → 0 ≤ v.ord x := by
    intro v hv
    have := hordD v
    rw [hDout v hv, neg_zero] at this
    exact this
  have hordP : ∀ j, (P j).ord x = -1 := by
    intro j
    have hge : -1 ≤ (P j).ord x := by have := hordD (P j); rwa [hDP] at this
    have hnot := hxDj j
    rw [mem_lSpace_iff_ord, not_or, not_forall] at hnot
    obtain ⟨-, v, hv⟩ := hnot
    rw [not_le] at hv
    by_cases hvj : v = P j
    · subst hvj
      rw [hDjP, neg_zero] at hv
      omega
    · rw [hDjne j v hvj] at hv
      exact absurd (hordD v) (not_le.mpr hv)

  have hxtr : Transcendental K x := by
    intro halg
    obtain ⟨c, hc⟩ := exists_eq_algebraMap_of_isAlgebraic halg
    have hc0 : c ≠ 0 := by rintro rfl; rw [map_zero] at hc; exact hx0 hc
    have h1 := hordP ⟨0, by omega⟩
    rw [hc, hordconst _ c hc0] at h1
    omega

  have hfdx : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F :=
    finiteDimensional_adjoin_of_transcendental x₀ hxtr
  haveI := hfdx
  have hpole : ∀ v : Place K F, D v = max 0 (-v.ord x) := by
    intro v
    by_cases hv : v ∈ Set.range P
    · obtain ⟨j, rfl⟩ := hv
      rw [hDP, hordP]; rfl
    · rw [hDout v hv]
      have := hordout v hv
      rw [max_eq_left]; omega
  have hfinrank : Module.finrank (IntermediateField.adjoin K ({x} : Set F)) F = m := by
    have h := degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental x hxtr D hpole
    rw [hdegD] at h
    exact_mod_cast h.symm
  exact ⟨x, P, hPinj, hxtr, hfdx, hfinrank, hordP, hordout⟩

end S_AlgebraicCurve_exists_transcendental_reduced_poleDivisor
end P2MW
export P2MW.S_AlgebraicCurve_exists_transcendental_reduced_poleDivisor (solution)
