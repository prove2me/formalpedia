-- Prove2me | solution 1 for AlgebraicCurve.Place.isDedekindDomain_iInf_toSubring_and_isMaximal_iff_of_finset_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/cb07e136-e363-5ac5-89ce-8732ba892c47

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_AlgebraicCurve_ell_eq_degree_add_one_sub_genusFF_of_isAlgClosed_of_isSeparable
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Theorems.Thm_AlgebraicCurve_Place_isSeparable_adjoin_of_ord_eq_one
import Theorems.Thm_AlgebraicCurve_Place_eq_of_forall_coe_mem_nonunits_iff_of_isDedekindDomain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_isDedekindDomain_iInf_toSubring_and_isMaximal_iff_of_finset_nonempty
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

open IsLocalRing WithZero
open scoped IntermediateField

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "IsCurveOver IsCurveOver.deg_eq_one_of_isAlgClosed Place Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor genusFF LSpace ell mem_lSpace_iff_ord lSpace_mono ell_eq_degree_add_one_sub_genusFF_of_isAlgClosed_of_isSeparable IsCurveOver.exists_separating_transcendental Place.isSeparable_adjoin_of_ord_eq_one Place.eq_of_forall_coe_mem_nonunits_iff_of_isDedekindDomain"
p2m_open "AlgebraicCurve~isAlgebraic_adjoin_of_transcendental"

namespace HolomorphyRingAux

section Ord

variable {k K : Type*} [Field k] [Field K] [Algebra k K] (v : Place k K)

theorem ord_nonneg_of_mem {f : K} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  · exact ((v.adicValuation_le_one_iff).mp (v.adicValuation_le_one_of_mem hf)).resolve_left hf0

theorem not_mem_of_ord_neg {f : K} (hf : v.ord f < 0) : f ∉ v.toValuationSubring :=
  fun h => (ord_nonneg_of_mem v h).not_gt hf

theorem ord_algebraMap (a : k) : v.ord (algebraMap k K a) = 0 := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · have h1 := ord_nonneg_of_mem v (v.algebraMap_mem' a)
    have h2 := ord_nonneg_of_mem v (v.algebraMap_mem' a⁻¹)
    rw [map_inv₀, v.ord_inv] at h2
    omega

theorem mk_mem_maximalIdeal_iff {g : K} (hg : g ∈ v.toValuationSubring) :
    (⟨g, hg⟩ : v.toValuationSubring) ∈ maximalIdeal v.toValuationSubring ↔ g = 0 ∨ 0 < v.ord g := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rcases eq_or_ne g 0 with rfl | hg0
  · simp only [true_or, iff_true]
    intro hu
    exact hu.ne_zero (Subtype.ext rfl)
  · rw [or_iff_right hg0]
    constructor
    · intro hu
      rcases (ord_nonneg_of_mem v hg).lt_or_eq with h | h
      · exact h
      · exact absurd (v.isUnit_mk_of_ord_eq_zero hg0 h.symm) hu
    · rintro hpos ⟨u, hu⟩
      have h0 := v.ord_coe_unit u
      rw [hu] at h0
      exact hpos.ne' h0

theorem isUnit_algebraMap {a : k} (ha : a ≠ 0) :
    IsUnit (⟨algebraMap k K a, v.algebraMap_mem' a⟩ : v.toValuationSubring) :=
  v.isUnit_mk_of_ord_eq_zero (by simpa using ha) (ord_algebraMap v a)

theorem neg_le_ord_of_mem {D : Divisor k K} {f : K} (hf : f ∈ LSpace D) (hf0 : f ≠ 0)
    (w : Place k K) : -D w ≤ w.ord f :=
  ((mem_lSpace_iff_ord.mp hf).resolve_left hf0) w

end Ord

section RR

variable {k K : Type*} [Field k] [IsAlgClosed k] [Field K] [Algebra k K]
  [IsCurveOver k K] [Algebra.EssFiniteType k K]

omit [Algebra.EssFiniteType k K] in
private theorem _root_.AlgebraicCurve.HolomorphyRingAux.degree_single (v : Place k K) (n : ℤ) : Divisor.degree (Finsupp.single v n) = n := by
  rw [Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed v, Nat.cast_one, mul_one]

p2m_export "AlgebraicCurve.HolomorphyRingAux" "degree_single"
omit [Algebra.EssFiniteType k K] in

theorem degree_eq_sum (D : Divisor k K) : D.degree = ∑ v ∈ D.support, D v := by
  have h : D.degree = D.sum fun v n => n * (v.deg : ℤ) := by
    simp [Divisor.degree, Finsupp.liftAddHom_apply]
  rw [h, Finsupp.sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [IsCurveOver.deg_eq_one_of_isAlgClosed v, Nat.cast_one, mul_one]

theorem ell_eq (D : Divisor k K) (hD : 2 * (genusFF k K : ℤ) - 1 ≤ D.degree) :
    (ell D : ℤ) = D.degree + 1 - (genusFF k K : ℤ) := by
  obtain ⟨x, hx, hfin, hsep⟩ := IsCurveOver.exists_separating_transcendental (K := k) (F := K)
  exact AlgebraicCurve.ell_eq_degree_add_one_sub_genusFF_of_isAlgClosed_of_isSeparable k x hx hfin
    hsep D hD

theorem lSpace_lt {D E : Divisor k K} (hDE : D ≤ E) (hD : 2 * (genusFF k K : ℤ) - 1 ≤ D.degree)
    (hlt : D.degree < E.degree) : LSpace D < LSpace E := by
  refine lt_of_le_of_ne (lSpace_mono hDE) fun heq => ?_
  have h1 := ell_eq D hD
  have h2 := ell_eq E (hD.trans hlt.le)
  have h3 : (ell D : ℤ) = ell E := by
    show ((Module.finrank k (LSpace D) : ℕ) : ℤ) = ((Module.finrank k (LSpace E) : ℕ) : ℤ)
    rw [heq]
  omega

omit [IsAlgClosed k] [IsCurveOver k K] [Algebra.EssFiniteType k K] in

theorem ord_lt_of_mem_of_not_mem {D E : Divisor k K} {Q : Place k K} (hDE : ∀ v, v ≠ Q → D v = E v)
    {f : K} (hfE : f ∈ LSpace E) (hfD : f ∉ LSpace D) : f ≠ 0 ∧ Q.ord f < -D Q := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hfD (Submodule.zero_mem _)
  refine ⟨hf0, ?_⟩
  by_contra hge
  push Not at hge
  apply hfD
  rw [mem_lSpace_iff_ord]
  refine Or.inr fun v => ?_
  by_cases hv : v = Q
  · subst hv
    exact hge
  · rw [hDE v hv]
    exact neg_le_ord_of_mem hfE hf0 v

end RR

section Avoid

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

theorem exists_mem_not_mem_not_mem {V U₁ U₂ : Submodule R M} (h₁ : ¬V ≤ U₁) (h₂ : ¬V ≤ U₂) :
    ∃ x ∈ V, x ∉ U₁ ∧ x ∉ U₂ := by
  obtain ⟨a, haV, haU⟩ := Set.not_subset.mp h₁
  obtain ⟨b, hbV, hbU⟩ := Set.not_subset.mp h₂
  by_cases ha2 : a ∈ U₂
  · by_cases hb1 : b ∈ U₁
    · refine ⟨a + b, V.add_mem haV hbV, fun h => haU ?_, fun h => hbU ?_⟩
      · have := U₁.sub_mem h hb1
        rwa [add_sub_cancel_right] at this
      · have := U₂.sub_mem h ha2
        rwa [add_sub_cancel_left] at this
    · exact ⟨b, hbV, hb1, hbU⟩
  · exact ⟨a, haV, haU, ha2⟩

end Avoid

section Outside

variable {k K : Type*} [Field k] [IsAlgClosed k] [Field K] [Algebra k K]
  [IsCurveOver k K] [Algebra.EssFiniteType k K]

theorem exists_pole_only_at (Q₀ : Place k K) :
    ∃ f : K, f ∉ Q₀.toValuationSubring ∧ ∀ v : Place k K, v ≠ Q₀ → f ∈ v.toValuationSubring := by
  classical
  set G : ℤ := (genusFF k K : ℤ) with hG
  set D : Divisor k K := Finsupp.single Q₀ (2 * G) with hD
  set E : Divisor k K := Finsupp.single Q₀ (2 * G + 1) with hE
  have hDE : D ≤ E := by
    rw [hD, hE]
    exact Finsupp.single_le_single.mpr (by omega)
  have hlt : LSpace D < LSpace E :=
    lSpace_lt hDE (by rw [hD, degree_single]; omega) (by rw [hD, hE, degree_single, degree_single]; omega)
  obtain ⟨f, hfE, hfD⟩ := SetLike.exists_of_lt hlt
  have hagree : ∀ v, v ≠ Q₀ → D v = E v := fun v hv => by
    rw [hD, hE, Finsupp.single_eq_of_ne hv, Finsupp.single_eq_of_ne hv]
  obtain ⟨hf0, hord⟩ := ord_lt_of_mem_of_not_mem hagree hfE hfD
  have hG0 : 0 ≤ G := by rw [hG]; exact Nat.cast_nonneg _
  refine ⟨f, not_mem_of_ord_neg Q₀ ?_, fun v hv => ?_⟩
  · rw [hD, Finsupp.single_eq_same] at hord
    omega
  · refine v.mem_toValuationSubring_of_ord_nonneg_alt hf0 ?_
    have h := neg_le_ord_of_mem hfE hf0 v
    rwa [hE, Finsupp.single_eq_of_ne hv, neg_zero] at h

theorem exists_not_mem_finset (Q₀ : Place k K) (T : Finset (Place k K)) :
    ∃ v : Place k K, v ∉ T := by
  classical
  obtain ⟨f, hfQ, hfreg⟩ := exists_pole_only_at Q₀

  have hzero : ∀ c : k, ∃ z : Place k K, 0 < z.ord (f - algebraMap k K c) := by
    intro c
    set g : K := f - algebraMap k K c with hg
    have hgQ : g ∉ Q₀.toValuationSubring := fun h => hfQ <| by
      have : f = g + algebraMap k K c := by rw [hg, sub_add_cancel]
      rw [this]
      exact add_mem h (Q₀.algebraMap_mem' c)
    have hg0 : g ≠ 0 := fun h => hgQ (h ▸ zero_mem _)
    obtain ⟨E, hE, hE0⟩ := HasPrincipalDivisors.exists_divisor (K := k) (F := K) g hg0
    have hEQ : E Q₀ < 0 := by
      rw [hE]
      by_contra h
      push Not at h
      exact hgQ (Q₀.mem_toValuationSubring_of_ord_nonneg_alt hg0 h)
    rw [degree_eq_sum] at hE0
    obtain ⟨z, -, hz⟩ := Finset.exists_pos_of_sum_zero_of_exists_nonzero (fun v => E v) hE0
      ⟨Q₀, Finsupp.mem_support_iff.mpr hEQ.ne, hEQ.ne⟩
    exact ⟨z, by rw [← hE]; exact hz⟩
  choose z hz using hzero

  have hinj : Function.Injective z := by
    intro c c' hcc'
    by_contra hne
    have h1 := hz c
    have h2 := hz c'
    rw [← hcc'] at h2
    set w := z c
    have hm1 : f - algebraMap k K c ∈ w.toValuationSubring :=
      w.mem_toValuationSubring_of_ord_nonneg_alt (fun h => by rw [h] at h1; simp at h1) h1.le
    have hm2 : f - algebraMap k K c' ∈ w.toValuationSubring :=
      w.mem_toValuationSubring_of_ord_nonneg_alt (fun h => by rw [h] at h2; simp at h2) h2.le
    have hM1 := (mk_mem_maximalIdeal_iff w hm1).mpr (Or.inr h1)
    have hM2 := (mk_mem_maximalIdeal_iff w hm2).mpr (Or.inr h2)
    have hdiff := Ideal.sub_mem _ hM2 hM1
    have heq : (⟨f - algebraMap k K c', hm2⟩ : w.toValuationSubring) - ⟨f - algebraMap k K c, hm1⟩
        = ⟨algebraMap k K (c - c'), w.algebraMap_mem' _⟩ := by
      apply Subtype.ext
      simp only [map_sub]
      push_cast
      ring
    rw [heq] at hdiff
    exact (IsLocalRing.mem_maximalIdeal _ |>.mp hdiff) (isUnit_algebraMap w (sub_ne_zero.mpr hne))

  by_contra hall
  push Not at hall
  have : Finite k := Finite.of_injective (fun c => (⟨z c, hall (z c)⟩ : ↥T))
    (fun c c' h => hinj (congrArg Subtype.val h :))
  exact not_finite k

end Outside

section TheFunction

variable {k K : Type*} [Field k] [IsAlgClosed k] [Field K] [Algebra k K]
  [IsCurveOver k K] [Algebra.EssFiniteType k K]

theorem exists_piece (Q v₀ : Place k K) (hQ : Q ≠ v₀) :
    ∃ s : K, s ∉ Q.toValuationSubring ∧ (∀ v, v ≠ Q → s ∈ v.toValuationSubring) ∧
      v₀.adicValuation s ≤ exp (-2 : ℤ) := by
  classical
  set G : ℤ := (genusFF k K : ℤ) with hG
  have hG0 : 0 ≤ G := by rw [hG]; exact Nat.cast_nonneg _
  set m : ℤ := 2 * G + 2 with hm
  set D : Divisor k K := Finsupp.single Q (m - 1) - Finsupp.single v₀ 2 with hD
  set E : Divisor k K := Finsupp.single Q m - Finsupp.single v₀ 2 with hE
  have hDE : D ≤ E := by
    rw [hD, hE]
    exact sub_le_sub_right (Finsupp.single_le_single.mpr (by omega)) _
  have hdD : D.degree = m - 1 - 2 := by rw [hD, map_sub, degree_single, degree_single]
  have hdE : E.degree = m - 2 := by rw [hE, map_sub, degree_single, degree_single]
  have hlt : LSpace D < LSpace E :=
    lSpace_lt hDE (by rw [hdD]; omega) (by rw [hdD, hdE]; omega)
  obtain ⟨s, hsE, hsD⟩ := SetLike.exists_of_lt hlt
  have hagree : ∀ v, v ≠ Q → D v = E v := fun v hv => by
    rw [hD, hE, Finsupp.sub_apply, Finsupp.sub_apply, Finsupp.single_eq_of_ne hv,
      Finsupp.single_eq_of_ne hv]
  obtain ⟨hs0, hord⟩ := ord_lt_of_mem_of_not_mem hagree hsE hsD
  have hDQ : D Q = m - 1 := by
    rw [hD, Finsupp.sub_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne hQ, sub_zero]
  refine ⟨s, not_mem_of_ord_neg Q (by rw [hDQ] at hord; omega), fun v hv => ?_, ?_⟩
  · refine v.mem_toValuationSubring_of_ord_nonneg_alt hs0 ?_
    have h := neg_le_ord_of_mem hsE hs0 v
    have hEv : E v ≤ 0 := by
      rw [hE, Finsupp.sub_apply, Finsupp.single_eq_of_ne hv, zero_sub, neg_nonpos]
      exact Finsupp.single_nonneg.mpr (by norm_num) v
    omega
  · have h := hsE v₀
    have hEv₀ : E v₀ = -2 := by
      rw [hE, Finsupp.sub_apply, Finsupp.single_eq_of_ne hQ.symm, Finsupp.single_eq_same, zero_sub]
    rwa [hEv₀] at h

theorem exists_piece₀ (Q₀ v₀ : Place k K) (hQ : Q₀ ≠ v₀) :
    ∃ s : K, s ∉ Q₀.toValuationSubring ∧ (∀ v, v ≠ Q₀ → s ∈ v.toValuationSubring) ∧
      v₀.adicValuation s = exp (-1 : ℤ) := by
  classical
  set G : ℤ := (genusFF k K : ℤ) with hG
  have hG0 : 0 ≤ G := by rw [hG]; exact Nat.cast_nonneg _
  set m : ℤ := 2 * G + 2 with hm
  set W : Divisor k K := Finsupp.single Q₀ m - Finsupp.single v₀ 1 with hW
  set W₁ : Divisor k K := Finsupp.single Q₀ (m - 1) - Finsupp.single v₀ 1 with hW₁
  set W₂ : Divisor k K := Finsupp.single Q₀ m - Finsupp.single v₀ 2 with hW₂
  have hdW : W.degree = m - 1 := by rw [hW, map_sub, degree_single, degree_single]
  have hdW₁ : W₁.degree = m - 1 - 1 := by rw [hW₁, map_sub, degree_single, degree_single]
  have hdW₂ : W₂.degree = m - 2 := by rw [hW₂, map_sub, degree_single, degree_single]
  have hle₁ : W₁ ≤ W := by
    rw [hW₁, hW]
    exact sub_le_sub_right (Finsupp.single_le_single.mpr (by omega)) _
  have hle₂ : W₂ ≤ W := by
    rw [hW₂, hW]
    exact sub_le_sub_left (Finsupp.single_le_single.mpr (by norm_num)) _
  have hlt₁ : LSpace W₁ < LSpace W := lSpace_lt hle₁ (by rw [hdW₁]; omega) (by rw [hdW₁, hdW]; omega)
  have hlt₂ : LSpace W₂ < LSpace W := lSpace_lt hle₂ (by rw [hdW₂]; omega) (by rw [hdW₂, hdW]; omega)
  obtain ⟨s, hsW, hs₁, hs₂⟩ := exists_mem_not_mem_not_mem (not_le_of_gt hlt₁) (not_le_of_gt hlt₂)
  have hagree₁ : ∀ v, v ≠ Q₀ → W₁ v = W v := fun v hv => by
    rw [hW₁, hW, Finsupp.sub_apply, Finsupp.sub_apply, Finsupp.single_eq_of_ne hv,
      Finsupp.single_eq_of_ne hv]
  have hagree₂ : ∀ v, v ≠ v₀ → W₂ v = W v := fun v hv => by
    rw [hW₂, hW, Finsupp.sub_apply, Finsupp.sub_apply, Finsupp.single_eq_of_ne hv,
      Finsupp.single_eq_of_ne hv]
  obtain ⟨hs0, hordQ⟩ := ord_lt_of_mem_of_not_mem hagree₁ hsW hs₁
  obtain ⟨-, hordv⟩ := ord_lt_of_mem_of_not_mem hagree₂ hsW hs₂
  have hW₁Q : W₁ Q₀ = m - 1 := by
    rw [hW₁, Finsupp.sub_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne hQ, sub_zero]
  have hW₂v : W₂ v₀ = -2 := by
    rw [hW₂, Finsupp.sub_apply, Finsupp.single_eq_of_ne hQ.symm, Finsupp.single_eq_same, zero_sub]
  have hWv : W v₀ = -1 := by
    rw [hW, Finsupp.sub_apply, Finsupp.single_eq_of_ne hQ.symm, Finsupp.single_eq_same, zero_sub]
  refine ⟨s, not_mem_of_ord_neg Q₀ (by rw [hW₁Q] at hordQ; omega), fun v hv => ?_, ?_⟩
  · refine v.mem_toValuationSubring_of_ord_nonneg_alt hs0 ?_
    have h := neg_le_ord_of_mem hsW hs0 v
    have hWle : W v ≤ 0 := by
      rw [hW, Finsupp.sub_apply, Finsupp.single_eq_of_ne hv, zero_sub, neg_nonpos]
      exact Finsupp.single_nonneg.mpr (by norm_num) v
    omega
  · have h1 := neg_le_ord_of_mem hsW hs0 v₀
    rw [hWv, neg_neg] at h1
    rw [hW₂v] at hordv
    have hord1 : v₀.ord s = 1 := by omega
    rw [v₀.adicValuation_eq_exp_neg_ord hs0, hord1]

theorem exists_fn (N : Finset (Place k K)) (hN : N.Nonempty) :
    ∃ t : K, (∀ v, v ∉ N → t ∈ v.toValuationSubring) ∧ (∀ Q ∈ N, t ∉ Q.toValuationSubring) ∧
      ∃ v₀ : Place k K, v₀ ∉ N ∧ v₀.ord t = 1 := by
  classical
  obtain ⟨Q₀, hQ₀⟩ := hN
  obtain ⟨v₀, hv₀⟩ := exists_not_mem_finset Q₀ N
  have hne : ∀ Q ∈ N, Q ≠ v₀ := fun Q hQ h => hv₀ (h ▸ hQ)
  obtain ⟨s₀, hs₀Q, hs₀reg, hs₀v⟩ := exists_piece₀ Q₀ v₀ (hne Q₀ hQ₀)
  have hpiece : ∀ Q : Place k K, ∃ s : K, Q ∈ N → Q ≠ Q₀ →
      s ∉ Q.toValuationSubring ∧ (∀ v, v ≠ Q → s ∈ v.toValuationSubring) ∧
        v₀.adicValuation s ≤ exp (-2 : ℤ) := by
    intro Q
    by_cases hQ : Q ∈ N
    · obtain ⟨s, h1, h2, h3⟩ := exists_piece Q v₀ (hne Q hQ)
      exact ⟨s, fun _ _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨0, fun h _ => (hQ h).elim⟩
  choose s hs using hpiece
  let tQ : Place k K → K := fun Q => if Q = Q₀ then s₀ else s Q
  have htQ₀ : tQ Q₀ = s₀ := if_pos rfl
  have htQ : ∀ Q, Q ≠ Q₀ → tQ Q = s Q := fun Q h => if_neg h

  have hreg : ∀ Q ∈ N, ∀ v, v ≠ Q → tQ Q ∈ v.toValuationSubring := by
    intro Q hQ v hv
    by_cases h : Q = Q₀
    · rw [h] at hv ⊢
      rw [htQ₀]
      exact hs₀reg v hv
    · rw [htQ Q h]
      exact (hs Q hQ h).2.1 v hv
  have hpole : ∀ Q ∈ N, tQ Q ∉ Q.toValuationSubring := by
    intro Q hQ
    by_cases h : Q = Q₀
    · rw [h, htQ₀]
      exact hs₀Q
    · rw [htQ Q h]
      exact (hs Q hQ h).1
  have hsmall : ∀ Q ∈ N.erase Q₀, v₀.adicValuation (tQ Q) ≤ exp (-2 : ℤ) := by
    intro Q hQ
    rw [htQ Q (Finset.ne_of_mem_erase hQ)]
    exact (hs Q (Finset.mem_of_mem_erase hQ) (Finset.ne_of_mem_erase hQ)).2.2
  refine ⟨∑ Q ∈ N, tQ Q, fun v hv => ?_, fun Q hQ ht => ?_, v₀, hv₀, ?_⟩
  · exact sum_mem fun Q hQ => hreg Q hQ v (fun h => hv (h ▸ hQ))
  · apply hpole Q hQ
    have hsplit : tQ Q = ∑ Q' ∈ N, tQ Q' - ∑ Q' ∈ N.erase Q, tQ Q' := by
      rw [← Finset.add_sum_erase N tQ hQ, add_sub_cancel_right]
    rw [hsplit]
    exact sub_mem ht (sum_mem fun Q' hQ' =>
      hreg Q' (Finset.mem_of_mem_erase hQ') Q (Finset.ne_of_mem_erase hQ').symm)
  · have hsum : ∑ Q ∈ N, tQ Q = tQ Q₀ + ∑ Q ∈ N.erase Q₀, tQ Q :=
      (Finset.add_sum_erase N tQ hQ₀).symm
    have h0 : v₀.adicValuation (tQ Q₀) = exp (-1 : ℤ) := by rw [htQ₀]; exact hs₀v
    have hrest : v₀.adicValuation (∑ Q ∈ N.erase Q₀, tQ Q) ≤ exp (-2 : ℤ) :=
      Valuation.map_sum_le _ hsmall
    have hval : v₀.adicValuation (∑ Q ∈ N, tQ Q) = exp (-1 : ℤ) := by
      rw [hsum, Valuation.map_add_eq_of_lt_left, h0]
      rw [h0]
      exact hrest.trans_lt (WithZero.exp_lt_exp.mpr (by norm_num))
    show -(WithZero.log (v₀.adicValuation (∑ Q ∈ N, tQ Q))) = 1
    rw [hval, WithZero.log_exp]
    norm_num

end TheFunction

section FieldTheory

open IntermediateField

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

theorem isTranscendenceBasis_of_transcendental {x : K} (hx : Transcendental k x)
    (hfd : FiniteDimensional k⟮x⟯ K) : IsTranscendenceBasis k (fun _ : Fin 1 => x) := by
  have hind : AlgebraicIndependent k (fun _ : Fin 1 => x) :=
    algebraicIndependent_unique_type_iff.mpr hx
  refine hind.isTranscendenceBasis_iff_isAlgebraic.mpr ?_
  have hr : Set.range (fun _ : Fin 1 => x) = ({x} : Set K) := by
    ext y
    simp [eq_comm]
  rw [hr, ← IntermediateField.isAlgebraic_adjoin_iff_top]
  haveI := hfd
  exact Algebra.IsAlgebraic.of_finite k⟮x⟯ K

theorem isAlgebraic_adjoin_of_transcendental {x : K} (hx : Transcendental k x)
    (hfd : FiniteDimensional k⟮x⟯ K) {t : K} (ht : Transcendental k t) :
    Algebra.IsAlgebraic k⟮t⟯ K := by
  classical
  have htind : AlgebraicIndepOn k id ({t} : Set K) := by
    refine algebraicIndependent_unique_type_iff.mpr ?_
    simpa using ht
  obtain ⟨s, hts, hbasis⟩ := exists_isTranscendenceBasis_superset htind
  have hcard := hbasis.lift_cardinalMk_eq (isTranscendenceBasis_of_transcendental hx hfd)
  simp only [Cardinal.mk_fin, Nat.cast_one, Cardinal.lift_one, Cardinal.lift_eq_one] at hcard
  have hsub : s.Subsingleton := Cardinal.mk_le_one_iff_set_subsingleton.mp hcard.le
  have hseq : s = {t} := hsub.eq_singleton_of_mem (hts rfl)
  subst hseq
  have h := hbasis.isAlgebraic_field
  rwa [Subtype.range_coe] at h

theorem finiteDimensional_adjoin_of_transcendental {x : K} (hx : Transcendental k x)
    (hfd : FiniteDimensional k⟮x⟯ K) {t : K} (ht : Transcendental k t) :
    FiniteDimensional k⟮t⟯ K := by
  classical
  haveI := hfd
  have halg : Algebra.IsAlgebraic k⟮t⟯ K := isAlgebraic_adjoin_of_transcendental hx hfd ht
  obtain ⟨s, hs⟩ := Module.finite_def.mp hfd
  set E : IntermediateField k⟮t⟯ K :=
    IntermediateField.adjoin k⟮t⟯ (insert x (↑s : Set K)) with hE
  have hxE : x ∈ E := IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)
  have hrange : ∀ r : k⟮x⟯, (r : K) ∈ E := by
    intro r
    have hle : k⟮x⟯ ≤ E.restrictScalars k :=
      IntermediateField.adjoin_simple_le_iff.mpr
        ((IntermediateField.mem_restrictScalars k).mpr hxE)
    exact (IntermediateField.mem_restrictScalars k).mp (hle r.2)
  have hmem : ∀ y : K, y ∈ E := by
    intro y
    have hy : y ∈ Submodule.span k⟮x⟯ (↑s : Set K) := by
      rw [hs]; exact Submodule.mem_top
    refine Submodule.span_induction (fun z hz => ?_) ?_ (fun z w _ _ hz hw => ?_)
      (fun r z _ hz => ?_) hy
    · exact IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ hz)
    · exact zero_mem E
    · exact add_mem hz hw
    · rw [Algebra.smul_def]
      exact mul_mem (hrange r) hz
  have htop : E = ⊤ := by
    rw [eq_top_iff]
    intro y _
    exact hmem y
  haveI : Finite ↥(insert x (↑s : Set K)) :=
    Set.Finite.to_subtype ((s.finite_toSet).insert x)
  have hfdE : FiniteDimensional k⟮t⟯ ↥E := by
    rw [hE]
    exact IntermediateField.finiteDimensional_adjoin
      (fun z _ => (halg.isAlgebraic z).isIntegral)
  rw [htop] at hfdE
  haveI := hfdE
  exact LinearEquiv.finiteDimensional
    (IntermediateField.topEquiv (F := k⟮t⟯) (E := K)).toLinearEquiv

theorem transcendental_of_not_mem [IsAlgClosed k] {t : K} (Q : Place k K)
    (ht : t ∉ Q.toValuationSubring) : Transcendental k t := by
  intro halg
  haveI : Algebra.IsAlgebraic k k⟮t⟯ := IntermediateField.isAlgebraic_adjoin_simple halg.isIntegral
  haveI : Algebra.IsIntegral k k⟮t⟯ := Algebra.isAlgebraic_iff_isIntegral.mp inferInstance
  obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := k⟮t⟯)).2
    ⟨t, IntermediateField.mem_adjoin_simple_self k t⟩
  apply ht
  have h := congrArg (fun z : k⟮t⟯ => (z : K)) hc
  simp only [IntermediateField.coe_algebraMap_apply] at h
  rw [← h]
  exact Q.algebraMap_mem' c

theorem mem_of_isIntegral_of_le {A₀ : Subalgebra k K} (O : ValuationSubring K)
    (hle : ∀ a ∈ A₀, a ∈ O) {y : K} (hy : IsIntegral A₀ y) : y ∈ O := by
  letI : Algebra A₀ O := (A₀.val.toRingHom.codRestrict O (fun a => hle a a.2)).toAlgebra
  haveI : IsScalarTower A₀ O K := IsScalarTower.of_algebraMap_eq (fun a => rfl)
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (R := O) (hy.tower_top (A := O))
  rw [← hz]
  exact z.2

end FieldTheory

section Main

open IntermediateField
open scoped IntermediateField.algebraAdjoinAdjoin

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

theorem mem_iInf_iff {N : Finset (Place k K)} {x : K} :
    x ∈ (⨅ (Q : Place k K) (_ : Q ∉ N), Q.toValuationSubring.toSubring) ↔
      ∀ Q : Place k K, Q ∉ N → x ∈ Q.toValuationSubring := by
  simp only [Subring.mem_iInf]
  rfl

def holRing (N : Finset (Place k K)) : Subalgebra k K :=
  { (⨅ (Q : Place k K) (_ : Q ∉ N), Q.toValuationSubring.toSubring).toSubsemiring with
    algebraMap_mem' := fun c => mem_iInf_iff.mpr fun Q _ => Q.algebraMap_mem' c }

theorem mem_holRing_iff {N : Finset (Place k K)} {x : K} :
    x ∈ holRing N ↔ ∀ Q : Place k K, Q ∉ N → x ∈ Q.toValuationSubring :=
  mem_iInf_iff

def centre (C : Subalgebra k K) (Q : Place k K) (hQ : ∀ c : C, (c : K) ∈ Q.toValuationSubring) :
    Ideal C :=
  (maximalIdeal Q.toValuationSubring).comap (C.val.toRingHom.codRestrict Q.toValuationSubring hQ)

theorem mem_centre_iff {C : Subalgebra k K} {Q : Place k K}
    (hQ : ∀ c : C, (c : K) ∈ Q.toValuationSubring) (g : C) :
    g ∈ centre C Q hQ ↔ (g : K) = 0 ∨ 0 < Q.ord (g : K) := by
  rw [centre, Ideal.mem_comap]
  exact mk_mem_maximalIdeal_iff Q (hQ g)

theorem isPrime_centre {C : Subalgebra k K} {Q : Place k K}
    (hQ : ∀ c : C, (c : K) ∈ Q.toValuationSubring) : (centre C Q hQ).IsPrime :=
  Ideal.comap_isPrime _ _

theorem mem_nonunits_iff_of_mem (v : Place k K) {g : K} (hg : g ∈ v.toValuationSubring) :
    g ∈ v.toValuationSubring.nonunits ↔ g = 0 ∨ 0 < v.ord g := by
  rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
  exact ⟨fun ⟨_, h⟩ => (mk_mem_maximalIdeal_iff v hg).mp h,
    fun h => ⟨hg, (mk_mem_maximalIdeal_iff v hg).mpr h⟩⟩

theorem exists_inv_not_mem (C : Subalgebra k K) [IsFractionRing C K] (Q : Place k K)
    (hQ : ∀ c : C, (c : K) ∈ Q.toValuationSubring) :
    ∃ c : C, c ≠ 0 ∧ (c : K)⁻¹ ∉ Q.toValuationSubring := by
  by_contra hall
  push Not at hall
  apply Q.ne_top'
  refine SetLike.ext fun z => ⟨fun _ => ValuationSubring.mem_top z, fun _ => ?_⟩
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := C) z
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  rw [div_eq_mul_inv]
  exact mul_mem (hQ a) (hall b hb0)

variable [IsAlgClosed k] [IsCurveOver k K] [Algebra.EssFiniteType k K]

theorem holRing_structure (N : Finset (Place k K)) (hN : N.Nonempty) :
    IsDedekindDomain (holRing N) ∧ IsFractionRing (holRing N) K ∧
      ∃ t : K, t ∈ holRing N ∧ ∀ Q ∈ N, t ∉ Q.toValuationSubring := by
  classical
  obtain ⟨t, htreg, htpole, v₀, hv₀, hv₀t⟩ := exists_fn N hN
  obtain ⟨Q₀, hQ₀⟩ := hN

  have httr : Transcendental k t := transcendental_of_not_mem Q₀ (htpole Q₀ hQ₀)
  obtain ⟨x, hx, hxfin, -⟩ := IsCurveOver.exists_separating_transcendental (K := k) (F := K)
  haveI hfin : FiniteDimensional k⟮t⟯ K := finiteDimensional_adjoin_of_transcendental hx hxfin httr
  haveI : Algebra.IsAlgebraic k⟮x⟯ K := by
    haveI := hxfin
    exact Algebra.IsAlgebraic.of_finite k⟮x⟯ K
  haveI hsep : Algebra.IsSeparable k⟮t⟯ K := Place.isSeparable_adjoin_of_ord_eq_one x v₀ hv₀t

  have htC : t ∈ holRing N := mem_holRing_iff.mpr htreg
  have hA₀C : Algebra.adjoin k ({t} : Set K) ≤ holRing N :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr htC)
  haveI : IsPrincipalIdealRing (Algebra.adjoin k ({t} : Set K)) :=
    IsPrincipalIdealRing.of_surjective (Polynomial.algEquivOfTranscendental k t httr).toAlgHom.toRingHom
      (Polynomial.algEquivOfTranscendental k t httr).surjective
  haveI : IsDedekindDomain (Algebra.adjoin k ({t} : Set K)) := IsPrincipalIdealRing.isDedekindDomain _
  letI : Algebra (Algebra.adjoin k ({t} : Set K)) (holRing N) := (Subalgebra.inclusion hA₀C).toRingHom.toAlgebra
  haveI : IsScalarTower (Algebra.adjoin k ({t} : Set K)) (holRing N) K :=
    IsScalarTower.of_algebraMap_eq (fun a => rfl)

  haveI hSD : IsDedekindDomain (integralClosure (Algebra.adjoin k ({t} : Set K)) K) :=
    integralClosure.isDedekindDomain (Algebra.adjoin k ({t} : Set K)) k⟮t⟯ K
  haveI hSF : IsFractionRing (integralClosure (Algebra.adjoin k ({t} : Set K)) K) K :=
    integralClosure.isFractionRing_of_finite_extension k⟮t⟯ K
  have hts : t ∈ integralClosure (Algebra.adjoin k ({t} : Set K)) K := by
    rw [mem_integralClosure_iff]
    exact (isIntegral_algebraMap (R := Algebra.adjoin k ({t} : Set K)) (A := K)
      (x := ⟨t, Algebra.self_mem_adjoin_singleton k t⟩))

  haveI hIC : IsIntegralClosure (holRing N) (Algebra.adjoin k ({t} : Set K)) K := by
    refine ⟨Subtype.val_injective, fun {y} => ⟨fun hy => ⟨⟨y, ?_⟩, rfl⟩, ?_⟩⟩
    ·
      refine mem_holRing_iff.mpr fun Q hQN => mem_of_isIntegral_of_le Q.toValuationSubring ?_ hy
      intro a ha
      have hle : Algebra.adjoin k ({t} : Set K) ≤ holRing N := hA₀C
      exact (mem_holRing_iff.mp (hle ha)) Q hQN
    ·
      rintro ⟨c, rfl⟩
      have hc : (c : K) ∈ holRing N := c.2
      suffices hcS : (c : K) ∈ (algebraMap (integralClosure (Algebra.adjoin k ({t} : Set K)) K) K).range by
        obtain ⟨z, hz⟩ := hcS
        show IsIntegral (Algebra.adjoin k ({t} : Set K)) (c : K)
        rw [← hz]
        exact (mem_integralClosure_iff _ _).mp z.2
      refine IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one K _ fun P => ?_
      set w : Place k K := Place.ofHeightOneSpectrum (K := k) P with hw
      have htw : t ∈ w.toValuationSubring := by
        rw [hw, Place.ofHeightOneSpectrum_toValuationSubring, Valuation.mem_valuationSubring_iff]
        exact P.valuation_le_one ⟨t, hts⟩
      have hwN : w ∉ N := fun h => htpole w h htw
      have hcw : (c : K) ∈ w.toValuationSubring := (mem_holRing_iff.mp hc) w hwN
      rwa [hw, Place.ofHeightOneSpectrum_toValuationSubring, Valuation.mem_valuationSubring_iff] at hcw
  haveI hCD : IsDedekindDomain (holRing N) :=
    IsIntegralClosure.isDedekindDomain (Algebra.adjoin k ({t} : Set K)) k⟮t⟯ K (holRing N)
  haveI hCF : IsFractionRing (holRing N) K :=
    IsIntegralClosure.isFractionRing_of_finite_extension (Algebra.adjoin k ({t} : Set K)) k⟮t⟯ K
      (holRing N)
  exact ⟨hCD, hCF, t, htC, htpole⟩

theorem holRing_dictionary (N : Finset (Place k K)) (hN : N.Nonempty) :
    IsDedekindDomain ↥(holRing N) ∧
    (∀ 𝔪 : Ideal ↥(holRing N), 𝔪.IsMaximal →
      ∃! Q : Place k K, Q ∉ N ∧
        ∀ g : ↥(holRing N), g ∈ 𝔪 ↔ (g : K) = 0 ∨ 0 < Q.ord (g : K)) ∧
    (∀ Q : Place k K, Q ∉ N →
      ∃ 𝔪 : Ideal ↥(holRing N), 𝔪.IsMaximal ∧
        ∀ g : ↥(holRing N), g ∈ 𝔪 ↔ (g : K) = 0 ∨ 0 < Q.ord (g : K)) ∧
    (∀ 𝔭 : Ideal ↥(holRing N), 𝔭.IsPrime → 𝔭 ≠ ⊥ → 𝔭.IsMaximal) := by
  classical
  obtain ⟨hD, hF, t, htC, htpole⟩ := holRing_structure N hN
  haveI := hD
  haveI := hF
  have hsub : ∀ Q : Place k K, Q ∉ N → ∀ c : holRing N, (c : K) ∈ Q.toValuationSubring :=
    fun Q hQ c => (mem_holRing_iff.mp c.2) Q hQ
  have hdim : ∀ 𝔭 : Ideal ↥(holRing N), 𝔭.IsPrime → 𝔭 ≠ ⊥ → 𝔭.IsMaximal :=
    fun 𝔭 h𝔭 hne => h𝔭.isMaximal hne

  have hcentre : ∀ Q : Place k K, ∀ hQ : Q ∉ N, (centre (holRing N) Q (hsub Q hQ)).IsMaximal := by
    intro Q hQ
    refine hdim _ (isPrime_centre (hsub Q hQ)) fun hbot => ?_
    obtain ⟨c, hc0, hcinv⟩ := exists_inv_not_mem (holRing N) Q (hsub Q hQ)
    have hcK : (c : K) ≠ 0 := fun h => hc0 (Subtype.ext h)
    have hnot : c ∉ centre (holRing N) Q (hsub Q hQ) := by rw [hbot]; exact hc0
    rw [mem_centre_iff] at hnot
    push Not at hnot
    have hord : Q.ord (c : K) = 0 := le_antisymm hnot.2 (ord_nonneg_of_mem Q (hsub Q hQ c))
    exact hcinv (Q.mem_toValuationSubring_of_ord_nonneg_alt (inv_ne_zero hcK)
      (by rw [Q.ord_inv, hord, neg_zero]))
  refine ⟨hD, fun 𝔪 h𝔪 => ?_, fun Q hQ => ⟨_, hcentre Q hQ, mem_centre_iff (hsub Q hQ)⟩, hdim⟩

  have hne : 𝔪 ≠ ⊥ := by
    intro hbot
    rw [hbot] at h𝔪
    have hfield : IsField (holRing N) := Ring.isField_iff_maximal_bot.mpr h𝔪
    obtain ⟨Q₀, hQ₀⟩ := hN
    obtain ⟨v₀, hv₀⟩ := exists_not_mem_finset Q₀ N
    obtain ⟨c, hc0, hcinv⟩ := exists_inv_not_mem (holRing N) v₀ (hsub v₀ hv₀)
    obtain ⟨b, hb⟩ := hfield.mul_inv_cancel hc0
    have hcK : (c : K) ≠ 0 := fun h => hc0 (Subtype.ext h)
    have hbK : (b : K) = (c : K)⁻¹ := by
      have h := congrArg (fun z : holRing N => (z : K)) hb
      simp only [Subalgebra.coe_mul, Subalgebra.coe_one] at h
      exact (eq_inv_of_mul_eq_one_right h)
    exact hcinv (hbK ▸ hsub v₀ hv₀ b)
  set P : IsDedekindDomain.HeightOneSpectrum (holRing N) := ⟨𝔪, h𝔪.isPrime, hne⟩ with hP
  set w : Place k K := Place.ofHeightOneSpectrum (K := k) P with hw
  have hOw : w.toValuationSubring = (P.valuation K).valuationSubring := rfl
  have hCw : ∀ c : holRing N, (c : K) ∈ w.toValuationSubring := fun c => by
    rw [hOw, Valuation.mem_valuationSubring_iff]
    exact P.valuation_le_one c
  have hwN : w ∉ N := fun h => htpole w h (hCw ⟨t, htC⟩)
  have hmem : ∀ g : holRing N, g ∈ 𝔪 ↔ (g : K) = 0 ∨ 0 < w.ord (g : K) := by
    intro g
    rw [← mk_mem_maximalIdeal_iff w (hCw g), ValuationSubring.valuation_lt_one_iff]
    show g ∈ 𝔪 ↔ (P.valuation K).valuationSubring.valuation (g : K) < 1
    rw [← (Valuation.isEquiv_valuation_valuationSubring (P.valuation K)).lt_one_iff_lt_one]
    exact (P.valuation_lt_one_iff_mem g).symm
  refine ⟨w, ⟨hwN, hmem⟩, fun Q' ⟨hQ'N, hQ'mem⟩ => ?_⟩
  refine Place.eq_of_forall_coe_mem_nonunits_iff_of_isDedekindDomain (holRing N) Q' w
    (hsub Q' hQ'N) hCw fun a => ?_
  rw [mem_nonunits_iff_of_mem Q' (hsub Q' hQ'N a), mem_nonunits_iff_of_mem w (hCw a), ← hQ'mem a,
    ← hmem a]

end Main

end HolomorphyRingAux

end AlgebraicCurve

p2m_open "AlgebraicCurve~isAlgebraic_adjoin_of_transcendental" in open _root_.P2MW.S_AlgebraicCurve_Place_isDedekindDomain_iInf_toSubring_and_isMaximal_iff_of_finset_nonempty.AlgebraicCurve in
theorem solution
    {k : Type*} [Field k] [IsAlgClosed k] {K : Type*} [Field K] [Algebra k K]
    [IsCurveOver k K] [Algebra.EssFiniteType k K]
    (N : Finset (Place k K)) (hN : N.Nonempty) :
    IsDedekindDomain ↥(⨅ (Q : Place k K) (_ : Q ∉ N), Q.toValuationSubring.toSubring) ∧
    (∀ 𝔪 : Ideal ↥(⨅ (Q : Place k K) (_ : Q ∉ N), Q.toValuationSubring.toSubring), 𝔪.IsMaximal →
      ∃! Q : Place k K, Q ∉ N ∧
        ∀ g : ↥(⨅ (Q : Place k K) (_ : Q ∉ N), Q.toValuationSubring.toSubring), g ∈ 𝔪 ↔ (g : K) = 0 ∨ 0 < Q.ord (g : K)) ∧
    (∀ Q : Place k K, Q ∉ N →
      ∃ 𝔪 : Ideal ↥(⨅ (Q : Place k K) (_ : Q ∉ N), Q.toValuationSubring.toSubring), 𝔪.IsMaximal ∧
        ∀ g : ↥(⨅ (Q : Place k K) (_ : Q ∉ N), Q.toValuationSubring.toSubring), g ∈ 𝔪 ↔ (g : K) = 0 ∨ 0 < Q.ord (g : K)) ∧
    (∀ 𝔭 : Ideal ↥(⨅ (Q : Place k K) (_ : Q ∉ N), Q.toValuationSubring.toSubring), 𝔭.IsPrime → 𝔭 ≠ ⊥ → 𝔭.IsMaximal) :=
  AlgebraicCurve.HolomorphyRingAux.holRing_dictionary N hN

end S_AlgebraicCurve_Place_isDedekindDomain_iInf_toSubring_and_isMaximal_iff_of_finset_nonempty
end P2MW
export P2MW.S_AlgebraicCurve_Place_isDedekindDomain_iInf_toSubring_and_isMaximal_iff_of_finset_nonempty (solution)
