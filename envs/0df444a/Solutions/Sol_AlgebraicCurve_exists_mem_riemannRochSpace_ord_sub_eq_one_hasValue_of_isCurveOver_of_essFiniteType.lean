-- Prove2me | solution 1 for AlgebraicCurve.exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_isCurveOver_of_essFiniteType
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/04d27f1a-f195-51bc-b5f6-0b188a231b11

import Mathlib
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_ell_eq_degree_add_one_sub_genusFF_of_isAlgClosed_of_isSeparable
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_isCurveOver_of_essFiniteType
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_isCurveOver_of_essFiniteType.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "riemannRochSpace mem_riemannRochSpace_iff genusFF Place Place.ord Place.ord_zero Divisor Divisor.degree Divisor.degree_single Place.HasValue LSpace ell lSpace_mono IsCurveOver IsCurveOver.deg_eq_one_of_isAlgClosed IsCurveOver.finiteResidue ell_eq_degree_add_one_sub_genusFF_of_isAlgClosed_of_isSeparable IsCurveOver.exists_separating_transcendental Place.mem_iff_ord_nonneg Place.HasValue.sub Place.HasValue.add Place.HasValue.smul Place.HasValue.eq_val"
namespace InterpGen
p2m_open "AlgebraicCurve"

section Avoid

variable {k V : Type*} [Field k] [Infinite k] [AddCommGroup V] [Module k V]

theorem exists_forall_ne_zero {ι : Type*} [DecidableEq ι] (s : Finset ι) (φ : ι → V →ₗ[k] k)
    (hφ : ∀ i ∈ s, φ i ≠ 0) : ∃ v : V, ∀ i ∈ s, φ i v ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert a s ha ih =>
    obtain ⟨v, hv⟩ := ih (fun i hi => hφ i (Finset.mem_insert_of_mem hi))
    by_cases hav : φ a v = 0
    · have hne : φ a ≠ 0 := hφ a (Finset.mem_insert_self a s)
      obtain ⟨u, hu⟩ : ∃ u : V, φ a u ≠ 0 := by
        by_contra h
        push_neg at h
        exact hne (LinearMap.ext fun x => by simpa using h x)
      let bad : Finset k := insert 0 (s.image fun i => -(φ i v) / (φ i u))
      obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset bad
      have ht0 : t ≠ 0 := fun h => ht (by rw [h]; exact Finset.mem_insert_self _ _)
      refine ⟨v + t • u, fun i hi => ?_⟩
      rcases Finset.mem_insert.mp hi with rfl | hi
      · rw [map_add, map_smul, hav, zero_add, smul_eq_mul]
        exact mul_ne_zero ht0 hu
      · rw [map_add, map_smul, smul_eq_mul]
        intro h0
        by_cases hiu : φ i u = 0
        · rw [hiu, mul_zero, add_zero] at h0
          exact hv i hi h0
        · apply ht
          refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, hi, ?_⟩)
          rw [div_eq_iff hiu]
          linear_combination -h0
    · refine ⟨v, fun i hi => ?_⟩
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hav
      · exact hv i hi

theorem exists_forall_apply_ne {ι : Type*} [DecidableEq ι] (s : Finset ι) (φ : ι → V →ₗ[k] k)
    (c : ι → k) (hφ : ∀ i ∈ s, φ i ≠ 0) (x₀ : V) : ∃ w : V, ∀ i ∈ s, φ i (x₀ + w) ≠ c i := by
  classical
  obtain ⟨v, hv⟩ := exists_forall_ne_zero s φ hφ
  let bad : Finset k := s.image fun i => (c i - φ i x₀) / φ i v
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset bad
  refine ⟨t • v, fun i hi h => ht (Finset.mem_image.mpr ⟨i, hi, ?_⟩)⟩
  rw [map_add, map_smul, smul_eq_mul] at h
  rw [div_eq_iff (hv i hi)]
  linear_combination -h

end Avoid

section PlaceValues

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_nonneg_of_mem' (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  by_cases h0 : f = 0
  · rw [h0, Place.ord_zero]
  · exact (Place.mem_iff_ord_nonneg v h0).mp hf

theorem mem_of_ord_nonneg' (v : Place K F) {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := (Place.mem_iff_ord_nonneg v hf).mpr h

theorem mem_of (v : Place K F) {g : F} (hg : g = 0 ∨ 0 ≤ v.ord g) : g ∈ v.toValuationSubring := by
  rcases hg with rfl | h
  · exact zero_mem _
  · by_cases h0 : g = 0
    · rw [h0]; exact zero_mem _
    · exact mem_of_ord_nonneg' v h0 h

theorem adicValuation_eq_exp_neg_ord (v : Place K F) {f : F} (hf : f ≠ 0) :
    v.adicValuation f = WithZero.exp (-v.ord f) := by
  rw [Place.ord, neg_neg, WithZero.exp_log (v.adicValuation_ne_zero hf)]

theorem ord_add_eq_of_lt (v : Place K F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0)
    (h : v.ord f < v.ord g) : v.ord (f + g) = v.ord f := by
  have hlt : v.adicValuation g < v.adicValuation f := by
    rw [adicValuation_eq_exp_neg_ord v hf, adicValuation_eq_exp_neg_ord v hg, WithZero.exp_lt_exp]
    linarith
  have := Valuation.map_add_eq_of_lt_left v.adicValuation hlt
  simp only [Place.ord, this]

private theorem _root_.AlgebraicCurve.Place.HasValue.sub {v : Place K F} {g g' : F} {a a' : K} (h : v.HasValue g a)
    (h' : v.HasValue g' a') : v.HasValue (g - g') (a - a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨sub_mem hg hg', ?_⟩
  have hx : (⟨g - g', sub_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ - ⟨g', hg'⟩ := rfl
  rw [hx, map_sub, hr, hr', map_sub]

p2m_alias "P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_isCurveOver_of_essFiniteType.AlgebraicCurve.Place.HasValue.sub" "AlgebraicCurve.Place.HasValue.sub"
private theorem _root_.AlgebraicCurve.Place.HasValue.add {v : Place K F} {g g' : F} {a a' : K} (h : v.HasValue g a)
    (h' : v.HasValue g' a') : v.HasValue (g + g') (a + a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨add_mem hg hg', ?_⟩
  have hx : (⟨g + g', add_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ + ⟨g', hg'⟩ := rfl
  rw [hx, map_add, hr, hr', map_add]

p2m_alias "P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_isCurveOver_of_essFiniteType.AlgebraicCurve.Place.HasValue.add" "AlgebraicCurve.Place.HasValue.add"
private theorem _root_.AlgebraicCurve.Place.HasValue.smul {v : Place K F} {g : F} {a : K} (h : v.HasValue g a) (c : K) :
    v.HasValue (c • g) (c * a) := by
  rw [Algebra.smul_def]
  exact (v.hasValue_algebraMap c).mul h

p2m_alias "P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_isCurveOver_of_essFiniteType.AlgebraicCurve.Place.HasValue.smul" "AlgebraicCurve.Place.HasValue.smul"

theorem hasValue_sum_zero (v : Place K F) {ι : Type*} (s : Finset ι) (f : ι → F)
    (h : ∀ i ∈ s, v.HasValue (f i) 0) : v.HasValue (∑ i ∈ s, f i) 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using v.hasValue_algebraMap (0 : K)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have := (h a (Finset.mem_insert_self a s)).add (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))
    rwa [zero_add] at this

theorem ord_pos_of_hasValue_zero (v : Place K F) {g : F} (hg : g ≠ 0) (h : v.HasValue g 0) :
    0 < v.ord g := by
  have hmem := h.mem
  have hres : IsLocalRing.residue v.toValuationSubring ⟨g, hmem⟩ = 0 := by
    rw [h.residue_eq, map_zero]
  have hmax : (⟨g, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring :=
    (IsLocalRing.residue_eq_zero_iff _).mp hres
  have h0 : 0 ≤ v.ord g := ord_nonneg_of_mem' v hmem
  rcases h0.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    obtain ⟨hm, hu⟩ := v.exists_isUnit_of_ord_eq_zero hg heq.symm
    exact (IsLocalRing.mem_maximalIdeal _).mp hmax hu

theorem hasValue_of_ord_sub_pos (v : Place K F) {g : F} {b : K}
    (h : 0 < v.ord (g - algebraMap K F b)) : v.HasValue g b := by
  have hne : g - algebraMap K F b ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at h; exact lt_irrefl _ h
  have hmem : g - algebraMap K F b ∈ v.toValuationSubring := mem_of_ord_nonneg' v hne h.le
  have hmax : (⟨_, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
    rw [IsLocalRing.mem_maximalIdeal]
    intro hu
    have h0 := v.ord_coe_unit hu.unit
    rw [IsUnit.unit_spec] at h0
    change v.ord (g - algebraMap K F b) = 0 at h0
    omega
  have hgmem : g ∈ v.toValuationSubring := by
    have : g = (g - algebraMap K F b) + algebraMap K F b := by ring
    rw [this]
    exact add_mem hmem (v.algebraMap_mem' b)
  refine ⟨hgmem, ?_⟩
  have hx : (⟨g, hgmem⟩ : v.toValuationSubring) =
      ⟨_, hmem⟩ + ⟨algebraMap K F b, v.algebraMap_mem' b⟩ := Subtype.ext (by push_cast; ring)
  rw [hx, map_add, (IsLocalRing.residue_eq_zero_iff _).mpr hmax, zero_add]
  exact v.residue_algebraMap b

theorem ord_sub_pos_of_hasValue (v : Place K F) {g : F} {b : K}
    (h : v.HasValue g b) (hne : g - algebraMap K F b ≠ 0) : 0 < v.ord (g - algebraMap K F b) := by
  have h' := h.sub (v.hasValue_algebraMap b)
  rw [sub_self] at h'
  exact ord_pos_of_hasValue_zero v hne h'

theorem ord_pos_of_hasValue_zero' (v : Place K F) {g : F} (h : v.HasValue g 0) (hne : g ≠ 0) :
    0 < v.ord g := ord_pos_of_hasValue_zero v hne h

theorem ord_nonneg_of_mem_riemannRochSpace {D : Divisor K F} {g : F} (hg : g ∈ riemannRochSpace D)
    (v : Place K F) (hv : D v = 0) : g = 0 ∨ 0 ≤ v.ord g := by
  have h := (mem_riemannRochSpace_iff.mp hg) v
  rw [hv, neg_zero] at h
  exact h

theorem riemannRochSpace_mono {D D' : Divisor K F} (h : ∀ v, D v ≤ D' v) :
    riemannRochSpace D ≤ riemannRochSpace D' := by
  intro g hg
  rw [mem_riemannRochSpace_iff] at hg ⊢
  intro v
  rcases hg v with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (le_trans (neg_le_neg (h v)) h1)

theorem surjective_algebraMap_residueField [IsAlgClosed K] [IsCurveOver K F] (v : Place K F) :
    Function.Surjective (algebraMap K v.ResidueField) := by
  haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
  haveI : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := v.ResidueField)).2

theorem exists_hasValue_of_mem [IsAlgClosed K] [IsCurveOver K F] (v : Place K F) {g : F}
    (hmem : g ∈ v.toValuationSubring) : ∃ a : K, v.HasValue g a := by
  obtain ⟨a, ha, -⟩ := v.exists_hasValue_of_surjective (surjective_algebraMap_residueField v) hmem
  exact ⟨a, ha⟩

theorem degree_sum_single [IsAlgClosed K] [IsCurveOver K F] (S : Finset (Place K F)) :
    Divisor.degree (∑ u ∈ S, Finsupp.single u (1 : ℤ)) = S.card := by
  rw [map_sum]
  simp_rw [Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed]
  simp

open Classical in
theorem sum_single_apply (S : Finset (Place K F)) (v : Place K F) :
    (∑ u ∈ S, Finsupp.single u (1 : ℤ)) v = if v ∈ S then 1 else 0 := by
  classical
  rw [Finset.sum_apply']
  simp_rw [Finsupp.single_apply]
  rw [Finset.sum_ite_eq' S v]

end PlaceValues

section Curve

variable {k F : Type*} [Field k] [IsAlgClosed k] [Field F] [Algebra k F] [IsCurveOver k F]

def val (v : Place k F) (g : F) (hg : g ∈ v.toValuationSubring) : k :=
  Classical.choose (exists_hasValue_of_mem v hg)

theorem hasValue_val (v : Place k F) (g : F) (hg : g ∈ v.toValuationSubring) :
    v.HasValue g (val v g hg) :=
  Classical.choose_spec (exists_hasValue_of_mem v hg)

private theorem _root_.AlgebraicCurve.Place.HasValue.eq_val {v : Place k F} {g : F} {a : k} (h : v.HasValue g a)
    (hg : g ∈ v.toValuationSubring) : a = val v g hg :=
  h.unique (hasValue_val v g hg)

p2m_alias "P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_isCurveOver_of_essFiniteType.AlgebraicCurve.Place.HasValue.eq_val" "AlgebraicCurve.Place.HasValue.eq_val"

def evalAt (D : Divisor k F) (v : Place k F) (hv : D v = 0) : riemannRochSpace D →ₗ[k] k where
  toFun g := val v (g : F) (mem_of v (ord_nonneg_of_mem_riemannRochSpace g.2 v hv))
  map_add' g g' := by
    symm
    apply AlgebraicCurve.Place.HasValue.eq_val
    exact (hasValue_val v _ _).add (hasValue_val v _ _)
  map_smul' c g := by
    symm
    apply AlgebraicCurve.Place.HasValue.eq_val
    exact (hasValue_val v _ _).smul c

theorem hasValue_evalAt (D : Divisor k F) (v : Place k F) (hv : D v = 0) (g : riemannRochSpace D) :
    v.HasValue (g : F) (evalAt D v hv g) :=
  hasValue_val v (g : F) (mem_of v (ord_nonneg_of_mem_riemannRochSpace g.2 v hv))

theorem evalAt_eq_iff {D : Divisor k F} {v : Place k F} {hv : D v = 0} {g : riemannRochSpace D}
    {a : k} : evalAt D v hv g = a ↔ v.HasValue (g : F) a := by
  constructor
  · rintro rfl; exact hasValue_evalAt D v hv g
  · intro h; exact (h.eq_val (mem_of v (ord_nonneg_of_mem_riemannRochSpace g.2 v hv))).symm

end Curve

section Fibre

variable {k F : Type*} [Field k] [IsAlgClosed k] [Field F] [Algebra k F] [IsCurveOver k F] [Algebra.EssFiniteType k F]

theorem exists_mem_notMem_sub_single (D : Divisor k F) (hD : 2 * ((genusFF k F) : ℤ) ≤ D.degree)
    (x : Place k F) :
    ∃ h : F, h ∈ riemannRochSpace D ∧ h ∉ riemannRochSpace (D - Finsupp.single x (1 : ℤ)) := by
  classical
  have hdeg' : (D - Finsupp.single x (1 : ℤ)).degree = D.degree - 1 := by
    rw [map_sub, Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed]; simp
  obtain ⟨xs, hxs, hfin, hsep⟩ := AlgebraicCurve.IsCurveOver.exists_separating_transcendental (K := k) (F := F)
  have h1 := AlgebraicCurve.ell_eq_degree_add_one_sub_genusFF_of_isAlgClosed_of_isSeparable k xs hxs hfin hsep D (by linarith)
  have h2 := AlgebraicCurve.ell_eq_degree_add_one_sub_genusFF_of_isAlgClosed_of_isSeparable k xs hxs hfin hsep
    (D - Finsupp.single x (1 : ℤ)) (by rw [hdeg']; linarith)
  have hlt : ell (D - Finsupp.single x (1 : ℤ)) < ell D := by
    have : (ell (D - Finsupp.single x (1 : ℤ)) : ℤ) < (ell D : ℤ) := by rw [h1, h2, hdeg']; linarith
    exact_mod_cast this

  have hpos : 0 < ell D := lt_of_le_of_lt (Nat.zero_le _) hlt
  haveI : Module.Finite k (LSpace D) := Module.finite_of_finrank_pos hpos
  by_contra hcon
  push_neg at hcon
  have hle : LSpace D ≤ LSpace (D - Finsupp.single x (1 : ℤ)) := fun h hh => hcon h hh
  have hge : LSpace (D - Finsupp.single x (1 : ℤ)) ≤ LSpace D :=
    lSpace_mono (by intro v; simp only [Finsupp.coe_sub, Pi.sub_apply]; linarith [show (0:ℤ) ≤ Finsupp.single x (1:ℤ) v from by rw [Finsupp.single_apply]; split_ifs <;> norm_num])
  have heq : LSpace (D - Finsupp.single x (1 : ℤ)) = LSpace D := le_antisymm hge hle
  rw [show ell (D - Finsupp.single x (1 : ℤ)) = ell D from by rw [ell, ell, heq]] at hlt
  exact lt_irrefl _ hlt

theorem exists_delta (D : Divisor k F) (hD : 2 * ((genusFF k F) : ℤ) ≤ D.degree) (x : Place k F)
    (hx : D x = 0) :
    ∃ h : riemannRochSpace D, evalAt D x hx h ≠ 0 := by
  classical
  obtain ⟨h, hL, hnot⟩ := exists_mem_notMem_sub_single D hD x
  refine ⟨⟨h, hL⟩, fun h0 => hnot ?_⟩
  have hval : x.HasValue h 0 := evalAt_eq_iff.mp h0
  rw [mem_riemannRochSpace_iff]
  intro v
  by_cases hh : h = 0
  · exact Or.inl hh
  · right
    rcases (mem_riemannRochSpace_iff.mp hL) v with h0' | hv
    · exact absurd h0' hh
    · rw [Finsupp.sub_apply]
      by_cases hxv : x = v
      · subst hxv
        rw [Finsupp.single_eq_same, hx]
        have := ord_pos_of_hasValue_zero x hh hval
        linarith
      · rw [Finsupp.single_apply, if_neg hxv]
        simpa using hv

end Fibre

section Main

variable {k F : Type*} [Field k] [IsAlgClosed k] [Field F] [Algebra k F] [IsCurveOver k F] [Algebra.EssFiniteType k F]

theorem main
    (U Zv Za : Finset (Place k F)) (t₀ : Place k F) (β : k)
    (val₀ : Place k F → k) (bad : Finset k)
    (hUZv : Disjoint U Zv) (hUZa : Disjoint U Za) (hZ : Disjoint Zv Za)
    (ht₀U : t₀ ∉ U) (ht₀v : t₀ ∉ Zv) (ht₀a : t₀ ∉ Za)
    (hcard : Zv.card + 2 * (genusFF k F) + 2 ≤ U.card) :
    ∃ g : F,
      g ∈ riemannRochSpace (∑ u ∈ U, Finsupp.single u (1 : ℤ)) ∧
      t₀.ord (g - algebraMap k F β) = 1 ∧
      (∀ z ∈ Zv, z.HasValue g (val₀ z)) ∧
      (∀ z ∈ Za, ∃ γ : k, γ ∉ bad ∧ z.HasValue g γ) := by
  classical
  haveI : Infinite k := IsAlgClosed.instInfinite

  set E : Divisor k F := ∑ u ∈ U, Finsupp.single u (1 : ℤ) with hE
  set P : Finset (Place k F) := insert t₀ Zv with hP
  set EP : Divisor k F := E - ∑ s ∈ P, Finsupp.single s (1 : ℤ) with hEP
  set EP2 : Divisor k F := EP - Finsupp.single t₀ (1 : ℤ) with hEP2
  have hEapp : ∀ v, E v = if v ∈ U then 1 else 0 := fun v => by rw [hE, sum_single_apply]
  have hPcard : P.card = Zv.card + 1 := by rw [hP, Finset.card_insert_of_notMem ht₀v]
  have hPU : Disjoint U P := by
    rw [hP, Finset.disjoint_insert_right]; exact ⟨ht₀U, hUZv⟩
  have hdegE : E.degree = U.card := degree_sum_single U
  have hdegEP : EP.degree = U.card - P.card := by
    rw [hEP, map_sub, hdegE, degree_sum_single]
  have hdegEP2 : EP2.degree = U.card - P.card - 1 := by
    rw [hEP2, map_sub, hdegEP, Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed]; simp
  have hEPapp : ∀ v, EP v = (if v ∈ U then 1 else 0) - (if v ∈ P then 1 else 0) := fun v => by
    rw [hEP, Finsupp.sub_apply, hEapp, sum_single_apply]
  have hEP2app : ∀ v, EP2 v = (if v ∈ U then 1 else 0) - (if v ∈ P then 1 else 0)
      - (if v = t₀ then 1 else 0) := fun v => by
    rw [hEP2, Finsupp.sub_apply, hEPapp, Finsupp.single_apply]
    by_cases h : v = t₀
    · subst h; simp
    · simp [h, Ne.symm h]
  have hgg : (2 : ℤ) * (genusFF k F) ≤ U.card - P.card - 1 := by
    have : (Zv.card : ℤ) + 2 * (genusFF k F) + 2 ≤ U.card := by exact_mod_cast hcard
    rw [hPcard]; push_cast; linarith

  have hstep1 : ∀ z ∈ P, ∃ h : F, h ∈ riemannRochSpace E ∧
      (∀ z' ∈ P, z' ≠ z → z'.HasValue h 0) ∧ ∃ a : k, a ≠ 0 ∧ z.HasValue h a := by
    intro z hz
    set Dz : Divisor k F := E - ∑ s ∈ P.erase z, Finsupp.single s (1 : ℤ) with hDz
    have hDzapp : ∀ v, Dz v = (if v ∈ U then 1 else 0) - (if v ∈ P.erase z then 1 else 0) :=
      fun v => by rw [hDz, Finsupp.sub_apply, hEapp, sum_single_apply]
    have hzU : z ∉ U := Finset.disjoint_right.mp hPU hz
    have hDzz : Dz z = 0 := by rw [hDzapp]; simp [hzU]
    have hdegDz : (2 : ℤ) * (genusFF k F) ≤ Dz.degree := by
      rw [hDz, map_sub, hdegE, degree_sum_single, Finset.card_erase_of_mem hz]
      have h1 : 1 ≤ P.card := Finset.card_pos.mpr ⟨z, hz⟩
      push_cast [h1]
      linarith
    obtain ⟨⟨h, hL⟩, hne⟩ := exists_delta Dz hdegDz z hDzz
    refine ⟨h, riemannRochSpace_mono (fun v => ?_) hL, fun z' hz' hne' => ?_, ⟨_, hne, hasValue_evalAt Dz z hDzz ⟨h, hL⟩⟩⟩
    · rw [hDzapp, hEapp]; split_ifs <;> norm_num
    ·
      have hz'U : z' ∉ U := Finset.disjoint_right.mp hPU hz'
      have hcoef : Dz z' = -1 := by
        rw [hDzapp]; simp [hz'U, Finset.mem_erase, hne', hz']
      rcases (mem_riemannRochSpace_iff.mp hL) z' with h0 | hord
      · rw [h0]; simpa using z'.hasValue_algebraMap (0 : k)
      · rw [hcoef, neg_neg] at hord
        exact hasValue_of_ord_sub_pos z' (by simp at hord ⊢; exact hord)
  choose! hδ hδL hδ0 aδ haδ hδa using hstep1

  let c : Place k F → k := fun z => if z = t₀ then β else val₀ z
  set g₁ : F := ∑ z ∈ P, (c z / aδ z) • hδ z with hg₁
  have hg₁L : g₁ ∈ riemannRochSpace E := by
    refine Submodule.sum_mem _ fun z hz => Submodule.smul_mem _ _ (hδL z hz)
  have hg₁val : ∀ z ∈ P, z.HasValue g₁ (c z) := by
    intro z hz
    rw [hg₁, ← Finset.add_sum_erase P _ hz]
    have hmain : z.HasValue ((c z / aδ z) • hδ z) (c z) := by
      have := (hδa z hz).smul (c z / aδ z)
      rwa [div_mul_cancel₀ _ (haδ z hz)] at this
    have hrest : z.HasValue (∑ x ∈ P.erase z, (c x / aδ x) • hδ x) 0 := by
      refine hasValue_sum_zero z (P.erase z) _ fun x hx => ?_
      have hxP := Finset.mem_of_mem_erase hx
      have hxz : z ≠ x := fun h => (Finset.notMem_erase x P) (h ▸ hx)
      have := (hδ0 x hxP z hz hxz).smul (c x / aδ x)
      rwa [mul_zero] at this
    have := hmain.add hrest
    rwa [add_zero] at this

  have hEPt₀ : EP t₀ = -1 := by
    rw [hEPapp]; simp [ht₀U, hP]
  have hdegEPge : (2 : ℤ) * (genusFF k F) ≤ EP.degree := by rw [hdegEP]; linarith
  obtain ⟨h₀, hh₀L, hh₀not⟩ := exists_mem_notMem_sub_single EP hdegEPge t₀
  have hh₀ne : h₀ ≠ 0 := by
    intro h; apply hh₀not; rw [h]; exact Submodule.zero_mem _
  have hh₀ord : t₀.ord h₀ = 1 := by
    rcases (mem_riemannRochSpace_iff.mp hh₀L) t₀ with h | h
    · exact absurd h hh₀ne
    · rw [hEPt₀, neg_neg] at h

      by_contra hne1
      apply hh₀not
      rw [mem_riemannRochSpace_iff]
      intro v
      right
      rcases (mem_riemannRochSpace_iff.mp hh₀L) v with h' | h'
      · exact absurd h' hh₀ne
      · simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_apply]
        split_ifs with htv
        · subst htv; rw [hEPt₀]; omega
        · simpa using h'

  have hEP_le_E : riemannRochSpace EP ≤ riemannRochSpace E := riemannRochSpace_mono (fun v => by
    rw [hEPapp, hEapp]; split_ifs <;> norm_num)
  have hEP2_le_EP : riemannRochSpace EP2 ≤ riemannRochSpace EP := riemannRochSpace_mono (fun v => by
    rw [hEP2app, hEPapp]; split_ifs <;> norm_num)
  have hvanP : ∀ w ∈ riemannRochSpace EP, ∀ z ∈ P, z.HasValue w 0 := by
    intro w hw z hz
    have hzU : z ∉ U := Finset.disjoint_right.mp hPU hz
    rcases (mem_riemannRochSpace_iff.mp hw) z with h0 | hord
    · rw [h0]; simpa using z.hasValue_algebraMap (0 : k)
    · rw [hEPapp] at hord
      simp only [hzU, hz, if_false, if_true, zero_sub, neg_neg] at hord
      exact hasValue_of_ord_sub_pos z (by simp at hord ⊢; exact hord)

  set r : F := g₁ - algebraMap k F β with hr
  have ht₀P : t₀ ∈ P := by rw [hP]; exact Finset.mem_insert_self _ _
  have hrval : t₀.HasValue r 0 := by
    have := (hg₁val t₀ ht₀P).sub (t₀.hasValue_algebraMap β)
    simp only [c, if_true, sub_self] at this
    exact this
  set q : F := r * h₀⁻¹ with hq
  have hqmem : q ∈ t₀.toValuationSubring := by
    by_cases hr0 : r = 0
    · rw [hq, hr0, zero_mul]; exact zero_mem _
    · apply mem_of_ord_nonneg' t₀ (mul_ne_zero hr0 (inv_ne_zero hh₀ne))
      rw [t₀.ord_mul hr0 (inv_ne_zero hh₀ne), t₀.ord_inv, hh₀ord]
      have := ord_pos_of_hasValue_zero t₀ hr0 hrval
      omega
  obtain ⟨ρ, hρ⟩ := exists_hasValue_of_mem t₀ hqmem
  set a : k := 1 - ρ with ha
  have hqa : t₀.HasValue (q + algebraMap k F a) 1 := by
    have := hρ.add (t₀.hasValue_algebraMap a)
    rwa [ha, add_sub_cancel] at this
  have hqa0 : q + algebraMap k F a ≠ 0 := by
    intro h0
    have h1 : t₀.HasValue (q + algebraMap k F a) 0 := by
      rw [h0]; simpa using t₀.hasValue_algebraMap (0 : k)
    exact one_ne_zero (hqa.unique h1)
  have hfactor : r + a • h₀ = h₀ * (q + algebraMap k F a) := by
    rw [hq, mul_add, ← mul_assoc, mul_comm h₀ r, mul_assoc, mul_inv_cancel₀ hh₀ne, mul_one,
      Algebra.smul_def, mul_comm]
  have hord1 : t₀.ord (r + a • h₀) = 1 := by
    rw [hfactor, t₀.ord_mul hh₀ne hqa0, hh₀ord, hqa.ord_eq_zero one_ne_zero, add_zero]
  have hra0 : r + a • h₀ ≠ 0 := by rw [hfactor]; exact mul_ne_zero hh₀ne hqa0
  set x₁ : F := g₁ + a • h₀ with hx₁
  have hx₁L : x₁ ∈ riemannRochSpace E :=
    add_mem hg₁L (Submodule.smul_mem _ _ (hEP_le_E hh₀L))
  have hx₁val : ∀ z ∈ P, z.HasValue x₁ (c z) := by
    intro z hz
    have := (hg₁val z hz).add ((hvanP h₀ hh₀L z hz).smul a)
    rwa [mul_zero, add_zero] at this
  have hx₁β : x₁ - algebraMap k F β = r + a • h₀ := by rw [hx₁, hr]; abel

  have hEP2_of_Za : ∀ y ∈ Za, EP2 y = 0 := by
    intro y hy
    have hyU : y ∉ U := Finset.disjoint_right.mp hUZa hy
    have hyZv : y ∉ Zv := Finset.disjoint_right.mp hZ hy
    have hyt : y ≠ t₀ := fun h => ht₀a (h ▸ hy)
    have hyP : y ∉ P := by rw [hP, Finset.mem_insert]; push_neg; exact ⟨hyt, hyZv⟩
    rw [hEP2app]; simp [hyU, hyP, hyt]
  have hdegEP2ge : (2 : ℤ) * (genusFF k F) ≤ EP2.degree := by rw [hdegEP2]; linarith

  let ψ : Place k F × k → (riemannRochSpace EP2 →ₗ[k] k) := fun yb =>
    if hy : yb.1 ∈ Za then evalAt EP2 yb.1 (hEP2_of_Za yb.1 hy) else 0
  have hψ : ∀ yb ∈ Za ×ˢ bad, ψ yb ≠ 0 := by
    rintro ⟨y, b⟩ hyb
    obtain ⟨hy, -⟩ := Finset.mem_product.mp hyb
    simp only [ψ, hy, dif_pos]
    obtain ⟨h, hne⟩ := exists_delta EP2 hdegEP2ge y (hEP2_of_Za y hy)
    intro h0
    rw [h0] at hne
    exact hne rfl

  have hx₁mem : ∀ y ∈ Za, x₁ ∈ y.toValuationSubring := by
    intro y hy
    have hyU : y ∉ U := Finset.disjoint_right.mp hUZa hy
    exact mem_of y (ord_nonneg_of_mem_riemannRochSpace hx₁L y (by rw [hEapp]; simp [hyU]))
  let cst : Place k F × k → k := fun yb =>
    if hy : yb.1 ∈ Za then yb.2 - val yb.1 x₁ (hx₁mem yb.1 hy) else 0
  obtain ⟨w, hw⟩ := exists_forall_apply_ne (Za ×ˢ bad) ψ cst hψ 0

  refine ⟨x₁ + (w : F), ?_, ?_, ?_, ?_⟩
  · exact add_mem hx₁L (hEP_le_E (hEP2_le_EP w.2))
  ·
    rw [show x₁ + (w : F) - algebraMap k F β = (r + a • h₀) + (w : F) by rw [← hx₁β]; abel]
    by_cases hw0 : (w : F) = 0
    · rw [hw0, add_zero, hord1]
    · rw [ord_add_eq_of_lt t₀ hra0 hw0 (by
        rw [hord1]
        rcases (mem_riemannRochSpace_iff.mp w.2) t₀ with h | h
        · exact absurd h hw0
        · rw [hEP2app] at h
          simp only [ht₀U, ht₀P, if_false, if_true] at h
          linarith), hord1]
  ·
    intro z hz
    have hzP : z ∈ P := by rw [hP]; exact Finset.mem_insert_of_mem hz
    have hzt : z ≠ t₀ := fun h => ht₀v (h ▸ hz)
    have h1 := hx₁val z hzP
    simp only [c, hzt, if_false] at h1
    have := h1.add (hvanP _ (hEP2_le_EP w.2) z hzP)
    rwa [add_zero] at this
  ·
    intro y hy
    refine ⟨val y x₁ (hx₁mem y hy) + evalAt EP2 y (hEP2_of_Za y hy) w, fun hb => ?_, ?_⟩
    · have h := hw ⟨y, _⟩ (Finset.mem_product.mpr ⟨hy, hb⟩)
      simp only [ψ, cst, hy, dif_pos, zero_add] at h
      apply h
      ring
    · exact (hasValue_val y x₁ (hx₁mem y hy)).add (hasValue_evalAt EP2 y _ w)

end Main

end AlgebraicCurve.InterpGen

end

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_isCurveOver_of_essFiniteType.AlgebraicCurve in
theorem solution
    (k F : Type*) [Field k] [IsAlgClosed k] [Field F] [Algebra k F] [IsCurveOver k F] [Algebra.EssFiniteType k F]
    (U Zv Za : Finset (Place k F)) (t₀ : Place k F) (β : k)
    (val : Place k F → k) (bad : Finset k)
    (hUZv : Disjoint U Zv) (hUZa : Disjoint U Za) (hZ : Disjoint Zv Za)
    (ht₀U : t₀ ∉ U) (ht₀v : t₀ ∉ Zv) (ht₀a : t₀ ∉ Za)
    (hcard : Zv.card + 2 * genusFF k F + 2 ≤ U.card) :
    ∃ g : F,
      g ∈ riemannRochSpace (∑ u ∈ U, Finsupp.single u (1 : ℤ)) ∧
      t₀.ord (g - algebraMap k F β) = 1 ∧
      (∀ z ∈ Zv, z.HasValue g (val z)) ∧
      (∀ z ∈ Za, ∃ γ : k, γ ∉ bad ∧ z.HasValue g γ) :=
  AlgebraicCurve.InterpGen.main U Zv Za t₀ β val bad hUZv hUZa hZ ht₀U ht₀v ht₀a hcard

end S_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_isCurveOver_of_essFiniteType
end P2MW
export P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_isCurveOver_of_essFiniteType (solution)
