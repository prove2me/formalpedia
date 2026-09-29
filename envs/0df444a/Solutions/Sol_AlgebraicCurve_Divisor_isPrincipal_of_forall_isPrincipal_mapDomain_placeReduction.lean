-- Prove2me | solution 1 for AlgebraicCurve.Divisor.isPrincipal_of_forall_isPrincipal_mapDomain_placeReduction
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/7e6cd452-c89b-5a60-bdaa-33c8aadb4ff6

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_IsAlgClosed_exists_valuationSubring_ringHom_retraction_forall_valuation_eq_one
import Theorems.Thm_AlgebraicCurve_Divisor_exists_finset_finrank_riemannRochSpace_mapDomain_placeReduction_eq
import Theorems.Thm_AlgebraicCurve_Place_exists_of_valuationSubring
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Divisor_isPrincipal_of_forall_isPrincipal_mapDomain_placeReduction
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one"
p2m_attr_erase "simp" "ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe"
p2m_attr_erase "simp" "AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Divisor_isPrincipal_of_forall_isPrincipal_mapDomain_placeReduction.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor Divisor.IsPrincipal HasPrincipalDivisors HasPrincipalDivisors.exists_divisor IsCurveOver IsCurveOver.forall_deg_eq_one_of_isAlgClosed IsCurveOver.finiteResidue riemannRochSpace mem_riemannRochSpace_iff Divisor.exists_finset_finrank_riemannRochSpace_mapDomain_placeReduction_eq Place.exists_of_valuationSubring"
namespace SpecializationPrincipleAux
p2m_open "AlgebraicCurve"

open IsLocalRing

universe uK uF uE uFE

section PlaceFacts

variable {K : Type uK} {F : Type uF} [Field K] [Field F] [Algebra K F]

theorem mem_of_ord_nonneg (v : Place K F) {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h
  rw [hu, hn, zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem π.2 n)

theorem ord_coe_nonneg (v : Place K F) (f : v.toValuationSubring) : 0 ≤ v.ord (f : F) := by
  by_cases hf : f = 0
  · simp [hf]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hf hπ
  have : (f : F) = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    rw [hu, zpow_natCast]; push_cast; rfl
  rw [this, v.ord_unit_smul_zpow u hπ]
  exact Int.natCast_nonneg n

theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) :
    0 ≤ v.ord f :=
  ord_coe_nonneg v ⟨f, hf⟩

theorem one_le_ord_of_mem_maximalIdeal (v : Place K F) {f : v.toValuationSubring} (hf : f ≠ 0)
    (hm : f ∈ maximalIdeal v.toValuationSubring) : 1 ≤ v.ord (f : F) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hf hπ
  have : (f : F) = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    rw [hu, zpow_natCast]; push_cast; rfl
  rw [this, v.ord_unit_smul_zpow u hπ]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · exfalso
    rw [hn, pow_zero, mul_one] at hu
    exact (IsLocalRing.mem_maximalIdeal _ |>.1 hm) (hu ▸ u.isUnit)
  · exact_mod_cast hn

theorem isUnit_algebraMap (v : Place K F) {c : K} (hc : c ≠ 0) :
    IsUnit (⟨algebraMap K F c, v.algebraMap_mem' c⟩ : v.toValuationSubring) := by
  refine IsUnit.of_mul_eq_one ⟨algebraMap K F c⁻¹, v.algebraMap_mem' c⁻¹⟩ ?_
  ext
  simp [hc]

theorem ord_algebraMap (v : Place K F) (c : K) : v.ord (algebraMap K F c) = 0 := by
  by_cases hc : c = 0
  · simp [hc]
  · obtain ⟨u, hu⟩ := isUnit_algebraMap v hc
    have := v.ord_coe_unit u
    rwa [hu] at this

theorem degree_eq_sum (hdeg : ∀ v : Place K F, v.deg = 1) (G : Divisor K F) :
    G.degree = G.sum fun _ n => n := by
  show (Finsupp.liftAddHom _) G = _
  rw [Finsupp.liftAddHom_apply]
  simp [hdeg]

theorem le_degree (hdeg : ∀ v : Place K F, v.deg = 1) (G : Divisor K F) (hG : ∀ v, 0 ≤ G v)
    (v : Place K F) : G v ≤ G.degree := by
  rw [degree_eq_sum hdeg]
  by_cases hv : v ∈ G.support
  · exact Finset.single_le_sum (f := fun w => G w) (fun w _ => hG w) hv
  · rw [Finsupp.notMem_support_iff.1 hv]
    exact Finset.sum_nonneg fun w _ => hG w

theorem eq_zero_of_degree_eq_zero (hdeg : ∀ v : Place K F, v.deg = 1) (G : Divisor K F)
    (hG : ∀ v, 0 ≤ G v) (h0 : G.degree = 0) : G = 0 := by
  ext v
  have hle := le_degree hdeg G hG v
  rw [h0] at hle
  exact le_antisymm hle (hG v)

variable [IsAlgClosed K] [IsCurveOver K F]

theorem mem_range_of_forall_ord_nonneg (v₀ : Place K F) {f : F} (hf : f ≠ 0)
    (h : ∀ v : Place K F, 0 ≤ v.ord f) : f ∈ Set.range (algebraMap K F) := by
  have hdeg := IsCurveOver.forall_deg_eq_one_of_isAlgClosed (K := K) (F := F)
  have hf₀ : f ∈ v₀.toValuationSubring := mem_of_ord_nonneg v₀ hf (h v₀)
  haveI : Module.Finite K v₀.ResidueField := IsCurveOver.finiteResidue v₀
  have : Algebra.IsIntegral K v₀.ResidueField := Algebra.IsIntegral.of_finite K _
  obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K)
    (K := v₀.ResidueField)).2 (residue _ ⟨f, hf₀⟩)
  have hmem : (⟨f, hf₀⟩ : v₀.toValuationSubring) - algebraMap K v₀.toValuationSubring c ∈
      maximalIdeal v₀.toValuationSubring := by
    rw [← Ideal.Quotient.eq]
    exact hc.symm
  by_cases hg : f - algebraMap K F c = 0
  · exact ⟨c, (sub_eq_zero.1 hg).symm⟩
  exfalso
  set g : F := f - algebraMap K F c with hg_def
  have hg1 : 1 ≤ v₀.ord g := by
    have hne : (⟨f, hf₀⟩ : v₀.toValuationSubring) - algebraMap K v₀.toValuationSubring c ≠ 0 := by
      intro h0
      apply hg
      have := congrArg Subtype.val h0
      simpa using this
    have := one_le_ord_of_mem_maximalIdeal v₀ hne hmem
    simpa using this
  have hg0 : ∀ v : Place K F, 0 ≤ v.ord g := fun v =>
    ord_nonneg_of_mem v (sub_mem (mem_of_ord_nonneg v hf (h v)) (v.algebraMap_mem' c))
  obtain ⟨Dg, hDg, hDg0⟩ := HasPrincipalDivisors.exists_divisor (K := K) g hg
  have hle := le_degree hdeg Dg (fun v => (hDg v).symm ▸ hg0 v) v₀
  rw [hDg0, hDg] at hle
  omega

theorem finrank_riemannRochSpace_ne_zero_of_isPrincipal (v₀ : Place K F) (D : Divisor K F)
    (hP : D.IsPrincipal) : Module.finrank K (riemannRochSpace D) ≠ 0 := by
  obtain ⟨φ, hφ0, hφ⟩ := hP
  have hle : riemannRochSpace D ≤ K ∙ φ⁻¹ := by
    intro g hg
    rw [mem_riemannRochSpace_iff] at hg
    by_cases hg0 : g = 0
    · simp [hg0]
    have hprod : ∀ v : Place K F, 0 ≤ v.ord (g * φ) := by
      intro v
      rw [v.ord_mul hg0 hφ0, ← hφ v]
      have := (hg v).resolve_left hg0
      omega
    obtain ⟨c, hc⟩ := mem_range_of_forall_ord_nonneg v₀ (mul_ne_zero hg0 hφ0) hprod
    rw [Submodule.mem_span_singleton]
    refine ⟨c, ?_⟩
    rw [Algebra.smul_def, hc]
    field_simp
  haveI : FiniteDimensional K (K ∙ φ⁻¹) := FiniteDimensional.span_of_finite K (Set.finite_singleton _)
  haveI : FiniteDimensional K (riemannRochSpace D) := Submodule.finiteDimensional_of_le hle
  intro h0
  have hbot := Submodule.finrank_eq_zero.1 h0
  have hmem : φ⁻¹ ∈ riemannRochSpace D := by
    rw [mem_riemannRochSpace_iff]
    intro v
    right
    rw [v.ord_inv, ← hφ v]
  rw [hbot, Submodule.mem_bot] at hmem
  exact inv_ne_zero hφ0 hmem

omit [IsAlgClosed K] in

theorem isPrincipal_of_riemannRochSpace_ne_bot (hdeg : ∀ v : Place K F, v.deg = 1)
    (D : Divisor K F) (hD : D.degree = 0) (hne : riemannRochSpace D ≠ ⊥) : D.IsPrincipal := by
  obtain ⟨f, hfL, hf0⟩ := (Submodule.ne_bot_iff _).1 hne
  rw [mem_riemannRochSpace_iff] at hfL
  obtain ⟨Df, hDf, hDf0⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
  have hG : ∀ v, 0 ≤ (Df + D) v := by
    intro v
    rw [Finsupp.add_apply, hDf v]
    have := (hfL v).resolve_left hf0
    omega
  have hG0 : (Df + D).degree = 0 := by rw [map_add, hDf0, hD, add_zero]
  have hzero := eq_zero_of_degree_eq_zero hdeg (Df + D) hG hG0
  refine ⟨f⁻¹, inv_ne_zero hf0, fun v => ?_⟩
  have := congrArg (fun G : Divisor K F => G v) hzero
  simp only [Finsupp.add_apply, Finsupp.coe_zero, Pi.zero_apply, hDf v] at this
  rw [v.ord_inv]
  omega

end PlaceFacts

section Reduction

variable {E : Type uE} {FE : Type uFE} [Field E] [Field FE] [Algebra E FE]

theorem valuation_algebraMap_eq_one (P : Place E FE) {e : E} (he : e ≠ 0) :
    P.toValuationSubring.valuation (algebraMap E FE e) = 1 := by
  have hu : IsUnit (⟨algebraMap E FE e, P.algebraMap_mem' e⟩ : P.toValuationSubring) := by
    refine IsUnit.of_mul_eq_one ⟨algebraMap E FE e⁻¹, P.algebraMap_mem' e⁻¹⟩ ?_
    ext
    simp [he]
  exact (ValuationSubring.valuation_eq_one_iff _ _).1 hu

theorem valuation_algebraMap_le_one (P : Place E FE) (e : E) :
    P.toValuationSubring.valuation (algebraMap E FE e) ≤ 1 :=
  (P.toValuationSubring.valuation_le_one_iff _).2 (P.algebraMap_mem' e)

theorem algebraMap_eq_of_valuation_sub_lt_one (P : Place E FE) {a b : E}
    (h : P.toValuationSubring.valuation (algebraMap E FE a - algebraMap E FE b) < 1) : a = b := by
  by_contra hab
  rw [← map_sub, valuation_algebraMap_eq_one P (sub_ne_zero.2 hab)] at h
  exact lt_irrefl _ h

theorem const_unique (P : Place E FE) {g : FE} {a b : E}
    (ha : P.toValuationSubring.valuation (g - algebraMap E FE a) < 1)
    (hb : P.toValuationSubring.valuation (g - algebraMap E FE b) < 1) : a = b := by
  refine algebraMap_eq_of_valuation_sub_lt_one P ?_
  have : algebraMap E FE a - algebraMap E FE b = (g - algebraMap E FE b) - (g - algebraMap E FE a) := by
    ring
  rw [this]
  exact Valuation.map_sub_lt _ hb ha

theorem mem_of_valuation_sub_lt_one (P : Place E FE) {g : FE} {a : E}
    (h : P.toValuationSubring.valuation (g - algebraMap E FE a) < 1) :
    g ∈ P.toValuationSubring := by
  rw [← ValuationSubring.valuation_le_one_iff]
  have : g = (g - algebraMap E FE a) + algebraMap E FE a := by ring
  rw [this]
  exact Valuation.map_add_le _ h.le (valuation_algebraMap_le_one P a)

theorem exists_valuation_sub_lt_one [IsAlgClosed E] (P : Place E FE)
    [Module.Finite E P.ResidueField] {g : FE} (hg : g ∈ P.toValuationSubring) :
    ∃ e : E, P.toValuationSubring.valuation (g - algebraMap E FE e) < 1 := by
  have : Algebra.IsIntegral E P.ResidueField := Algebra.IsIntegral.of_finite E _
  obtain ⟨e, he⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := E)
    (K := P.ResidueField)).2 (residue _ ⟨g, hg⟩)
  refine ⟨e, ?_⟩
  have hmem : (⟨g, hg⟩ : P.toValuationSubring) - algebraMap E P.toValuationSubring e ∈
      maximalIdeal P.toValuationSubring := by
    rw [← Ideal.Quotient.eq]
    exact he.symm
  have := (ValuationSubring.valuation_lt_one_iff _ _).1 hmem
  simpa using this

theorem valuation_eq_one_of_sub_lt_one (P : Place E FE) {g : FE} {e : E} (he0 : e ≠ 0)
    (h : P.toValuationSubring.valuation (g - algebraMap E FE e) < 1) :
    P.toValuationSubring.valuation g = 1 := by
  have h1 := valuation_algebraMap_eq_one P he0
  have : g = algebraMap E FE e + (g - algebraMap E FE e) := by ring
  rw [this, Valuation.map_add_eq_of_lt_left _ (by rwa [h1]), h1]

theorem valuation_inv_sub_inv_lt_one (P : Place E FE) {g : FE} {e : E} (he0 : e ≠ 0)
    (h : P.toValuationSubring.valuation (g - algebraMap E FE e) < 1) :
    P.toValuationSubring.valuation (g⁻¹ - algebraMap E FE e⁻¹) < 1 := by
  have hvg := valuation_eq_one_of_sub_lt_one P he0 h
  have hg0 : g ≠ 0 := by
    rintro rfl; rw [Valuation.map_zero] at hvg; exact zero_ne_one hvg
  have he' : algebraMap E FE e ≠ 0 := (map_ne_zero (algebraMap E FE)).2 he0
  have : g⁻¹ - algebraMap E FE e⁻¹ = -(g - algebraMap E FE e) * (g⁻¹ * (algebraMap E FE e)⁻¹) := by
    rw [map_inv₀]
    field_simp
    ring
  rw [this, Valuation.map_mul, Valuation.map_neg, Valuation.map_mul, Valuation.map_inv,
    Valuation.map_inv, hvg, valuation_algebraMap_eq_one P he0]
  simpa using h

variable (A : ValuationSubring E)

def compositeRing [IsAlgClosed E] (P : Place E FE) [Module.Finite E P.ResidueField] :
    ValuationSubring FE where
  carrier := {g | ∃ a : E, a ∈ A ∧ P.toValuationSubring.valuation (g - algebraMap E FE a) < 1}
  mul_mem' := by
    rintro g h ⟨a, haA, ha⟩ ⟨b, hbA, hb⟩
    refine ⟨a * b, mul_mem haA hbA, ?_⟩
    have hg1 : P.toValuationSubring.valuation g ≤ 1 :=
      (P.toValuationSubring.valuation_le_one_iff _).2 (mem_of_valuation_sub_lt_one P ha)
    have : g * h - algebraMap E FE (a * b) =
        g * (h - algebraMap E FE b) + algebraMap E FE b * (g - algebraMap E FE a) := by
      rw [map_mul]; ring
    rw [this]
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul]
      calc P.toValuationSubring.valuation g * P.toValuationSubring.valuation (h - algebraMap E FE b)
          ≤ 1 * P.toValuationSubring.valuation (h - algebraMap E FE b) :=
            mul_le_mul_left hg1 _
        _ < 1 := by rw [one_mul]; exact hb
    · rw [map_mul]
      calc P.toValuationSubring.valuation (algebraMap E FE b) *
            P.toValuationSubring.valuation (g - algebraMap E FE a)
          ≤ 1 * P.toValuationSubring.valuation (g - algebraMap E FE a) :=
            mul_le_mul_left (valuation_algebraMap_le_one P b) _
        _ < 1 := by rw [one_mul]; exact ha
  one_mem' := ⟨1, one_mem A, by simp⟩
  add_mem' := by
    rintro g h ⟨a, haA, ha⟩ ⟨b, hbA, hb⟩
    refine ⟨a + b, add_mem haA hbA, ?_⟩
    have : g + h - algebraMap E FE (a + b) = (g - algebraMap E FE a) + (h - algebraMap E FE b) := by
      rw [map_add]; ring
    rw [this]
    exact Valuation.map_add_lt _ ha hb
  zero_mem' := ⟨0, zero_mem A, by simp⟩
  neg_mem' := by
    rintro g ⟨a, haA, ha⟩
    refine ⟨-a, neg_mem haA, ?_⟩
    have : -g - algebraMap E FE (-a) = -(g - algebraMap E FE a) := by rw [map_neg]; ring
    rw [this, Valuation.map_neg]
    exact ha
  mem_or_inv_mem' := by
    intro g
    simp only [Set.mem_setOf_eq]
    by_cases hg : g ∈ P.toValuationSubring
    · obtain ⟨e, he⟩ := exists_valuation_sub_lt_one P hg
      by_cases heA : e ∈ A
      · exact Or.inl ⟨e, heA, he⟩
      · right
        have he0 : e ≠ 0 := by rintro rfl; exact heA (zero_mem A)
        have heinv : e⁻¹ ∈ A := (A.mem_or_inv_mem e).resolve_left heA
        exact ⟨e⁻¹, heinv, valuation_inv_sub_inv_lt_one P he0 he⟩
    ·
      right
      refine ⟨0, zero_mem A, ?_⟩
      have hg' : g⁻¹ ∈ P.toValuationSubring := (P.toValuationSubring.mem_or_inv_mem g).resolve_left hg
      have hg0 : g ≠ 0 := by rintro rfl; exact hg (zero_mem _)
      rcases P.toValuationSubring.valuation_lt_one_or_eq_one ⟨g⁻¹, hg'⟩ with hlt | heq
      · simpa using hlt
      · exfalso
        apply hg
        rw [← ValuationSubring.valuation_le_one_iff]
        have : P.toValuationSubring.valuation g⁻¹ = 1 := heq
        rw [Valuation.map_inv, inv_eq_one] at this
        exact this.le

variable [IsAlgClosed E]

theorem mem_compositeRing_iff (P : Place E FE) [Module.Finite E P.ResidueField] (g : FE) :
    g ∈ compositeRing A P ↔
      ∃ a : E, a ∈ A ∧ P.toValuationSubring.valuation (g - algebraMap E FE a) < 1 :=
  Iff.rfl

variable {K : Type uK} {F : Type uF} [Field K] [Field F] [Algebra K F] [Algebra K E] [Algebra F FE]
  [Algebra K FE] [IsScalarTower K E FE] [IsScalarTower K F FE]

def reducedRing (P : Place E FE) [Module.Finite E P.ResidueField] : ValuationSubring F :=
  (compositeRing A P).comap (algebraMap F FE)

theorem mem_reducedRing_iff (P : Place E FE) [Module.Finite E P.ResidueField] (f : F) :
    f ∈ reducedRing (F := F) A P ↔
      ∃ a : E, a ∈ A ∧
        P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE a) < 1 :=
  Iff.rfl

omit [IsAlgClosed E] in
theorem algebraMap_algebraMap_eq (k : K) :
    algebraMap F FE (algebraMap K F k) = algebraMap E FE (algebraMap K E k) :=
  (IsScalarTower.algebraMap_apply K F FE k).symm.trans (IsScalarTower.algebraMap_apply K E FE k)

theorem algebraMap_mem_reducedRing (hK : ∀ k : K, algebraMap K E k ∈ A) (P : Place E FE)
    [Module.Finite E P.ResidueField] (k : K) : algebraMap K F k ∈ reducedRing (F := F) A P :=
  ⟨algebraMap K E k, hK k, by
    rw [algebraMap_algebraMap_eq (E := E), sub_self, Valuation.map_zero]; exact zero_lt_one⟩

theorem reducedRing_ne_top (hK : ∀ k : K, algebraMap K E k ∈ A)
    (hrat : ∀ a : E, a ∈ A → ∃ k : K, A.valuation (a - algebraMap K E k) < 1)
    (P : Place E FE) [Module.Finite E P.ResidueField] {x : F} (hx : Transcendental K x) :
    reducedRing (F := F) A P ≠ ⊤ := by
  intro htop
  have hall : ∀ f : F, f ∈ reducedRing (F := F) A P := fun f => htop ▸ trivial
  obtain ⟨a, haA, ha⟩ := hall x
  obtain ⟨k, hk⟩ := hrat a haA

  set y : F := x - algebraMap K F k with hy_def
  set b : E := a - algebraMap K E k with hb_def
  have hy0 : y ≠ 0 := by
    intro h0
    apply hx
    rw [sub_eq_zero.1 h0]
    exact isAlgebraic_algebraMap k
  have hyb : P.toValuationSubring.valuation (algebraMap F FE y - algebraMap E FE b) < 1 := by
    have : algebraMap F FE y - algebraMap E FE b = algebraMap F FE x - algebraMap E FE a := by
      simp only [hy_def, hb_def, map_sub, algebraMap_algebraMap_eq (E := E)]
      ring
    rwa [this]
  have hbA : b ∈ A := sub_mem haA (hK k)
  have hb1 : A.valuation b < 1 := hk
  obtain ⟨c, hcA, hc⟩ := hall y⁻¹
  rw [map_inv₀] at hc
  have hyFE0 : algebraMap F FE y ≠ 0 := (map_ne_zero _).2 hy0
  by_cases hb0 : b = 0
  ·
    rw [hb0, map_zero, sub_zero] at hyb
    have hinv : P.toValuationSubring.valuation (algebraMap F FE y)⁻¹ ≤ 1 :=
      (P.toValuationSubring.valuation_le_one_iff _).2 (mem_of_valuation_sub_lt_one P hc)
    have h1 : (1 : _) = P.toValuationSubring.valuation (algebraMap F FE y) *
        P.toValuationSubring.valuation (algebraMap F FE y)⁻¹ := by
      rw [← Valuation.map_mul, mul_inv_cancel₀ hyFE0, Valuation.map_one]
    have : (1 : _) ≤ P.toValuationSubring.valuation (algebraMap F FE y) := by
      calc (1 : _) = _ := h1
        _ ≤ P.toValuationSubring.valuation (algebraMap F FE y) * 1 := mul_le_mul_right hinv _
        _ = _ := mul_one _
    exact absurd hyb (not_lt.2 this)
  ·
    have hc' := valuation_inv_sub_inv_lt_one P hb0 hyb
    have hcb : c = b⁻¹ := const_unique P hc hc'
    have hunit : IsUnit (⟨b, hbA⟩ : A) := by
      refine IsUnit.of_mul_eq_one ⟨b⁻¹, hcb ▸ hcA⟩ ?_
      ext
      simp [hb0]
    have := (ValuationSubring.valuation_eq_one_iff _ _).1 hunit
    rw [show ((⟨b, hbA⟩ : A) : E) = b from rfl] at this
    rw [this] at hb1
    exact lt_irrefl _ hb1

theorem exists_placeReduction [CharZero K] [IsCurveOver E FE]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hK : ∀ k : K, algebraMap K E k ∈ A)
    (hrat : ∀ a : E, a ∈ A → ∃ k : K, A.valuation (a - algebraMap K E k) < 1) :
    ∃ r : Place E FE → Place K F, ∀ (P : Place E FE) (f : F), f ∈ (r P).toValuationSubring ↔
      ∃ a : E, a ∈ A ∧
        P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE a) < 1 := by
  obtain ⟨x, hx, hfin⟩ := hfg
  haveI := hfin
  have hex : ∀ P : Place E FE, ∃ v : Place K F,
      v.toValuationSubring = @reducedRing E FE _ _ _ A _ F _ _ P (IsCurveOver.finiteResidue P) := by
    intro P
    haveI : Module.Finite E P.ResidueField := IsCurveOver.finiteResidue P
    exact Place.exists_of_valuationSubring x (reducedRing (F := F) A P)
      (algebraMap_mem_reducedRing A hK P) (reducedRing_ne_top A hK hrat P hx)
  choose r hr using hex
  refine ⟨r, fun P f => ?_⟩
  rw [hr P]
  exact @mem_reducedRing_iff E FE _ _ _ A _ F _ _ P (IsCurveOver.finiteResidue P) f

end Reduction

end AlgebraicCurve.SpecializationPrincipleAux

open AlgebraicCurve.SpecializationPrincipleAux in
theorem solution
    (K F E FE : Type*) [Field K] [Field F] [Field E] [Field FE] [Algebra K F] [Algebra E FE]
    [Algebra K E] [Algebra F FE] [Algebra K FE] [IsScalarTower K E FE] [IsScalarTower K F FE]
    [IsAlgClosed K] [CharZero K] [IsAlgClosed E]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    [IsCurveOver K F] [IsCurveOver E FE]
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (D : Divisor E FE) (hD : D.degree = 0)
    (h : ∀ (A : ValuationSubring E) (r : Place E FE → Place K F),
      (∀ k : K, algebraMap K E k ∈ A) →
      (∀ a : E, a ∈ A → ∃ k : K, A.valuation (a - algebraMap K E k) < 1) →
      (∀ (P : Place E FE) (f : F), f ∈ (r P).toValuationSubring ↔
        ∃ a : E, a ∈ A ∧
          P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE a) < 1) →
      Divisor.IsPrincipal (K := K) (F := F) (Finsupp.mapDomain r D)) :
    D.IsPrincipal := by
  by_contra hnp

  have hbot : riemannRochSpace D = ⊥ := by
    by_contra hne
    exact hnp (isPrincipal_of_riemannRochSpace_ne_bot
      (IsCurveOver.forall_deg_eq_one_of_isAlgClosed (K := E) (F := FE)) D hD hne)
  have hfin0 : Module.finrank E (riemannRochSpace D) = 0 := by rw [hbot, finrank_bot]

  have hD0 : D ≠ 0 := by
    rintro rfl
    exact hnp ⟨1, one_ne_zero, fun v => by simp⟩
  obtain ⟨P₀, hP₀⟩ : ∃ P₀ : Place E FE, P₀ ∈ D.support := by
    by_contra hno
    push Not at hno
    exact hD0 (Finsupp.support_eq_empty.1 (Finset.eq_empty_of_forall_notMem hno))

  obtain ⟨S, hS0, hS⟩ :=
    AlgebraicCurve.Divisor.exists_finset_finrank_riemannRochSpace_mapDomain_placeReduction_eq
      K F E FE hfg hfgE hgen D
  obtain ⟨A, hK, σ, hker, hsec, hunits⟩ :=
    IsAlgClosed.exists_valuationSubring_ringHom_retraction_forall_valuation_eq_one K E S hS0
  have hrat : ∀ a : E, a ∈ A → ∃ k : K, A.valuation (a - algebraMap K E k) < 1 := by
    intro a ha
    refine ⟨σ ⟨a, ha⟩, ?_⟩
    have hmem : (⟨a, ha⟩ : A) - ⟨algebraMap K E (σ ⟨a, ha⟩), hK _⟩ ∈ RingHom.ker σ := by
      rw [RingHom.mem_ker, map_sub, hsec, sub_self]
    rw [hker] at hmem
    exact (ValuationSubring.valuation_lt_one_iff _ _).1 hmem

  obtain ⟨r, hr⟩ := exists_placeReduction (F := F) (FE := FE) A hfg hK hrat
  have hℓ := hS A r hK hrat hunits hr
  rw [hfin0] at hℓ

  exact finrank_riemannRochSpace_ne_zero_of_isPrincipal (r P₀) (Finsupp.mapDomain r D)
    (h A r hK hrat hr) hℓ

end S_AlgebraicCurve_Divisor_isPrincipal_of_forall_isPrincipal_mapDomain_placeReduction
end P2MW
export P2MW.S_AlgebraicCurve_Divisor_isPrincipal_of_forall_isPrincipal_mapDomain_placeReduction (solution)
