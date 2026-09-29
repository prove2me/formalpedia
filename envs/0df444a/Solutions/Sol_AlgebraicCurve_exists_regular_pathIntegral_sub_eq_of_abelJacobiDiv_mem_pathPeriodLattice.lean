-- Prove2me | solution 1 for AlgebraicCurve.exists_regular_pathIntegral_sub_eq_of_abelJacobiDiv_mem_pathPeriodLattice
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/4657144e-a81d-5d6b-8aa1-e6d73618452f

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_ComplexLineIntegral
import Theorems.Thm_AlgebraicCurve_exists_loops_pathIntegral_reciprocity
import Theorems.Thm_AlgebraicCurve_span_real_pathPeriodLattice_eq_top
import Theorems.Thm_AlgebraicCurve_exists_isPrimitiveAlong_of_mem_regularDifferentials
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_regular_pathIntegral_sub_eq_of_abelJacobiDiv_mem_pathPeriodLattice
p2m_attr_erase "instance" "AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers"
p2m_attr_erase "instance" "AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

open AlgebraicCurve
open scoped Manifold ContDiff Topology

namespace AbelReciprocityNorm

section LinAlg

variable {n : ℕ}

theorem exists_mulVec_eq (A B : Matrix (Fin n) (Fin n) ℂ)
    (hRR : ∀ i k, ∑ j, (A j i * B j k - B j i * A j k) = 0)
    (hinj : ∀ c : Fin n → ℂ, A.mulVec c = 0 → B.mulVec c = 0 → c = 0)
    (x y : Fin n → ℂ) (hxy : ∀ i, ∑ j, (A j i * y j - B j i * x j) = 0) :
    ∃ c : Fin n → ℂ, A.mulVec c = x ∧ B.mulVec c = y := by
  classical

  let T : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) × (Fin n → ℂ) :=
    LinearMap.prod (Matrix.mulVecLin A) (Matrix.mulVecLin B)
  let Φ : (Fin n → ℂ) × (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    (Matrix.mulVecLin A.transpose).comp (LinearMap.snd ℂ _ _) -
      (Matrix.mulVecLin B.transpose).comp (LinearMap.fst ℂ _ _)
  have hT : ∀ c, T c = (A.mulVec c, B.mulVec c) := fun c => rfl
  have hΦ : ∀ (p : (Fin n → ℂ) × (Fin n → ℂ)) (i : Fin n),
      Φ p i = ∑ j, (A j i * p.2 j - B j i * p.1 j) := by
    intro p i
    simp only [Φ, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.snd_apply,
      LinearMap.fst_apply, Matrix.mulVecLin_apply, Pi.sub_apply, Matrix.mulVec,
      dotProduct, Matrix.transpose_apply, Finset.sum_sub_distrib]

  have hTΦ : LinearMap.range T ≤ LinearMap.ker Φ := by
    rintro _ ⟨c, rfl⟩
    rw [LinearMap.mem_ker]
    funext i
    rw [hΦ, Pi.zero_apply, hT]
    simp only [Matrix.mulVec, dotProduct]
    have hj : ∀ j, A j i * ∑ k, B j k * c k - B j i * ∑ k, A j k * c k =
        ∑ k, c k * (A j i * B j k - B j i * A j k) := by
      intro j
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [Finset.sum_congr rfl fun j _ => hj j, Finset.sum_comm]
    simp only [← Finset.mul_sum, hRR, mul_zero, Finset.sum_const_zero]

  have hTinj : Function.Injective T := by
    intro c c' h
    have h1 : A.mulVec (c - c') = 0 := by
      rw [Matrix.mulVec_sub]; exact sub_eq_zero.2 (congrArg Prod.fst h)
    have h2 : B.mulVec (c - c') = 0 := by
      rw [Matrix.mulVec_sub]; exact sub_eq_zero.2 (congrArg Prod.snd h)
    exact sub_eq_zero.1 (hinj _ h1 h2)
  have hrT : Module.finrank ℂ (LinearMap.range T) = n := by
    rw [LinearMap.finrank_range_of_inj hTinj, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

  let M : Matrix (Fin n ⊕ Fin n) (Fin n) ℂ := Matrix.fromRows A B
  have hMinj : Function.Injective M.mulVecLin := by
    intro c c' h
    have h' : M.mulVec (c - c') = 0 := by
      rw [Matrix.mulVec_sub]; exact sub_eq_zero.2 h
    rw [Matrix.fromRows_mulVec] at h'
    have h1 : A.mulVec (c - c') = 0 := by
      funext j; exact congrFun h' (Sum.inl j)
    have h2 : B.mulVec (c - c') = 0 := by
      funext j; exact congrFun h' (Sum.inr j)
    exact sub_eq_zero.1 (hinj _ h1 h2)
  have hMrank : M.rank = n := by
    rw [Matrix.rank, LinearMap.finrank_range_of_inj hMinj, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin]
  have hMtsurj : Function.Surjective M.transpose.mulVecLin := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    have : M.transpose.rank = n := by rw [Matrix.rank_transpose, hMrank]
    exact this
  have hΦsurj : Function.Surjective Φ := by
    intro tv
    obtain ⟨u, hu⟩ := hMtsurj tv
    refine ⟨(fun j => -u (Sum.inr j), fun j => u (Sum.inl j)), ?_⟩
    funext i
    rw [hΦ]
    have hu' := congrFun hu i
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      Fintype.sum_sum_type, M, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr] at hu'
    rw [← hu']
    simp only [mul_neg, sub_neg_eq_add, Finset.sum_add_distrib]
  have hkerΦ : Module.finrank ℂ (LinearMap.ker Φ) = n := by
    have h1 := LinearMap.finrank_range_add_finrank_ker Φ
    rw [LinearMap.range_eq_top.2 hΦsurj, finrank_top, Module.finrank_prod,
      Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h1
    omega
  have heq : LinearMap.range T = LinearMap.ker Φ :=
    Submodule.eq_of_le_of_finrank_eq hTΦ (hrT.trans hkerΦ.symm)
  have hmem : (x, y) ∈ LinearMap.ker Φ := by
    rw [LinearMap.mem_ker]
    funext i
    rw [hΦ]
    exact hxy i
  rw [← heq] at hmem
  obtain ⟨c, hc⟩ := hmem
  exact ⟨c, congrArg Prod.fst hc, congrArg Prod.snd hc⟩

end LinAlg

section Prim

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

theorem sub_eq_sub_of_isPrimitiveAlong {θ : Ω[F⁄ℂ]} {P Q : Place ℂ F} {γ : Path P Q}
    {g g' : unitInterval → ℂ} (hg : IsPrimitiveAlong θ γ g) (hg' : IsPrimitiveAlong θ γ g')
    (t : unitInterval) : g t - g' t = g 0 - g' 0 := by
  have hloc : IsLocallyConstant (fun s => g s - g' s) := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun t₀ => ?_
    obtain ⟨Φ, hΦ, hgΦ⟩ := hg t₀
    obtain ⟨Φ', hΦ', hgΦ'⟩ := hg' t₀
    set z₀ : ℂ := extChartAt 𝓘(ℂ, ℂ) (γ t₀) (γ t₀) with hz₀

    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hΦ.and hΦ')
    have hconst : ∀ z ∈ Metric.ball z₀ r, Φ z - Φ' z = Φ z₀ - Φ' z₀ := by
      intro z hz
      have hd : ∀ w ∈ Metric.ball z₀ r, HasDerivAt (fun u => Φ u - Φ' u) 0 w := by
        intro w hw
        have h__af := (hball w hw).1.sub (hball w hw).2
        simp at h__af
        exact h__af
      exact Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball z₀ r).isPreconnected
        (fun w hw => (hd w hw).differentiableAt.differentiableWithinAt)
        (fun w hw => (hd w hw).deriv) hz (Metric.mem_ball_self hr)

    have hcont : ContinuousAt (fun s : unitInterval => extChartAt 𝓘(ℂ, ℂ) (γ t₀) (γ s)) t₀ :=
      (continuousAt_extChartAt (I := 𝓘(ℂ, ℂ)) (γ t₀)).comp γ.continuous.continuousAt
    have hin : ∀ᶠ s in 𝓝 t₀, extChartAt 𝓘(ℂ, ℂ) (γ t₀) (γ s) ∈ Metric.ball z₀ r :=
      hcont (Metric.ball_mem_nhds z₀ hr)
    filter_upwards [hin, hgΦ, hgΦ'] with s hs hs1 hs2
    have h0 : g t₀ - g' t₀ = Φ z₀ - Φ' z₀ := by
      rw [hgΦ.self_of_nhds, hgΦ'.self_of_nhds]
    rw [hs1, hs2, hconst _ hs, h0]
  have := hloc.apply_eq_of_preconnectedSpace (x := t) (y := 0)
  exact this

theorem pathIntegral_eq_of_isPrimitiveAlong {θ : Ω[F⁄ℂ]} {P Q : Place ℂ F} {γ : Path P Q}
    {g : unitInterval → ℂ} (hg : IsPrimitiveAlong θ γ g) : pathIntegral θ γ = g 1 - g 0 := by
  classical
  have h : ∃ g, IsPrimitiveAlong θ γ g := ⟨g, hg⟩
  rw [pathIntegral_def, dif_pos h]
  have := sub_eq_sub_of_isPrimitiveAlong h.choose_spec hg 1
  linear_combination this

theorem isPrimitiveAlong_add {θ₁ θ₂ : Ω[F⁄ℂ]} {P Q : Place ℂ F} {γ : Path P Q}
    {g₁ g₂ : unitInterval → ℂ} (h₁ : IsPrimitiveAlong θ₁ γ g₁) (h₂ : IsPrimitiveAlong θ₂ γ g₂)
    (hadd : ∀ t₀ : unitInterval, ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) (γ t₀) (γ t₀)),
      (γ t₀).readDifferential (θ₁ + θ₂) z =
        (γ t₀).readDifferential θ₁ z + (γ t₀).readDifferential θ₂ z) :
    IsPrimitiveAlong (θ₁ + θ₂) γ (fun t => g₁ t + g₂ t) := by
  intro t₀
  obtain ⟨Φ₁, hΦ₁, hg₁⟩ := h₁ t₀
  obtain ⟨Φ₂, hΦ₂, hg₂⟩ := h₂ t₀
  refine ⟨fun z => Φ₁ z + Φ₂ z, ?_, ?_⟩
  · filter_upwards [hΦ₁, hΦ₂, hadd t₀] with z hz1 hz2 hz
    rw [hz]
    exact hz1.add hz2
  · filter_upwards [hg₁, hg₂] with s hs1 hs2
    rw [hs1, hs2]

theorem isPrimitiveAlong_smul {θ : Ω[F⁄ℂ]} {P Q : Place ℂ F} {γ : Path P Q}
    {g : unitInterval → ℂ} (h : IsPrimitiveAlong θ γ g) (a : ℂ)
    (hsmul : ∀ t₀ : unitInterval, ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) (γ t₀) (γ t₀)),
      (γ t₀).readDifferential (a • θ) z = a * (γ t₀).readDifferential θ z) :
    IsPrimitiveAlong (a • θ) γ (fun t => a * g t) := by
  intro t₀
  obtain ⟨Φ, hΦ, hg⟩ := h t₀
  refine ⟨fun z => a * Φ z, ?_, ?_⟩
  · filter_upwards [hΦ, hsmul t₀] with z hz1 hz
    rw [hz]
    exact hz1.const_mul a
  · filter_upwards [hg] with s hs
    rw [hs]

end Prim

section PlaceAlgebra

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem isRational_of_isAlgClosed [IsAlgClosed K] (w : Place K F) [w.FiniteResidue] :
    w.IsRational := by
  haveI : Module.Finite K w.ResidueField := Place.FiniteResidue.finite
  haveI : Algebra.IsIntegral K w.ResidueField := Algebra.IsIntegral.of_finite K _
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := w.ResidueField)).2

theorem evalAt_add_of_mem (w : Place K F) (hw : w.IsRational) {f g : F}
    (hf : f ∈ w.toValuationSubring) (hg : g ∈ w.toValuationSubring) :
    w.evalAt (f + g) = w.evalAt f + w.evalAt g := by
  apply w.algebraMap_residueField_injective
  rw [w.algebraMap_evalAt hw (add_mem hf hg), map_add, w.algebraMap_evalAt hw hf,
    w.algebraMap_evalAt hw hg, ← map_add]
  rfl

theorem evalAt_algebraMap_mul_of_mem (w : Place K F) (hw : w.IsRational) (a : K) {f : F}
    (hf : f ∈ w.toValuationSubring) :
    w.evalAt (algebraMap K F a * f) = a * w.evalAt f := by
  rw [w.evalAt_mul_of_mem hw (w.algebraMap_mem' a) hf, w.evalAt_algebraMap_eq]

theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) :
    0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

theorem eventually_mem_toValuationSubring [HasPrincipalDivisors K F]
    [TopologicalSpace (Place K F)] [T1Space (Place K F)] {f : F} {v : Place K F}
    (hv : f ∈ v.toValuationSubring) : ∀ᶠ u in 𝓝 v, f ∈ u.toValuationSubring := by
  by_cases hf0 : f = 0
  · exact Filter.Eventually.of_forall fun u => by rw [hf0]; exact zero_mem _
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
  have hfin : Set.Finite {u : Place K F | u.ord f < 0} := by
    refine (D.support.finite_toSet).subset fun u hu => ?_
    have hu' : u.ord f < 0 := hu
    rw [Finset.mem_coe, Finsupp.mem_support_iff, hD u]
    exact hu'.ne
  have hopen : IsOpen {u : Place K F | u.ord f < 0}ᶜ := hfin.isClosed.isOpen_compl
  have hvmem : v ∈ {u : Place K F | u.ord f < 0}ᶜ := by
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
    exact ord_nonneg_of_mem v hv
  filter_upwards [hopen.mem_nhds hvmem] with u hu
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hu
  exact u.mem_toValuationSubring_of_ord_nonneg_alt hf0 hu

theorem differentialCoeff_add (v : Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    (θ₁ θ₂ : Ω[F⁄K]) :
    v.differentialCoeff (θ₁ + θ₂) = v.differentialCoeff θ₁ + v.differentialCoeff θ₂ :=
  v.differentialCoeff_unique (by rw [add_smul, v.differentialCoeff_smul_dCoord,
    v.differentialCoeff_smul_dCoord])

theorem differentialCoeff_sub (v : Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    (θ₁ θ₂ : Ω[F⁄K]) :
    v.differentialCoeff (θ₁ - θ₂) = v.differentialCoeff θ₁ - v.differentialCoeff θ₂ :=
  v.differentialCoeff_unique (by rw [sub_smul, v.differentialCoeff_smul_dCoord,
    v.differentialCoeff_smul_dCoord])

theorem differentialCoeff_mem (v : Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    {θ : Ω[F⁄K]} (hθ : θ ∈ regularDifferentials K F) :
    v.differentialCoeff θ ∈ v.toValuationSubring := by
  obtain ⟨f, hf, hfe⟩ := (mem_regularDifferentials_iff (K := K) (F := F)).1 hθ v
  rwa [v.differentialCoeff_unique hfe]

theorem ordDifferential_nonneg (v : Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    {θ : Ω[F⁄K]} (hθ : θ ∈ regularDifferentials K F) : 0 ≤ v.ordDifferential θ :=
  ord_nonneg_of_mem v (differentialCoeff_mem v hθ)

theorem dCoordFn_mem (v : Place K F) : v.dCoordFn ∈ v.toValuationSubring := by
  refine v.mem_toValuationSubring_of_ord_nonneg_alt ?_ (by rw [v.ord_dCoordFn]; exact zero_le_one)
  intro h0
  have := v.ord_dCoordFn
  rw [h0, v.ord_zero] at this
  exact zero_ne_one this

theorem evalAt_eq_zero_of_ord_pos (v : Place K F) {f : F} (h : 0 < v.ord f) : v.evalAt f = 0 := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [v.ord_zero] at h
    exact lt_irrefl _ h
  have hf : f ∈ v.toValuationSubring := v.mem_toValuationSubring_of_ord_nonneg_alt hf0 h.le
  have hnu : ¬IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
    intro hu
    have := v.ord_coe_unit hu.unit
    rw [IsUnit.unit_spec] at this
    change v.ord f = 0 at this
    omega
  have hres : IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩ = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).2 ((IsLocalRing.mem_maximalIdeal _).2
      (mem_nonunits_iff.2 hnu))
  rw [v.evalAt_of_mem hf, hres, ← map_zero (algebraMap K v.ResidueField), v.residueInv_algebraMap]

theorem evalAt_dCoordFn_mul_eq_zero (v : Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    {θ : Ω[F⁄K]} (hθ : θ ∈ regularDifferentials K F) :
    v.evalAt (v.dCoordFn * v.differentialCoeff θ) = 0 := by
  set h := v.differentialCoeff θ with hh
  have hmem : h ∈ v.toValuationSubring := differentialCoeff_mem v hθ
  by_cases h0 : h = 0
  · rw [h0, mul_zero]
    simpa using v.evalAt_algebraMap_eq (0 : K)
  have hπ0 : v.dCoordFn ≠ 0 := by
    intro h0'
    have := v.ord_dCoordFn
    rw [h0', v.ord_zero] at this
    exact zero_ne_one this
  have hpos : 0 < v.ord (v.dCoordFn * h) := by
    rw [v.ord_mul hπ0 h0, v.ord_dCoordFn]
    have := ord_nonneg_of_mem v hmem
    omega
  exact evalAt_eq_zero_of_ord_pos v hpos

theorem differentialCoeff_mem_of_evalAt_eq_zero (v : Place K F) (hv : v.IsRational)
    [v.DCoordGenerates] [Nontrivial Ω[F⁄K]] {θ : Ω[F⁄K]} (hθ : -1 ≤ v.ordDifferential θ)
    (hres : v.evalAt (v.dCoordFn * v.differentialCoeff θ) = 0) :
    v.differentialCoeff θ ∈ v.toValuationSubring := by
  set h := v.differentialCoeff θ with hh
  by_cases h0 : h = 0
  · rw [h0]; exact zero_mem _
  have hπ0 : v.dCoordFn ≠ 0 := by
    intro h0'
    have := v.ord_dCoordFn
    rw [h0', v.ord_zero] at this
    exact zero_ne_one this
  have hθ' : -1 ≤ v.ord h := hθ
  rcases hθ'.lt_or_eq with hlt | heq
  · exact v.mem_toValuationSubring_of_ord_nonneg_alt h0 (by omega)
  · exfalso
    have hord0 : v.ord (v.dCoordFn * h) = 0 := by
      rw [v.ord_mul hπ0 h0, v.ord_dCoordFn, ← heq]; norm_num
    exact v.evalAt_ne_zero_of_ord_eq_zero hv (mul_ne_zero hπ0 h0) hord0 hres

end PlaceAlgebra

section Charts

variable {F : Type*} [Field F] [Algebra ℂ F]

theorem isRational [IsCurveOver ℂ F] (w : Place ℂ F) : w.IsRational := isRational_of_isAlgClosed w

variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

theorem eventually_symm_mem {v : Place ℂ F} {U : Set (Place ℂ F)} (hU : U ∈ 𝓝 v) :
    ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) v v), (extChartAt 𝓘(ℂ, ℂ) v).symm z ∈ U := by
  have hc : ContinuousAt (extChartAt 𝓘(ℂ, ℂ) v).symm (extChartAt 𝓘(ℂ, ℂ) v v) :=
    continuousAt_extChartAt_symm v
  have hU' : U ∈ 𝓝 ((extChartAt 𝓘(ℂ, ℂ) v).symm (extChartAt 𝓘(ℂ, ℂ) v v)) := by
    rwa [extChartAt_to_inv]
  exact hc hU'

variable [IsCurveOver ℂ F] [T2Space (Place ℂ F)]

theorem eventually_readDifferential_add (v : Place ℂ F) [v.DCoordGenerates] {θ₁ θ₂ : Ω[F⁄ℂ]}
    (h₁ : v.differentialCoeff θ₁ ∈ v.toValuationSubring)
    (h₂ : v.differentialCoeff θ₂ ∈ v.toValuationSubring) :
    ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) v v),
      v.readDifferential (θ₁ + θ₂) z = v.readDifferential θ₁ z + v.readDifferential θ₂ z := by
  have e₁ := eventually_symm_mem (eventually_mem_toValuationSubring (K := ℂ) h₁)
  have e₂ := eventually_symm_mem (eventually_mem_toValuationSubring (K := ℂ) h₂)
  filter_upwards [e₁, e₂] with z hz₁ hz₂
  simp only [Place.readDifferential_apply, Place.chartRead_apply]
  rw [differentialCoeff_add, evalAt_add_of_mem _ (isRational _) hz₁ hz₂, add_mul]

theorem eventually_readDifferential_smul (v : Place ℂ F) [v.DCoordGenerates] {θ : Ω[F⁄ℂ]}
    (h : v.differentialCoeff θ ∈ v.toValuationSubring) (a : ℂ) :
    ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) v v),
      v.readDifferential (a • θ) z = a * v.readDifferential θ z := by
  have e := eventually_symm_mem (eventually_mem_toValuationSubring (K := ℂ) h)
  filter_upwards [e] with z hz
  simp only [Place.readDifferential_apply, Place.chartRead_apply]
  rw [← algebraMap_smul F a θ, v.differentialCoeff_smul,
    evalAt_algebraMap_mul_of_mem _ (isRational _) a hz, mul_assoc]

theorem isPrimitiveAlong_sum (hgen : ∀ v : Place ℂ F, v.DCoordGenerates) {ι : Type*}
    (s : Finset ι) (θ : ι → Ω[F⁄ℂ]) (hθ : ∀ i, θ i ∈ regularDifferentials ℂ F) (c : ι → ℂ)
    {P Q : Place ℂ F} (γ : Path P Q) (g : ι → unitInterval → ℂ)
    (hg : ∀ i, IsPrimitiveAlong (θ i) γ (g i)) :
    IsPrimitiveAlong (∑ i ∈ s, c i • θ i) γ (fun t => ∑ i ∈ s, c i * g i t) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro t₀
    refine ⟨fun _ => 0, ?_, Filter.Eventually.of_forall fun t => by simp⟩
    haveI := hgen (γ t₀)
    filter_upwards with z
    simp only [Finset.sum_empty]
    rw [Place.readDifferential_apply, Place.chartRead_apply, Place.differentialCoeff_zero]
    have h0 : Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) (γ t₀)).symm z) (0 : F) = 0 := by
      simpa using Place.evalAt_algebraMap_eq ((extChartAt 𝓘(ℂ, ℂ) (γ t₀)).symm z) (0 : ℂ)
    rw [h0, zero_mul]
    exact hasDerivAt_const z 0
  | insert a s ha ih =>
    have hreg : (∑ i ∈ s, c i • θ i) ∈ regularDifferentials ℂ F :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hθ i)
    have h1 : IsPrimitiveAlong (c a • θ a) γ (fun t => c a * g a t) := by
      refine isPrimitiveAlong_smul (hg a) (c a) fun t₀ => ?_
      haveI := hgen (γ t₀)
      exact eventually_readDifferential_smul (γ t₀) (differentialCoeff_mem _ (hθ a)) (c a)
    have h2 := isPrimitiveAlong_add h1 ih fun t₀ => by
      haveI := hgen (γ t₀)
      exact eventually_readDifferential_add (γ t₀)
        (differentialCoeff_mem _ (Submodule.smul_mem _ _ (hθ a))) (differentialCoeff_mem _ hreg)
    simp only [Finset.sum_insert ha]
    exact h2

end Charts

end AbelReciprocityNorm

open AbelReciprocityNorm in
theorem solution
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F] [HasCanonicalDivisor (K := ℂ) (F := F)]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [CompactSpace (Place ℂ F)]
    [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    {n : ℕ} (b : Module.Basis (Fin n) ℂ ↥(regularDifferentials ℂ F)) (P₀ : Place ℂ F)
    (D : Divisor ℂ F) (hD0 : Divisor.degree D = 0)
    (η : Ω[F⁄ℂ]) (hη : ∀ v : Place ℂ F, -1 ≤ v.ordDifferential η)
    (hres : ∀ v : Place ℂ F, Place.evalAt v (v.dCoordFn * v.differentialCoeff η) = (D v : ℂ))
    (hD : abelJacobiDiv (fun i => (b i : Ω[F⁄ℂ])) P₀ D ∈
      pathPeriodLattice (fun i => (b i : Ω[F⁄ℂ]))) :
    ∃ ζ ∈ regularDifferentials ℂ F, ∀ (P : Place ℂ F) (γ : Path P P),
      (∀ t, D (γ t) = 0) → ∃ m : ℤ, pathIntegral (η - ζ) γ = 2 * Real.pi * Complex.I * m := by
  classical
  have _ := hD0

  have hgen : ∀ v : Place ℂ F, v.DCoordGenerates := by
    obtain ⟨x, hx, hfd⟩ := hfg
    haveI := AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional hx hfd
    exact AlgebraicCurve.dCoordGenerates_of_isCurveOver
  have hbreg : ∀ i, (b i : Ω[F⁄ℂ]) ∈ regularDifferentials ℂ F := fun i => (b i).2
  set S : Finset (Place ℂ F) := D.support with hS
  have hSD : ∀ v : Place ℂ F, v ∉ S → D v = 0 := fun v hv => by
    simpa [hS, Finsupp.mem_support_iff] using hv

  obtain ⟨Pα, Pβ, α, β, -, hG1, hG2, hRR, hR3⟩ :=
    AlgebraicCurve.exists_loops_pathIntegral_reciprocity F hfg hF b P₀ S

  obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin n) (Fin n) ℂ,
      ∀ j i, A j i = pathIntegral (b i : Ω[F⁄ℂ]) (α j) := ⟨fun j i => _, fun _ _ => rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin n) (Fin n) ℂ,
      ∀ j i, B j i = pathIntegral (b i : Ω[F⁄ℂ]) (β j) := ⟨fun j i => _, fun _ _ => rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : Fin n → ℂ, ∀ j, x j = pathIntegral η (α j) := ⟨fun j => _, fun _ => rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : Fin n → ℂ, ∀ j, y j = pathIntegral η (β j) := ⟨fun j => _, fun _ => rfl⟩

  have hΛ : ∀ u ∈ pathPeriodLattice (fun i => (b i : Ω[F⁄ℂ])), ∃ κ μ : Fin n → ℤ,
      u = fun i => ∑ j, ((κ j : ℂ) * A j i + (μ j : ℂ) * B j i) := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨Q, δ, rfl⟩ := hu
      obtain ⟨κ, μ, hκμ⟩ := hG1 Q δ
      refine ⟨κ, μ, funext fun i => ?_⟩
      rw [hκμ _ (hbreg i)]
      simp only [← hA, ← hB]
    | zero => exact ⟨0, 0, by funext i; simp⟩
    | add u u' _ _ hu hu' =>
      obtain ⟨κ, μ, rfl⟩ := hu
      obtain ⟨κ', μ', rfl⟩ := hu'
      refine ⟨κ + κ', μ + μ', funext fun i => ?_⟩
      simp only [Pi.add_apply, Int.cast_add, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    | smul a u _ hu =>
      obtain ⟨κ, μ, rfl⟩ := hu
      refine ⟨a • κ, a • μ, funext fun i => ?_⟩
      simp only [Pi.smul_apply, zsmul_eq_mul, Int.cast_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by push_cast; ring
  obtain ⟨m, m', hm⟩ := hΛ _ hD
  have hAJ : ∀ i, abelJacobiDiv (fun i => (b i : Ω[F⁄ℂ])) P₀ D i =
      ∑ j, ((m j : ℂ) * A j i + (m' j : ℂ) * B j i) := fun i => congrFun hm i

  obtain ⟨κ, μ, hrec⟩ := hR3 D η hη hres (fun v hv => Finsupp.mem_support_iff.2 hv)
  have hrec' : ∀ i, ∑ j, (A j i * y j - B j i * x j) = 2 * Real.pi * Complex.I *
      (abelJacobiDiv (fun i => (b i : Ω[F⁄ℂ])) P₀ D i +
        ∑ j, ((κ j : ℂ) * A j i + (μ j : ℂ) * B j i)) := by
    intro i
    have h := hrec i
    simp only [← hA, ← hB, ← hx, ← hy] at h
    exact h

  have hRR' : ∀ i k, ∑ j, (A j i * B j k - B j i * A j k) = 0 := by
    intro i k
    have h := hRR _ (hbreg i) _ (hbreg k)
    simp only [← hA, ← hB] at h
    exact h

  have hcomb : ∀ (c : Fin n → ℂ) {P' Q' : Place ℂ F} (δ : Path P' Q'),
      ∃ g : unitInterval → ℂ, IsPrimitiveAlong (∑ i, c i • (b i : Ω[F⁄ℂ])) δ g ∧
        g 1 - g 0 = ∑ i, c i * pathIntegral (b i : Ω[F⁄ℂ]) δ := by
    intro c P' Q' δ
    have hex : ∀ i, ∃ g : unitInterval → ℂ, IsPrimitiveAlong (b i : Ω[F⁄ℂ]) δ g := fun i =>
      (AlgebraicCurve.exists_isPrimitiveAlong_of_mem_regularDifferentials F hfg hF _
        (hbreg i) δ).1
    choose g hg using hex
    refine ⟨fun t => ∑ i, c i * g i t,
      isPrimitiveAlong_sum hgen Finset.univ (fun i => (b i : Ω[F⁄ℂ])) hbreg c δ g hg, ?_⟩
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by
      rw [pathIntegral_eq_of_isPrimitiveAlong (hg i)]; ring
  have hcombInt : ∀ (c : Fin n → ℂ) {P' Q' : Place ℂ F} (δ : Path P' Q'),
      pathIntegral (∑ i, c i • (b i : Ω[F⁄ℂ])) δ = ∑ i, c i * pathIntegral (b i : Ω[F⁄ℂ]) δ := by
    intro c P' Q' δ
    obtain ⟨g, hg, hg'⟩ := hcomb c δ
    rw [pathIntegral_eq_of_isPrimitiveAlong hg, hg']
  have hinj : ∀ c : Fin n → ℂ, A.mulVec c = 0 → B.mulVec c = 0 → c = 0 := by
    intro c hAc hBc

    let ℓ : (Fin n → ℂ) →ₗ[ℝ] ℂ :=
      { toFun := fun u => ∑ i, c i * u i
        map_add' := fun u u' => by
          simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
        map_smul' := fun r u => by
          simp only [Pi.smul_apply, Complex.real_smul, RingHom.id_apply, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring }
    have hℓ : ∀ u : Fin n → ℂ, ℓ u = ∑ i, c i * u i := fun u => rfl
    have hAc' : ∀ j, ∑ i, A j i * c i = 0 := fun j => by
      have := congrFun hAc j; simpa [Matrix.mulVec, dotProduct] using this
    have hBc' : ∀ j, ∑ i, B j i * c i = 0 := fun j => by
      have := congrFun hBc j; simpa [Matrix.mulVec, dotProduct] using this
    have hgenℓ : ∀ u ∈ pathPeriodLattice (fun i => (b i : Ω[F⁄ℂ])), ℓ u = 0 := by
      intro u hu
      obtain ⟨κ', μ', rfl⟩ := hΛ u hu
      rw [hℓ]
      calc ∑ i, c i * ∑ j, ((κ' j : ℂ) * A j i + (μ' j : ℂ) * B j i)
          = ∑ j, ((κ' j : ℂ) * ∑ i, A j i * c i + (μ' j : ℂ) * ∑ i, B j i * c i) := by
            simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
            rw [Finset.sum_comm (f := fun i j => c i * ((κ' j : ℂ) * A j i)),
              Finset.sum_comm (f := fun i j => c i * ((μ' j : ℂ) * B j i))]
            refine congrArg₂ (· + ·) ?_ ?_
            · exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
            · exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
        _ = 0 := by simp [hAc', hBc']
    have hspan := AlgebraicCurve.span_real_pathPeriodLattice_eq_top F hfg hF b
    have hker : Submodule.span ℝ (pathPeriodLattice (fun i => (b i : Ω[F⁄ℂ])) :
        Set (Fin n → ℂ)) ≤ LinearMap.ker ℓ := by
      rw [Submodule.span_le]
      intro u hu
      exact (LinearMap.mem_ker).2 (hgenℓ u hu)
    rw [hspan, top_le_iff] at hker
    funext k
    have hk : ℓ (Pi.single k 1) = 0 := by
      have : (Pi.single k 1 : Fin n → ℂ) ∈ LinearMap.ker ℓ := by rw [hker]; trivial
      exact (LinearMap.mem_ker).1 this
    rw [hℓ] at hk
    simpa [Pi.single_apply] using hk

  obtain ⟨N, hN⟩ : ∃ N : Fin n → ℤ, ∀ j, N j = m j + κ j := ⟨fun j => _, fun _ => rfl⟩
  obtain ⟨N', hN'⟩ : ∃ N' : Fin n → ℤ, ∀ j, N' j = m' j + μ j := ⟨fun j => _, fun _ => rfl⟩
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : Fin n → ℂ, ∀ j, x₀ j = -(2 * Real.pi * Complex.I * (N' j : ℂ)) :=
    ⟨fun j => _, fun _ => rfl⟩
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : Fin n → ℂ, ∀ j, y₀ j = 2 * Real.pi * Complex.I * (N j : ℂ) :=
    ⟨fun j => _, fun _ => rfl⟩
  have hker : ∀ i, ∑ j, (A j i * (y - y₀) j - B j i * (x - x₀) j) = 0 := by
    intro i
    have e : ∑ j, (A j i * (y - y₀) j - B j i * (x - x₀) j) =
        ∑ j, (A j i * y j - B j i * x j) -
          2 * Real.pi * Complex.I * ∑ j, (((m j : ℂ) + κ j) * A j i + ((m' j : ℂ) + μ j) * B j i) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Pi.sub_apply, hx₀, hy₀, hN, hN', Int.cast_add]
      ring
    rw [e, hrec' i, hAJ i, ← mul_sub, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    have : ∀ j, (m j : ℂ) * A j i + (m' j : ℂ) * B j i + ((κ j : ℂ) * A j i + (μ j : ℂ) * B j i) -
        (((m j : ℂ) + κ j) * A j i + ((m' j : ℂ) + μ j) * B j i) = 0 := fun j => by ring
    simp [this]
  obtain ⟨c, hc1, hc2⟩ := exists_mulVec_eq A B hRR' hinj (x - x₀) (y - y₀) hker
  have hcα : ∀ j, x j - ∑ i, c i * A j i = -(2 * Real.pi * Complex.I * (N' j : ℂ)) := fun j => by
    have h := congrFun hc1 j
    simp only [Matrix.mulVec, dotProduct, Pi.sub_apply] at h
    have e : ∑ i, A j i * c i = ∑ i, c i * A j i := Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [← hx₀ j]
    rw [e] at h
    linear_combination -h
  have hcβ : ∀ j, y j - ∑ i, c i * B j i = 2 * Real.pi * Complex.I * (N j : ℂ) := fun j => by
    have h := congrFun hc2 j
    simp only [Matrix.mulVec, dotProduct, Pi.sub_apply] at h
    have e : ∑ i, B j i * c i = ∑ i, c i * B j i := Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [← hy₀ j]
    rw [e] at h
    linear_combination -h

  obtain ⟨ζ, hζ⟩ : ∃ ζ : Ω[F⁄ℂ], ζ = ∑ i, c i • (b i : Ω[F⁄ℂ]) := ⟨_, rfl⟩
  have hζreg : ζ ∈ regularDifferentials ℂ F := by
    rw [hζ]; exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hbreg i)
  refine ⟨ζ, hζreg, fun P γ hγ => ?_⟩

  by_cases hprim : ∃ g, IsPrimitiveAlong (η - ζ) γ g
  swap
  · refine ⟨0, ?_⟩
    rw [pathIntegral_def, dif_neg hprim]
    simp
  obtain ⟨g, hg⟩ := hprim
  have hγS : ∀ t, γ t ∉ S := fun t ht => (Finsupp.mem_support_iff.1 ht) (hγ t)

  have hηreg : ∀ v : Place ℂ F, v ∉ S → v.differentialCoeff η ∈ v.toValuationSubring := by
    intro v hv
    haveI := hgen v
    refine differentialCoeff_mem_of_evalAt_eq_zero v (isRational v) (hη v) ?_
    rw [hres v, hSD v hv, Int.cast_zero]
  obtain ⟨gζ, hgζ, hgζ'⟩ := hcomb c γ
  rw [← hζ] at hgζ
  have hgη : IsPrimitiveAlong η γ (fun t => g t + gζ t) := by
    have h := isPrimitiveAlong_add hg hgζ fun t₀ => by
      haveI := hgen (γ t₀)
      refine eventually_readDifferential_add (γ t₀) ?_ (differentialCoeff_mem _ hζreg)
      rw [differentialCoeff_sub]
      exact sub_mem (hηreg _ (hγS t₀)) (differentialCoeff_mem _ hζreg)
    simpa only [sub_add_cancel] using h
  have hIηζ : pathIntegral (η - ζ) γ =
      pathIntegral η γ - ∑ i, c i * pathIntegral (b i : Ω[F⁄ℂ]) γ := by
    rw [pathIntegral_eq_of_isPrimitiveAlong hg, pathIntegral_eq_of_isPrimitiveAlong hgη, ← hgζ']
    ring

  obtain ⟨κ', μ', w, hG2γ⟩ := hG2 P γ hγS
  have hordη : ∀ v : Place ℂ F, v ∉ S → 0 ≤ v.ordDifferential η := fun v hv => by
    haveI := hgen v
    exact ord_nonneg_of_mem v (hηreg v hv)
  have hordζ : ∀ v : Place ℂ F, 0 ≤ v.ordDifferential ζ := fun v => by
    haveI := hgen v
    exact ordDifferential_nonneg v hζreg
  have hresζ : ∀ v : Place ℂ F, Place.evalAt v (v.dCoordFn * v.differentialCoeff ζ) = 0 := fun v => by
    haveI := hgen v
    exact evalAt_dCoordFn_mul_eq_zero v hζreg
  have eη : pathIntegral η γ = ∑ j, ((κ' j : ℂ) * x j + (μ' j : ℂ) * y j) +
      2 * Real.pi * Complex.I * ∑ v ∈ S, (w v : ℂ) * (D v : ℂ) := by
    rw [hG2γ η hη hordη]
    simp only [← hx, ← hy, hres]
  have eζ : ∑ i, c i * pathIntegral (b i : Ω[F⁄ℂ]) γ =
      ∑ j, ((κ' j : ℂ) * ∑ i, c i * A j i + (μ' j : ℂ) * ∑ i, c i * B j i) := by
    have h := hG2γ ζ (fun v => by have := hordζ v; omega) (fun v _ => hordζ v)
    rw [hζ, hcombInt c γ] at h
    rw [h]
    have h0 : ∑ v ∈ S, (w v : ℂ) * Place.evalAt v (v.dCoordFn *
        v.differentialCoeff (∑ i, c i • (b i : Ω[F⁄ℂ]))) = 0 :=
      Finset.sum_eq_zero fun v _ => by rw [← hζ, hresζ v, mul_zero]
    rw [h0, mul_zero, add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hcombInt c (α j), hcombInt c (β j)]
    simp only [← hA, ← hB]

  refine ⟨∑ j, (-(κ' j * N' j) + μ' j * N j) + ∑ v ∈ S, w v * D v, ?_⟩
  rw [hIηζ, eη, eζ]
  have key : ∀ j, ((κ' j : ℂ) * x j + (μ' j : ℂ) * y j) -
      ((κ' j : ℂ) * ∑ i, c i * A j i + (μ' j : ℂ) * ∑ i, c i * B j i) =
      2 * Real.pi * Complex.I * (-((κ' j : ℂ) * (N' j : ℂ)) + (μ' j : ℂ) * (N j : ℂ)) := by
    intro j
    have h1 := hcα j
    have h2 := hcβ j
    linear_combination (κ' j : ℂ) * h1 + (μ' j : ℂ) * h2
  have hsum : ∑ j, ((κ' j : ℂ) * x j + (μ' j : ℂ) * y j) -
      ∑ j, ((κ' j : ℂ) * ∑ i, c i * A j i + (μ' j : ℂ) * ∑ i, c i * B j i) =
      2 * Real.pi * Complex.I * ∑ j, (-((κ' j : ℂ) * (N' j : ℂ)) + (μ' j : ℂ) * (N j : ℂ)) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => key j
  push_cast
  linear_combination hsum

end S_AlgebraicCurve_exists_regular_pathIntegral_sub_eq_of_abelJacobiDiv_mem_pathPeriodLattice
end P2MW
export P2MW.S_AlgebraicCurve_exists_regular_pathIntegral_sub_eq_of_abelJacobiDiv_mem_pathPeriodLattice (solution)
