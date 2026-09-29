-- Prove2me | solution 1 for AlgebraicCurve.Place.existsUnique_forall_mem_toValuationSubring_and_evalAt_eq_appLE_of_differentiableAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/831658e9-5010-5778-908f-c248ef87aaee

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_CurveModel
import Theorems.Thm_AlgebraicCurve_Place_evalAt_eq_zero_iff_one_le_ord
import Theorems.Thm_AlgebraicCurve_Place_forall_not_le_preimage_or_finite_setOf_of_differentiableAt_appLE_of_isSeparated
import Theorems.Thm_AlgebraicCurve_exists_eventuallyEq_evalAt_of_meromorphicAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_existsUnique_forall_mem_toValuationSubring_and_evalAt_eq_appLE_of_differentiableAt
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.Gamma0Pair.isElliptic AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry AlgebraicCurve~H1"
p2m_open_scoped "Manifold P2MW.S_AlgebraicCurve_Place_existsUnique_forall_mem_toValuationSubring_and_evalAt_eq_appLE_of_differentiableAt.Manifold ContDiff Topology"

p2m_open_scoped "Manifold" in

theorem Manifold.exists_isOpen_differentiableOn_extChartAt_symm_of_forall_differentiableAt
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ, ℂ) ω M]
    {O : Set M} (hO : IsOpen O) (G : M → ℂ)
    (hG : ∀ v ∈ O, DifferentiableAt ℂ (fun z : ℂ => G ((extChartAt 𝓘(ℂ, ℂ) v).symm z)) (extChartAt 𝓘(ℂ, ℂ) v v)) :
    ∀ v ∈ O, ∃ S : Set ℂ, IsOpen S ∧ extChartAt 𝓘(ℂ, ℂ) v v ∈ S ∧
      DifferentiableOn ℂ (fun z : ℂ => G ((extChartAt 𝓘(ℂ, ℂ) v).symm z)) S := by
  intro v hv

  set S : Set ℂ := ((extChartAt 𝓘(ℂ, ℂ) v).symm ⁻¹' (O ∩ (extChartAt 𝓘(ℂ, ℂ) v).source)) ∩
    (extChartAt 𝓘(ℂ, ℂ) v).target with hS
  have hSopen : IsOpen S := by
    rw [hS]
    have h1 : IsOpen ((extChartAt 𝓘(ℂ, ℂ) v).target ∩
        (extChartAt 𝓘(ℂ, ℂ) v).symm ⁻¹' (O ∩ (extChartAt 𝓘(ℂ, ℂ) v).source)) :=
      (continuousOn_extChartAt_symm (I := 𝓘(ℂ, ℂ)) v).isOpen_inter_preimage
        (isOpen_extChartAt_target (I := 𝓘(ℂ, ℂ)) v) (hO.inter (isOpen_extChartAt_source (I := 𝓘(ℂ, ℂ)) v))
    rwa [Set.inter_comm] at h1
  have hmem : extChartAt 𝓘(ℂ, ℂ) v v ∈ S := by
    rw [hS]
    refine ⟨?_, mem_extChartAt_target (I := 𝓘(ℂ, ℂ)) v⟩
    show (extChartAt 𝓘(ℂ, ℂ) v).symm (extChartAt 𝓘(ℂ, ℂ) v v) ∈ O ∩ (extChartAt 𝓘(ℂ, ℂ) v).source
    rw [extChartAt_to_inv]
    exact ⟨hv, mem_extChartAt_source (I := 𝓘(ℂ, ℂ)) v⟩

  have hdiff : DifferentiableOn ℂ (fun z : ℂ => G ((extChartAt 𝓘(ℂ, ℂ) v).symm z)) S := by
    intro z₁ hz₁
    rw [hS] at hz₁
    obtain ⟨⟨hO₁, hsrc₁⟩, htgt₁⟩ := hz₁
    apply DifferentiableAt.differentiableWithinAt
    set v₁ : M := (extChartAt 𝓘(ℂ, ℂ) v).symm z₁ with hv₁
    have hA1 : DifferentiableAt ℂ (fun z : ℂ => G ((extChartAt 𝓘(ℂ, ℂ) v₁).symm z)) (extChartAt 𝓘(ℂ, ℂ) v₁ v₁) :=
      hG v₁ hO₁
    have hy : z₁ ∈ ((extChartAt 𝓘(ℂ, ℂ) v).symm ≫ extChartAt 𝓘(ℂ, ℂ) v₁).source := by
      rw [PartialEquiv.trans_source, PartialEquiv.symm_source]
      refine ⟨htgt₁, ?_⟩
      show (extChartAt 𝓘(ℂ, ℂ) v).symm z₁ ∈ (extChartAt 𝓘(ℂ, ℂ) v₁).source
      exact mem_extChartAt_source (I := 𝓘(ℂ, ℂ)) v₁
    have hτ : ContDiffWithinAt ℂ ω (extChartAt 𝓘(ℂ, ℂ) v₁ ∘ (extChartAt 𝓘(ℂ, ℂ) v).symm) (Set.range 𝓘(ℂ, ℂ)) z₁ :=
      contDiffWithinAt_ext_coord_change (I := 𝓘(ℂ, ℂ)) v₁ v hy
    have hτ' : DifferentiableAt ℂ (extChartAt 𝓘(ℂ, ℂ) v₁ ∘ (extChartAt 𝓘(ℂ, ℂ) v).symm) z₁ := by
      have h' : ContDiffAt ℂ ω (extChartAt 𝓘(ℂ, ℂ) v₁ ∘ (extChartAt 𝓘(ℂ, ℂ) v).symm) z₁ :=
        hτ.contDiffAt (by simp)
      exact h'.differentiableAt (by simp)
    have heq : (fun z : ℂ => G ((extChartAt 𝓘(ℂ, ℂ) v).symm z)) =ᶠ[𝓝 z₁]
        ((fun z : ℂ => G ((extChartAt 𝓘(ℂ, ℂ) v₁).symm z)) ∘ (extChartAt 𝓘(ℂ, ℂ) v₁ ∘ (extChartAt 𝓘(ℂ, ℂ) v).symm)) := by
      have hn : (extChartAt 𝓘(ℂ, ℂ) v).symm ⁻¹' (extChartAt 𝓘(ℂ, ℂ) v₁).source ∈ 𝓝 z₁ :=
        (continuousAt_extChartAt_symm'' (I := 𝓘(ℂ, ℂ)) htgt₁).preimage_mem_nhds
          ((isOpen_extChartAt_source (I := 𝓘(ℂ, ℂ)) v₁).mem_nhds (mem_extChartAt_source (I := 𝓘(ℂ, ℂ)) v₁))
      filter_upwards [hn] with z hz
      simp only [Function.comp_apply]
      rw [(extChartAt 𝓘(ℂ, ℂ) v₁).left_inv hz]
    refine (Filter.EventuallyEq.differentiableAt_iff heq).2 ?_
    exact DifferentiableAt.comp z₁ hA1 hτ'
  exact ⟨S, hSopen, hmem, hdiff⟩

p2m_open_scoped "Manifold" in
theorem Manifold.analyticAt_extChartAt_of_forall_differentiableAt
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ, ℂ) ω M]
    {O : Set M} (hO : IsOpen O) (G : M → ℂ)
    (hG : ∀ v ∈ O, DifferentiableAt ℂ (fun z : ℂ => G ((extChartAt 𝓘(ℂ, ℂ) v).symm z)) (extChartAt 𝓘(ℂ, ℂ) v v)) :
    ∀ v ∈ O, AnalyticAt ℂ (fun z : ℂ => G ((extChartAt 𝓘(ℂ, ℂ) v).symm z)) (extChartAt 𝓘(ℂ, ℂ) v v) := by
  intro v hv
  obtain ⟨S, hS, hmem, hdiff⟩ := Manifold.exists_isOpen_differentiableOn_extChartAt_symm_of_forall_differentiableAt hO G hG v hv
  exact hdiff.analyticAt (hS.mem_nhds hmem)

theorem eventually_analyticAt_extChartAt_symm_of_forall_differentiableAt
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ, ℂ) ω M]
    (G : M → ℂ) (O : Set M) (hO : IsOpen O)
    (hG : ∀ v ∈ O, DifferentiableAt ℂ (fun z : ℂ => G ((extChartAt 𝓘(ℂ, ℂ) v).symm z)) (extChartAt 𝓘(ℂ, ℂ) v v))
    (v : M) (hv : v ∈ O) :
    ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) v v), AnalyticAt ℂ (fun z : ℂ => G ((extChartAt 𝓘(ℂ, ℂ) v).symm z)) z := by
  obtain ⟨S, hS, hmem, hdiff⟩ := Manifold.exists_isOpen_differentiableOn_extChartAt_symm_of_forall_differentiableAt hO G hG v hv
  filter_upwards [hS.mem_nhds hmem] with z hz
  exact hdiff.analyticAt (hS.mem_nhds hz)

theorem analyticAt_extChartAt_symm_of_forall_differentiableAt
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ, ℂ) ω M]
    (G : M → ℂ) (O : Set M) (hO : IsOpen O)
    (hG : ∀ v ∈ O, DifferentiableAt ℂ (fun z : ℂ => G ((extChartAt 𝓘(ℂ, ℂ) v).symm z)) (extChartAt 𝓘(ℂ, ℂ) v v))
    (v : M) (hv : v ∈ O) :
    AnalyticAt ℂ (fun z : ℂ => G ((extChartAt 𝓘(ℂ, ℂ) v).symm z)) (extChartAt 𝓘(ℂ, ℂ) v v) :=
  Manifold.analyticAt_extChartAt_of_forall_differentiableAt hO G hG v hv

theorem differentiableOn_extChartAt_symm_of_forall_differentiableAt
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ, ℂ) ω M]
    (G : M → ℂ) (O : Set M) (hO : IsOpen O)
    (hG : ∀ v ∈ O, DifferentiableAt ℂ (fun z : ℂ => G ((extChartAt 𝓘(ℂ, ℂ) v).symm z)) (extChartAt 𝓘(ℂ, ℂ) v v))
    (v : M) :
    IsOpen ((extChartAt 𝓘(ℂ, ℂ) v).target ∩ (extChartAt 𝓘(ℂ, ℂ) v).symm ⁻¹' ((extChartAt 𝓘(ℂ, ℂ) v).source ∩ O)) ∧
    DifferentiableOn ℂ (fun z : ℂ => G ((extChartAt 𝓘(ℂ, ℂ) v).symm z))
      ((extChartAt 𝓘(ℂ, ℂ) v).target ∩ (extChartAt 𝓘(ℂ, ℂ) v).symm ⁻¹' ((extChartAt 𝓘(ℂ, ℂ) v).source ∩ O)) := by
  refine ⟨(continuousOn_extChartAt_symm (I := 𝓘(ℂ, ℂ)) v).isOpen_inter_preimage
      (isOpen_extChartAt_target (I := 𝓘(ℂ, ℂ)) v) ((isOpen_extChartAt_source (I := 𝓘(ℂ, ℂ)) v).inter hO), ?_⟩
  intro z₁ hz₁
  obtain ⟨htgt₁, hsrc₁, hO₁⟩ := hz₁
  apply DifferentiableAt.differentiableWithinAt
  set v₁ : M := (extChartAt 𝓘(ℂ, ℂ) v).symm z₁ with hv₁
  have hA1 : DifferentiableAt ℂ (fun z : ℂ => G ((extChartAt 𝓘(ℂ, ℂ) v₁).symm z)) (extChartAt 𝓘(ℂ, ℂ) v₁ v₁) :=
    hG v₁ hO₁
  have hy : z₁ ∈ ((extChartAt 𝓘(ℂ, ℂ) v).symm ≫ extChartAt 𝓘(ℂ, ℂ) v₁).source := by
    rw [PartialEquiv.trans_source, PartialEquiv.symm_source]
    refine ⟨htgt₁, ?_⟩
    show (extChartAt 𝓘(ℂ, ℂ) v).symm z₁ ∈ (extChartAt 𝓘(ℂ, ℂ) v₁).source
    exact mem_extChartAt_source (I := 𝓘(ℂ, ℂ)) v₁
  have hτ : ContDiffWithinAt ℂ ω (extChartAt 𝓘(ℂ, ℂ) v₁ ∘ (extChartAt 𝓘(ℂ, ℂ) v).symm) (Set.range 𝓘(ℂ, ℂ)) z₁ :=
    contDiffWithinAt_ext_coord_change (I := 𝓘(ℂ, ℂ)) v₁ v hy
  have hτ' : DifferentiableAt ℂ (extChartAt 𝓘(ℂ, ℂ) v₁ ∘ (extChartAt 𝓘(ℂ, ℂ) v).symm) z₁ := by
    have h' : ContDiffAt ℂ ω (extChartAt 𝓘(ℂ, ℂ) v₁ ∘ (extChartAt 𝓘(ℂ, ℂ) v).symm) z₁ :=
      hτ.contDiffAt (by simp)
    exact h'.differentiableAt (by simp)
  have heq : (fun z : ℂ => G ((extChartAt 𝓘(ℂ, ℂ) v).symm z)) =ᶠ[𝓝 z₁]
      ((fun z : ℂ => G ((extChartAt 𝓘(ℂ, ℂ) v₁).symm z)) ∘ (extChartAt 𝓘(ℂ, ℂ) v₁ ∘ (extChartAt 𝓘(ℂ, ℂ) v).symm)) := by
    have hn : (extChartAt 𝓘(ℂ, ℂ) v).symm ⁻¹' (extChartAt 𝓘(ℂ, ℂ) v₁).source ∈ 𝓝 z₁ :=
      (continuousAt_extChartAt_symm'' (I := 𝓘(ℂ, ℂ)) htgt₁).preimage_mem_nhds
        ((isOpen_extChartAt_source (I := 𝓘(ℂ, ℂ)) v₁).mem_nhds (mem_extChartAt_source (I := 𝓘(ℂ, ℂ)) v₁))
    filter_upwards [hn] with z hz
    simp only [Function.comp_apply]
    rw [(extChartAt 𝓘(ℂ, ℂ) v₁).left_inv hz]
  refine (Filter.EventuallyEq.differentiableAt_iff heq).2 ?_
  exact DifferentiableAt.comp z₁ hA1 hτ'

theorem analyticAt_extChartAt_symm_of_mem_of_forall_differentiableAt
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ, ℂ) ω M]
    (G : M → ℂ) (O : Set M) (hO : IsOpen O)
    (hG : ∀ v ∈ O, DifferentiableAt ℂ (fun z : ℂ => G ((extChartAt 𝓘(ℂ, ℂ) v).symm z)) (extChartAt 𝓘(ℂ, ℂ) v v))
    (v : M) {z : ℂ}
    (hz : z ∈ (extChartAt 𝓘(ℂ, ℂ) v).target ∩ (extChartAt 𝓘(ℂ, ℂ) v).symm ⁻¹' ((extChartAt 𝓘(ℂ, ℂ) v).source ∩ O)) :
    AnalyticAt ℂ (fun z : ℂ => G ((extChartAt 𝓘(ℂ, ℂ) v).symm z)) z := by
  obtain ⟨hS, hd⟩ := differentiableOn_extChartAt_symm_of_forall_differentiableAt G O hO hG v
  exact hd.analyticAt (hS.mem_nhds hz)

namespace H2_16

variable {F : Type} [Field F] [Algebra ℂ F]

theorem mem_iff_adicValuation_le_one (v : Place ℂ F) (f : F) :
    f ∈ v.toValuationSubring ↔ v.adicValuation f ≤ 1 := by
  constructor
  · intro hf
    have := v.adicValuation_coe ⟨f, hf⟩
    rw [show ((⟨f, hf⟩ : v.toValuationSubring) : F) = f from rfl] at this
    rw [this]
    exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _
  · intro hle
    by_contra hf
    have hf0 : f ≠ 0 := by rintro rfl; exact hf (zero_mem _)
    have hinv : f⁻¹ ∈ v.toValuationSubring := by
      rcases v.toValuationSubring.mem_or_inv_mem f with h | h
      · exact absurd h hf
      · exact h
    have hnu : ¬ IsUnit (⟨f⁻¹, hinv⟩ : v.toValuationSubring) := by
      intro hu
      obtain ⟨b, hb⟩ := hu.exists_right_inv
      have hbF : f⁻¹ * (b : F) = 1 := by
        have := congrArg (fun x : v.toValuationSubring => (x : F)) hb
        simpa using this
      have hbf : (b : F) = f := by
        calc (b : F) = f * (f⁻¹ * (b : F)) := by rw [← mul_assoc, mul_inv_cancel₀ hf0, one_mul]
          _ = f := by rw [hbF, mul_one]
      exact hf (hbf ▸ b.2)
    have hmem : (⟨f⁻¹, hinv⟩ : v.toValuationSubring) ∈ v.heightOneSpectrum.asIdeal := by
      rw [Place.heightOneSpectrum_asIdeal, IsLocalRing.mem_maximalIdeal]; exact hnu
    have hlt : v.adicValuation f⁻¹ < 1 := by
      have := v.adicValuation_coe ⟨f⁻¹, hinv⟩
      rw [show ((⟨f⁻¹, hinv⟩ : v.toValuationSubring) : F) = f⁻¹ from rfl] at this
      rw [this]
      exact (IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem _ _).2 hmem
    rw [map_inv₀] at hlt
    have hne : v.adicValuation f ≠ 0 := v.adicValuation_ne_zero hf0
    have : 1 < v.adicValuation f := by
      rwa [inv_lt_one₀ (zero_lt_iff.2 hne)] at hlt
    exact absurd hle (not_le.2 this)

theorem mem_iff_ord_nonneg (v : Place ℂ F) {f : F} (hf : f ≠ 0) :
    f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f := by
  rw [mem_iff_adicValuation_le_one]
  have hne : v.adicValuation f ≠ 0 := v.adicValuation_ne_zero hf
  show v.adicValuation f ≤ 1 ↔ 0 ≤ -(WithZero.log (v.adicValuation f))
  rw [neg_nonneg, WithZero.log_le_iff_le_exp hne, WithZero.exp_zero]

theorem isRational [IsCurveOver ℂ F] (v : Place ℂ F) : v.IsRational := by
  haveI : Module.Finite ℂ v.ResidueField := IsCurveOver.finiteResidue v
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ) (K := v.ResidueField)).2

theorem evalAt_sub_algebraMap (v : Place ℂ F) (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) (c : ℂ) :
    v.evalAt (f - algebraMap ℂ F c) = v.evalAt f - c := by
  have hc : algebraMap ℂ F c ∈ v.toValuationSubring := v.algebraMap_mem' c
  have hfc : f - algebraMap ℂ F c ∈ v.toValuationSubring := v.toValuationSubring.toSubring.sub_mem hf hc
  apply v.algebraMap_residueField_injective
  rw [map_sub, v.algebraMap_evalAt hv hfc, v.algebraMap_evalAt hv hf]
  have : (⟨f - algebraMap ℂ F c, hfc⟩ : v.toValuationSubring) = ⟨f, hf⟩ - algebraMap ℂ v.toValuationSubring c := by
    apply Subtype.ext; rfl
  rw [this, map_sub]
  rfl

theorem evalAt_algebraMap (v : Place ℂ F) (hv : v.IsRational) (c : ℂ) : v.evalAt (algebraMap ℂ F c) = c := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (v.algebraMap_mem' c)]
  have : (⟨algebraMap ℂ F c, v.algebraMap_mem' c⟩ : v.toValuationSubring) = algebraMap ℂ v.toValuationSubring c :=
    Subtype.ext rfl
  rw [this]; rfl

end H2_16

open H2_16 in
theorem mem_toValuationSubring_and_evalAt_eq_of_eventuallyEq_analyticAt
    (F : Type) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧ FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [CompactSpace (Place ℂ F)] [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f) (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f) (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    (f : F) (v : Place ℂ F) (A : ℂ → ℂ) (hA : AnalyticAt ℂ A (extChartAt 𝓘(ℂ, ℂ) v v))
    (h : (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f) =ᶠ[𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) v v)] A) :
    f ∈ v.toValuationSubring ∧ Place.evalAt v f = A (extChartAt 𝓘(ℂ, ℂ) v v) := by
  classical
  haveI : HasPrincipalDivisors ℂ F := IsCurveOver.hasPrincipalDivisors
  set c₀ : ℂ := extChartAt 𝓘(ℂ, ℂ) v v with hc₀
  have hsymm0 : (extChartAt 𝓘(ℂ, ℂ) v).symm c₀ = v := by rw [hc₀]; exact extChartAt_to_inv (I := 𝓘(ℂ, ℂ)) v
  have hrat : ∀ w : Place ℂ F, w.IsRational := fun w => isRational w

  have hAlim : Filter.Tendsto A (𝓝[≠] c₀) (𝓝 (A c₀)) := hA.continuousAt.continuousWithinAt.tendsto
  have huniq : ∀ d : ℂ, Filter.Tendsto (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f) (𝓝[≠] c₀) (𝓝 d) →
      A c₀ = d := by
    intro d hd
    have h2 : Filter.Tendsto A (𝓝[≠] c₀) (𝓝 d) := hd.congr' h
    exact tendsto_nhds_unique hAlim h2
  by_cases hf0 : f = 0
  · subst hf0
    refine ⟨zero_mem _, ?_⟩
    have hz : ∀ w : Place ℂ F, Place.evalAt w (0 : F) = 0 := fun w => by
      rw [show (0 : F) = algebraMap ℂ F 0 from (map_zero _).symm, evalAt_algebraMap w (hrat w)]
    rw [hz]
    refine (huniq 0 ?_).symm
    simp only [hz]; exact tendsto_const_nhds
  · obtain ⟨hmer, hord⟩ := hF f hf0 v

    have hordA : meromorphicOrderAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f) c₀ = meromorphicOrderAt A c₀ :=
      meromorphicOrderAt_congr h
    have hnn : (0 : WithTop ℤ) ≤ (v.ord f : WithTop ℤ) := by
      rw [← hord, hordA]; exact hA.meromorphicOrderAt_nonneg
    have hord0 : 0 ≤ v.ord f := by exact_mod_cast hnn
    have hmem : f ∈ v.toValuationSubring := (mem_iff_ord_nonneg v hf0).2 hord0
    refine ⟨hmem, ?_⟩
    set c : ℂ := Place.evalAt v f with hc

    obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := ℂ) f hf0
    have hfin : {w : Place ℂ F | f ∉ w.toValuationSubring}.Finite := by
      refine (D.support.finite_toSet).subset ?_
      intro w hw
      simp only [Set.mem_setOf_eq] at hw
      rw [Finset.mem_coe, Finsupp.mem_support_iff, hD]
      intro h0
      exact hw ((mem_iff_ord_nonneg w hf0).2 (by rw [h0]))
    have hopen : IsOpen {w : Place ℂ F | f ∈ w.toValuationSubring} := by
      have : {w : Place ℂ F | f ∈ w.toValuationSubring} = {w : Place ℂ F | f ∉ w.toValuationSubring}ᶜ := by
        ext w; simp
      rw [this]; exact hfin.isClosed.isOpen_compl
    have hnear : ∀ᶠ z in 𝓝 c₀, f ∈ ((extChartAt 𝓘(ℂ, ℂ) v).symm z).toValuationSubring := by
      have : (extChartAt 𝓘(ℂ, ℂ) v).symm ⁻¹' {w : Place ℂ F | f ∈ w.toValuationSubring} ∈ 𝓝 c₀ := by
        apply (continuousAt_extChartAt_symm (I := 𝓘(ℂ, ℂ)) v).preimage_mem_nhds
        rw [hsymm0]; exact hopen.mem_nhds hmem
      exact this
    by_cases hg0 : f - algebraMap ℂ F c = 0
    ·
      have hfc : f = algebraMap ℂ F c := sub_eq_zero.1 hg0
      refine (huniq c ?_).symm
      have : (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f) = fun _ => c := by
        funext z; rw [hfc, evalAt_algebraMap _ (hrat _)]
      rw [this]; exact tendsto_const_nhds
    · obtain ⟨hmer', hord'⟩ := hF (f - algebraMap ℂ F c) hg0 v
      have hmem' : f - algebraMap ℂ F c ∈ v.toValuationSubring :=
        v.toValuationSubring.toSubring.sub_mem hmem (v.algebraMap_mem' c)
      have hzero : v.evalAt (f - algebraMap ℂ F c) = 0 := by
        rw [evalAt_sub_algebraMap _ (hrat _) hmem c, hc]; ring
      have hord1 : 1 ≤ v.ord (f - algebraMap ℂ F c) :=
        (AlgebraicCurve.Place.evalAt_eq_zero_iff_one_le_ord v (hrat v) hg0 hmem').1 hzero
      have hpos : 0 < meromorphicOrderAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) (f - algebraMap ℂ F c)) c₀ := by
        rw [hc₀, hord']; exact_mod_cast hord1
      have htend0 := tendsto_zero_of_meromorphicOrderAt_pos hpos

      have heq : (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) (f - algebraMap ℂ F c)) =ᶠ[𝓝[≠] c₀]
          fun z => A z - c := by
        filter_upwards [h, mem_nhdsWithin_of_mem_nhds hnear] with z hz hzmem
        rw [evalAt_sub_algebraMap _ (hrat _) hzmem c, hz]
      have h3 : Filter.Tendsto (fun z => A z - c) (𝓝[≠] c₀) (𝓝 0) := htend0.congr' heq
      have h4 : Filter.Tendsto (fun z => A z - c) (𝓝[≠] c₀) (𝓝 (A c₀ - c)) := hAlim.sub_const c
      have := tendsto_nhds_unique h4 h3
      rw [hc] at this
      exact (sub_eq_zero.1 this).symm

namespace K6aB15

theorem top_le_preimage_basicOpen_iff {X : Scheme.{0}} (R : Spec (CommRingCat.of ℂ) ⟶ X) (W : X.Opens)
    (e : ⊤ ≤ R ⁻¹ᵁ W) (r : Γ(X, W)) :
    ⊤ ≤ R ⁻¹ᵁ X.basicOpen r ↔ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (R.appLE W ⊤ e r) ≠ 0 := by
  have key : (⊤ : (Spec (CommRingCat.of ℂ)).Opens) ≤ R ⁻¹ᵁ X.basicOpen r ↔
      (default : ↥(Spec (CommRingCat.of ℂ))) ∈ (Spec (CommRingCat.of ℂ)).basicOpen (R.appLE W ⊤ e r) := by
    rw [Scheme.basicOpen_appLE]
    constructor
    · intro h; exact ⟨trivial, h trivial⟩
    · rintro ⟨-, h⟩ p _
      rw [Subsingleton.elim p default]; exact h
  rw [key, basicOpen_eq_of_affine']
  show (_ ∉ (default : ↥(Spec (CommRingCat.of ℂ))).asIdeal) ↔ _
  rw [Scheme.default_asIdeal, Ideal.mem_bot]

theorem eval_mul_pow_eq {X : Scheme.{0}} (U₀ U : X.Opens) (h : Γ(X, U₀)) (hDU : X.basicOpen h ≤ U)
    (s : Γ(X, U)) (a : Γ(X, U₀)) (m : ℕ)
    (hay : X.presheaf.map (homOfLE hDU).op s * (X.presheaf.map (homOfLE (X.basicOpen_le h)).op h) ^ m =
      X.presheaf.map (homOfLE (X.basicOpen_le h)).op a)
    (R : Spec (CommRingCat.of ℂ) ⟶ X) (eU : ⊤ ≤ R ⁻¹ᵁ U) (e₀ : ⊤ ≤ R ⁻¹ᵁ U₀) (eD : ⊤ ≤ R ⁻¹ᵁ X.basicOpen h) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (R.appLE U ⊤ eU s) *
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (R.appLE U₀ ⊤ e₀ h) ^ m =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (R.appLE U₀ ⊤ e₀ a) := by
  have e1 : R.appLE (X.basicOpen h) ⊤ eD (X.presheaf.map (homOfLE hDU).op s) = R.appLE U ⊤ eU s := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  have e2 : ∀ b : Γ(X, U₀), R.appLE (X.basicOpen h) ⊤ eD (X.presheaf.map (homOfLE (X.basicOpen_le h)).op b) =
      R.appLE U₀ ⊤ e₀ b := by
    intro b; rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  have := congrArg (fun z => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (R.appLE (X.basicOpen h) ⊤ eD z)) hay
  simp only [map_mul, map_pow, e1, e2] at this
  exact this

end K6aB15

open K6aB15 in

theorem solution
    (F : Type) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [CompactSpace (Place ℂ F)]
    [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    {Y : Scheme.{0}} (pY : Y ⟶ Spec (CommRingCat.of ℂ)) [IsSeparated pY] [LocallyOfFiniteType pY]
    (w : Place ℂ F → {P : Spec (CommRingCat.of ℂ) ⟶ Y // P ≫ pY = 𝟙 _})
    (hw : ∀ (U : Y.Opens), IsAffineOpen U → ∀ (φ : Γ(Y, U)),
      IsOpen {v : Place ℂ F | ⊤ ≤ (w v).1 ⁻¹ᵁ U} ∧
      ∃ G : Place ℂ F → ℂ,
        (∀ (v : Place ℂ F) (h : ⊤ ≤ (w v).1 ⁻¹ᵁ U),
          G v = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((w v).1.appLE U ⊤ h) φ)) ∧
        ∀ v : Place ℂ F, ⊤ ≤ (w v).1 ⁻¹ᵁ U →
          DifferentiableAt ℂ (fun z : ℂ => G ((extChartAt 𝓘(ℂ, ℂ) v).symm z))
            (extChartAt 𝓘(ℂ, ℂ) v v))
    (U : Y.Opens) (hU : IsAffineOpen U) (hne : ∃ v : Place ℂ F, ⊤ ≤ (w v).1 ⁻¹ᵁ U) (φ : Γ(Y, U)) :
    ∃! ξ : F, ∀ (v : Place ℂ F) (h : ⊤ ≤ (w v).1 ⁻¹ᵁ U),
      ξ ∈ v.toValuationSubring ∧ Place.evalAt v ξ = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((w v).1.appLE U ⊤ h) φ) := by
  classical
  set O : Set (Place ℂ F) := {v | ⊤ ≤ (w v).1 ⁻¹ᵁ U} with hO_def
  have hO : IsOpen O := (hw U hU 1).1
  obtain ⟨G, hG, hGd⟩ := (hw U hU φ).2

  have hfin : Set.Finite {v : Place ℂ F | ¬ (⊤ ≤ (w v).1 ⁻¹ᵁ U)} := by
    rcases AlgebraicCurve.Place.forall_not_le_preimage_or_finite_setOf_of_differentiableAt_appLE_of_isSeparated
      F hfg hF pY w hw U hU with h | h
    · obtain ⟨v, hv⟩ := hne; exact absurd hv (h v)
    · exact h

  let g : Place ℂ F → ℂ := fun v => if ⊤ ≤ (w v).1 ⁻¹ᵁ U then G v else 0
  have hgO : ∀ v ∈ O, g v = G v := fun v hv => if_pos hv

  have hGan : ∀ v ∈ O, AnalyticAt ℂ (fun z : ℂ => G ((extChartAt 𝓘(ℂ, ℂ) v).symm z)) (extChartAt 𝓘(ℂ, ℂ) v v) :=
    fun v hv => analyticAt_extChartAt_symm_of_forall_differentiableAt G O hO hGd v hv

  have hgmer : ∀ v : Place ℂ F, MeromorphicAt (fun z : ℂ => g ((extChartAt 𝓘(ℂ, ℂ) v).symm z)) (extChartAt 𝓘(ℂ, ℂ) v v) := by
    intro v
    by_cases hvO : v ∈ O
    · have h1 : (fun z : ℂ => g ((extChartAt 𝓘(ℂ, ℂ) v).symm z)) =ᶠ[𝓝 (extChartAt 𝓘(ℂ, ℂ) v v)]
          (fun z : ℂ => G ((extChartAt 𝓘(ℂ, ℂ) v).symm z)) := by
        have hc : ContinuousAt (extChartAt 𝓘(ℂ, ℂ) v).symm (extChartAt 𝓘(ℂ, ℂ) v v) := continuousAt_extChartAt_symm v
        have : ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) v v), (extChartAt 𝓘(ℂ, ℂ) v).symm z ∈ O := by
          apply hc.preimage_mem_nhds
          rw [extChartAt_to_inv]; exact hO.mem_nhds hvO
        exact this.mono (fun z hz => hgO _ hz)
      exact (hGan v hvO).meromorphicAt.congr (h1.symm.filter_mono nhdsWithin_le_nhds)
    ·
      set c := extChartAt 𝓘(ℂ, ℂ) v with hc_def

      obtain ⟨_, ⟨U'', hU'', rfl⟩, hyU'', -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ ((w v).1.base default)) isOpen_univ
      have hv'' : ⊤ ≤ (w v).1 ⁻¹ᵁ (U'' : Y.Opens) := by
        intro p _; rw [Subsingleton.elim p default]; exact hyU''
      have hO'' : IsOpen {u : Place ℂ F | ⊤ ≤ (w u).1 ⁻¹ᵁ (U'' : Y.Opens)} := (hw U'' hU'' 1).1

      have hOv : IsOpen {u : Place ℂ F | u ∈ O ∨ u = v} := by
        have : {u : Place ℂ F | u ∈ O ∨ u = v} = ({u : Place ℂ F | ¬ (⊤ ≤ (w u).1 ⁻¹ᵁ U)} \ {v})ᶜ := by
          ext u; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_diff, Set.mem_singleton_iff, not_and, not_not]
          show u ∈ O ∨ u = v ↔ (¬ (u ∈ O) → u = v)
          tauto
        rw [this, isOpen_compl_iff]
        exact (hfin.subset Set.diff_subset).isClosed

      have hN : c.target ∩ c.symm ⁻¹' (c.source ∩ ({u | ⊤ ≤ (w u).1 ⁻¹ᵁ (U'' : Y.Opens)} ∩ {u | u ∈ O ∨ u = v})) ∈ 𝓝 (c v) := by
        apply Filter.inter_mem (extChartAt_target_mem_nhds v)
        apply (continuousAt_extChartAt_symm v).preimage_mem_nhds
        rw [hc_def, extChartAt_to_inv]
        exact ((isOpen_extChartAt_source v).inter (hO''.inter hOv)).mem_nhds ⟨mem_extChartAt_source v, hv'', Or.inr rfl⟩
      obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hN

      set z₁ : ℂ := c v + ((r / 2 : ℝ) : ℂ) with hz₁
      have hz₁ball : z₁ ∈ Metric.ball (c v) r := by
        rw [Metric.mem_ball, hz₁, dist_self_add_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
        linarith
      have hz₁ne : z₁ ≠ c v := by
        intro h
        have h2 : ((r / 2 : ℝ) : ℂ) = 0 := add_left_cancel (a := c v) (by rw [← hz₁, h, add_zero])
        have : (r / 2 : ℝ) = 0 := by exact_mod_cast h2
        linarith
      obtain ⟨hz₁t, hz₁s, hz₁'', hz₁O⟩ := hball hz₁ball
      have hv₁ne : c.symm z₁ ≠ v := by
        intro h
        apply hz₁ne
        have h' : c.symm z₁ = c.symm (c v) := by rw [h, hc_def, extChartAt_to_inv]
        exact c.symm.injOn hz₁t (by rw [c.symm_source]; exact mem_extChartAt_target v) h'
      have hv₁O : ⊤ ≤ (w (c.symm z₁)).1 ⁻¹ᵁ U := hz₁O.resolve_right hv₁ne
      have hy₁U : (w (c.symm z₁)).1.base default ∈ U := hv₁O (show default ∈ (⊤ : (Spec (CommRingCat.of ℂ)).Opens) from trivial)
      have hy₁U'' : (w (c.symm z₁)).1.base default ∈ (U'' : Y.Opens) :=
        hz₁'' (show default ∈ (⊤ : (Spec (CommRingCat.of ℂ)).Opens) from trivial)
      obtain ⟨b, hbU, hy₁b⟩ := hU''.exists_basicOpen_le ⟨(w (c.symm z₁)).1.base default, hy₁U⟩ hy₁U''

      obtain ⟨Gb, hGb, hGbd⟩ := (hw U'' hU'' b).2
      have hGb_an : AnalyticAt ℂ (fun z : ℂ => Gb (c.symm z)) (c v) :=
        analyticAt_extChartAt_symm_of_forall_differentiableAt Gb _ hO'' hGbd v hv''
      have hGb_on : AnalyticOnNhd ℂ (fun z : ℂ => Gb (c.symm z)) (Metric.ball (c v) r) := by
        intro z hz
        obtain ⟨hzt, hzs, hz'', -⟩ := hball hz
        exact analyticAt_extChartAt_symm_of_mem_of_forall_differentiableAt Gb _ hO'' hGbd v ⟨hzt, hzs, hz''⟩
      have hGb_v₁ : Gb (c.symm z₁) ≠ 0 := by
        rw [hGb _ hz₁'']
        exact (top_le_preimage_basicOpen_iff (w (c.symm z₁)).1 U'' hz₁'' b).1
          (fun p _ => by rw [Subsingleton.elim p default]; exact hy₁b)
      have hne_ev : ∀ᶠ z in 𝓝[≠] (c v), Gb (c.symm z) ≠ 0 := by
        rcases hGb_an.eventually_eq_zero_or_eventually_ne_zero with h0 | h1
        · exfalso
          have := hGb_on.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball (c v) r).isPreconnected
            (Metric.mem_ball_self hr) h0 hz₁ball
          exact hGb_v₁ this
        · exact h1

      letI := hU''.isLocalization_basicOpen b
      obtain ⟨⟨a, ⟨_, m, rfl⟩⟩, hay⟩ :=
        IsLocalization.surj (Submonoid.powers b) (Y.presheaf.map (homOfLE hbU).op φ)
      have hay' : Y.presheaf.map (homOfLE hbU).op φ *
          (Y.presheaf.map (homOfLE (Y.basicOpen_le b)).op b) ^ m =
          Y.presheaf.map (homOfLE (Y.basicOpen_le b)).op a := by
        have := hay; simp only [map_pow] at this; exact this
      obtain ⟨Ga, hGa, hGad⟩ := (hw U'' hU'' a).2
      have hGa_an : AnalyticAt ℂ (fun z : ℂ => Ga (c.symm z)) (c v) :=
        analyticAt_extChartAt_symm_of_forall_differentiableAt Ga _ hO'' hGad v hv''
      have key : ∀ᶠ z in 𝓝[≠] (c v), g (c.symm z) = Ga (c.symm z) / Gb (c.symm z) ^ m := by
        have hball' : ∀ᶠ z in 𝓝[≠] (c v), z ∈ Metric.ball (c v) r := nhdsWithin_le_nhds (Metric.ball_mem_nhds _ hr)
        filter_upwards [hne_ev, hball'] with z hz hzb
        obtain ⟨hzt, hzs, hz'', -⟩ := hball hzb
        have hbval : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((w (c.symm z)).1.appLE (U'' : Y.Opens) ⊤ hz'') b) ≠ 0 := by
          rw [← hGb _ hz'']; exact hz
        have huD : ⊤ ≤ (w (c.symm z)).1 ⁻¹ᵁ Y.basicOpen b := (top_le_preimage_basicOpen_iff _ _ hz'' b).2 hbval
        have huU : ⊤ ≤ (w (c.symm z)).1 ⁻¹ᵁ U := le_trans huD (fun p hp => hbU hp)
        have hgu : g (c.symm z) = G (c.symm z) := if_pos huU
        rw [hgu, hG _ huU, hGa _ hz'', hGb _ hz'', eq_div_iff (pow_ne_zero m hbval)]
        exact eval_mul_pow_eq (U'' : Y.Opens) U b hbU φ a m hay' (w (c.symm z)).1 huU hz'' huD
      refine ((hGa_an.meromorphicAt).div ((hGb_an.meromorphicAt).pow m)).congr ?_
      exact key.mono (fun z hz => by simp only [Pi.div_apply, Pi.pow_apply]; exact hz.symm)
  obtain ⟨ξ, hξ⟩ := AlgebraicCurve.exists_eventuallyEq_evalAt_of_meromorphicAt F hfg hF g hgmer

  have hex : ∀ (v : Place ℂ F) (h : ⊤ ≤ (w v).1 ⁻¹ᵁ U),
      ξ ∈ v.toValuationSubring ∧ Place.evalAt v ξ = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((w v).1.appLE U ⊤ h) φ) := by
    intro v hv
    have hvO : v ∈ O := hv

    have h1 : (fun z : ℂ => g ((extChartAt 𝓘(ℂ, ℂ) v).symm z)) =ᶠ[𝓝 (extChartAt 𝓘(ℂ, ℂ) v v)]
        (fun z : ℂ => G ((extChartAt 𝓘(ℂ, ℂ) v).symm z)) := by
      have hc : ContinuousAt (extChartAt 𝓘(ℂ, ℂ) v).symm (extChartAt 𝓘(ℂ, ℂ) v v) := continuousAt_extChartAt_symm v
      have : ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) v v), (extChartAt 𝓘(ℂ, ℂ) v).symm z ∈ O := by
        apply hc.preimage_mem_nhds
        rw [extChartAt_to_inv]; exact hO.mem_nhds hvO
      exact this.mono (fun z hz => hgO _ hz)
    have h2 := ((hξ v).symm.trans (h1.filter_mono nhdsWithin_le_nhds))
    have := mem_toValuationSubring_and_evalAt_eq_of_eventuallyEq_analyticAt F hfg hF ξ v _ (hGan v hvO) h2
    rw [extChartAt_to_inv, hG v hv] at this
    exact this

  refine ⟨ξ, hex, fun ξ' hξ' => ?_⟩

  by_contra hne'
  have hd0 : ξ' - ξ ≠ 0 := sub_ne_zero.2 hne'

  have hrat : ∀ v : Place ℂ F, v.IsRational := by
    intro v
    haveI : Module.Finite ℂ v.ResidueField := IsCurveOver.finiteResidue v
    haveI : Algebra.IsIntegral ℂ v.ResidueField := Algebra.IsIntegral.of_finite ℂ v.ResidueField
    exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ) (K := v.ResidueField)).2

  have hord : ∀ v ∈ O, v.ord (ξ' - ξ) ≠ 0 := by
    intro v hv
    obtain ⟨h1, h1v⟩ := hex v hv
    obtain ⟨h2, h2v⟩ := hξ' v hv
    have hmem : ξ' - ξ ∈ v.toValuationSubring := v.toValuationSubring.sub_mem h2 h1
    have hres : IsLocalRing.residue v.toValuationSubring ⟨ξ' - ξ, hmem⟩ = 0 := by
      have e : (⟨ξ' - ξ, hmem⟩ : v.toValuationSubring) = ⟨ξ', h2⟩ - ⟨ξ, h1⟩ := rfl
      rw [e, map_sub, ← Place.algebraMap_evalAt v (hrat v) h2, ← Place.algebraMap_evalAt v (hrat v) h1, h2v, h1v, sub_self]
    have hmax : (⟨ξ' - ξ, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring :=
      (IsLocalRing.residue_eq_zero_iff _).1 hres
    have hnu : ¬ IsUnit (⟨ξ' - ξ, hmem⟩ : v.toValuationSubring) := (IsLocalRing.mem_maximalIdeal _).1 hmax
    have hne1 : v.adicValuation (ξ' - ξ) ≠ 1 := fun h => hnu ((v.adicValuation_coe_eq_one_iff ⟨ξ' - ξ, hmem⟩).1 h)
    have hne0 : v.adicValuation (ξ' - ξ) ≠ 0 := v.adicValuation_ne_zero hd0
    intro h0
    apply hne1
    simp only [Place.ord, neg_eq_zero] at h0
    rw [← WithZero.exp_log hne0, h0, WithZero.exp_zero]

  obtain ⟨v₀, hv₀⟩ := hne
  have hv₀O : v₀ ∈ O := hv₀
  have hOinf : O.Infinite := by
    let c := extChartAt 𝓘(ℂ, ℂ) v₀
    have hS : IsOpen (c.target ∩ c.symm ⁻¹' (c.source ∩ O)) :=
      (continuousOn_extChartAt_symm v₀).isOpen_inter_preimage (isOpen_extChartAt_target v₀)
        ((isOpen_extChartAt_source v₀).inter hO)
    have hmemS : c v₀ ∈ c.target ∩ c.symm ⁻¹' (c.source ∩ O) :=
      ⟨mem_extChartAt_target v₀, by
        show c.symm (c v₀) ∈ c.source ∩ O
        rw [extChartAt_to_inv]; exact ⟨mem_extChartAt_source v₀, hv₀O⟩⟩
    have hSinf : (c.target ∩ c.symm ⁻¹' (c.source ∩ O)).Infinite := infinite_of_mem_nhds (c v₀) (hS.mem_nhds hmemS)
    exact Set.infinite_of_injOn_mapsTo (f := c.symm) (fun x hx y hy hxy => c.symm.injOn hx.1 hy.1 hxy)
      (fun x hx => hx.2.2) hSinf

  obtain ⟨D, hD, -⟩ := (IsCurveOver.hasPrincipalDivisors (K := ℂ) (F := F)).exists_divisor (ξ' - ξ) hd0
  have hsub : O ⊆ (D.support : Set (Place ℂ F)) := fun v hv => by
    rw [Finset.mem_coe, Finsupp.mem_support_iff, hD v]; exact hord v hv
  exact hOinf (D.support.finite_toSet.subset hsub)

end S_AlgebraicCurve_Place_existsUnique_forall_mem_toValuationSubring_and_evalAt_eq_appLE_of_differentiableAt
end P2MW
export P2MW.S_AlgebraicCurve_Place_existsUnique_forall_mem_toValuationSubring_and_evalAt_eq_appLE_of_differentiableAt (solution)
