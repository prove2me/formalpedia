-- Prove2me | solution 1 for AlgebraicCurve.exists_finset_card_le_span_eq_pathPeriodLattice
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/e9c202fd-edca-58ab-a083-059d8befe1b3

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_ComplexLineIntegral
import Theorems.Thm_AlgebraicCurve_exists_isUnit_det_evalAt_differentialCoeff
import Theorems.Thm_AlgebraicCurve_exists_abelJacobiDiv_sub_mem_pathPeriodLattice_and_image_mem_nhds
import Theorems.Thm_AlgebraicCurve_Divisor_isPrincipal_of_abelJacobiDiv_mem_pathPeriodLattice
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_finset_card_le_span_eq_pathPeriodLattice
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion"
p2m_attr_erase "instance" "AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_exists_finset_card_le_span_eq_pathPeriodLattice.AlgebraicCurve Filter Topology Set"
open scoped Manifold ContDiff Topology

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor Divisor.degree Divisor.degree_single IsCurveOver IsCurveOver.deg_eq_one_of_isAlgClosed HasCanonicalDivisor Place.evalAt regularDifferentials abelJacobiDiv pathPeriodLattice exists_isUnit_det_evalAt_differentialCoeff exists_abelJacobiDiv_sub_mem_pathPeriodLattice_and_image_mem_nhds Divisor.isPrincipal_of_abelJacobiDiv_mem_pathPeriodLattice"
namespace PeriodLatticeGeneratorsProof
p2m_open "AlgebraicCurve"

section Lattice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_finset_card_le_span_eq_of_discrete (L : Submodule ℤ E) [DiscreteTopology L] :
    ∃ s : Finset E, s.card ≤ Module.finrank ℝ E ∧ Submodule.span ℤ (s : Set E) = L := by
  classical

  set W : Submodule ℝ E := Submodule.span ℝ (L : Set E) with hW
  set L' : Submodule ℤ W := L.comap (W.subtype.restrictScalars ℤ) with hL'
  have hmemL' : ∀ x : W, x ∈ L' ↔ (x : E) ∈ L := fun x => Iff.rfl

  haveI : DiscreteTopology L' := by
    have h0 : IsOpen ({0} : Set L) := isOpen_discrete _
    obtain ⟨t, ht, hpre⟩ := isOpen_induced_iff.1 h0
    refine discreteTopology_of_isOpen_singleton_zero ?_
    refine isOpen_induced_iff.2 ⟨((↑) : W → E) ⁻¹' t, ht.preimage continuous_subtype_val, ?_⟩
    ext x
    simp only [mem_preimage, mem_singleton_iff]
    have hx : ((x : W) : E) ∈ L := (hmemL' x).1 x.2
    have key : (⟨((x : W) : E), hx⟩ : L) ∈ ((↑) : L → E) ⁻¹' t ↔ (⟨((x : W) : E), hx⟩ : L) = 0 := by
      rw [hpre]; exact Iff.rfl
    simp only [mem_preimage] at key
    rw [key]
    constructor
    · intro h
      have h' : ((x : W) : E) = 0 := by simpa using congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext (by simpa using h'))
    · intro h
      subst h
      exact Subtype.ext rfl

  haveI : IsZLattice ℝ L' := by
    refine ⟨?_⟩
    apply Submodule.map_injective_of_injective (f := W.subtype) W.injective_subtype
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
    apply le_antisymm
    · exact Submodule.span_le.2 (by
        rintro _ ⟨x, hx, rfl⟩
        exact Submodule.subset_span ((hmemL' x).1 hx))
    · refine Submodule.span_le.2 fun y hy => Submodule.subset_span ?_
      exact ⟨⟨y, Submodule.subset_span hy⟩, (hmemL' _).2 hy, rfl⟩
  haveI : Module.Free ℤ L' := ZLattice.module_free ℝ L'
  haveI : Module.Finite ℤ L' := ZLattice.module_finite ℝ L'
  have hrank : Module.finrank ℤ L' = Module.finrank ℝ W := ZLattice.rank ℝ L'

  set B := Module.finBasis ℤ L' with hB
  set ψ : L' →ₗ[ℤ] E := (W.subtype.restrictScalars ℤ).comp L'.subtype with hψ
  have hψ_apply : ∀ x : L', ψ x = ((x : W) : E) := fun x => rfl
  refine ⟨Finset.univ.image fun k => ψ (B k), ?_, ?_⟩
  · calc (Finset.univ.image fun k => ψ (B k)).card ≤ Finset.univ.card := Finset.card_image_le
      _ = Module.finrank ℤ L' := by simp
      _ = Module.finrank ℝ W := hrank
      _ ≤ Module.finrank ℝ E := Submodule.finrank_le W
  · apply le_antisymm
    · refine Submodule.span_le.2 ?_
      rintro _ hx
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
      rw [hψ_apply]
      exact (hmemL' _).1 (B k).2
    · intro y hy
      have hy' : (⟨⟨y, Submodule.subset_span hy⟩, (hmemL' _).2 hy⟩ : L') ∈
          Submodule.span ℤ (Set.range B) := by
        rw [B.span_eq]; exact Submodule.mem_top
      have himg := Submodule.mem_map_of_mem (f := ψ) hy'
      rw [Submodule.map_span] at himg
      have hyψ : ψ ⟨⟨y, Submodule.subset_span hy⟩, (hmemL' _).2 hy⟩ = y := rfl
      rw [hyψ] at himg
      refine Submodule.span_mono ?_ himg
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨k, Finset.mem_univ _, rfl⟩)

end Lattice

section Discrete

variable {E : Type*} [NormedAddCommGroup E]

theorem discreteTopology_of_nhds_inter (L : Submodule ℤ E) {V : Set E} (hV : V ∈ 𝓝 (0 : E))
    (h : ∀ x ∈ L, x ∈ V → x = 0) : DiscreteTopology L := by
  refine discreteTopology_of_isOpen_singleton_zero ?_
  refine isOpen_induced_iff.2 ⟨interior V, isOpen_interior, ?_⟩
  ext x
  simp only [mem_preimage, mem_singleton_iff]
  constructor
  · intro hx
    exact Subtype.ext (h x x.2 (interior_subset hx))
  · rintro rfl
    exact mem_interior_iff_mem_nhds.2 hV

end Discrete

section Divisors

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem sum_single_apply_nonneg {n : ℕ} (P : Fin n → Place K F) (w : Place K F) :
    0 ≤ (∑ k, Finsupp.single (P k) (1 : ℤ) : Divisor K F) w := by
  classical
  rw [Finsupp.finsetSum_apply]
  exact Finset.sum_nonneg fun k _ => by
    rw [Finsupp.single_apply]; split_ifs <;> norm_num

theorem ord_algebraMap (w : Place K F) (c : K) : w.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  have hu : IsUnit (⟨algebraMap K F c, w.algebraMap_mem' c⟩ : w.toValuationSubring) := by
    refine ⟨⟨⟨algebraMap K F c, w.algebraMap_mem' c⟩, ⟨algebraMap K F c⁻¹, w.algebraMap_mem' c⁻¹⟩,
      ?_, ?_⟩, rfl⟩
    · ext; simp [hc]
    · ext; simp [hc]
  exact w.ord_coe_unit hu.unit

end Divisors

section Separation

variable {X : Type*} [TopologicalSpace X] [T2Space X]

theorem exists_nhds_eq_of_sum_single_eq {n : ℕ} {v : Fin n → X} (hv : Function.Injective v) :
    ∃ W : Fin n → Set X, (∀ j, W j ∈ 𝓝 (v j)) ∧
      ∀ P : Fin n → X, (∀ j, P j ∈ W j) →
        (∑ k, Finsupp.single (P k) (1 : ℤ) : X →₀ ℤ) = ∑ k, Finsupp.single (v k) (1 : ℤ) →
          P = v := by
  classical
  obtain ⟨U, hU, hdisj⟩ := (Set.finite_range v).t2_separation
  refine ⟨fun j => U (v j), fun j => (hU (v j)).2.mem_nhds (hU (v j)).1, ?_⟩
  intro P hP hsum
  funext j
  have hj := congrArg (fun D : X →₀ ℤ => D (v j)) hsum
  simp only [Finsupp.finsetSum_apply] at hj

  have hR : (∑ k, (Finsupp.single (v k) (1 : ℤ)) (v j)) = 1 := by
    rw [Finset.sum_eq_single j (fun k _ hkj => by
        rw [Finsupp.single_apply, if_neg (fun h => hkj (hv h))])
      (fun h => absurd (Finset.mem_univ j) h), Finsupp.single_eq_same]

  have hL : (∑ k, (Finsupp.single (P k) (1 : ℤ)) (v j)) = (Finsupp.single (P j) (1 : ℤ)) (v j) := by
    refine Finset.sum_eq_single j ?_ (fun h => absurd (Finset.mem_univ j) h)
    intro k _ hkj
    rw [Finsupp.single_apply, if_neg]
    intro hk
    have hne : v k ≠ v j := fun h => hkj (hv h)
    have hd : Disjoint (U (v k)) (U (v j)) :=
      hdisj (Set.mem_range_self k) (Set.mem_range_self j) hne
    exact Set.disjoint_left.1 hd (hP k) (hk ▸ (hU (v j)).1)
  rw [hR, hL] at hj
  by_contra hne
  rw [Finsupp.single_apply, if_neg hne] at hj
  exact zero_ne_one hj

end Separation

end AlgebraicCurve.PeriodLatticeGeneratorsProof

open AlgebraicCurve.PeriodLatticeGeneratorsProof in
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
    {n : ℕ} (b : Module.Basis (Fin n) ℂ ↥(regularDifferentials ℂ F)) :
    ∃ s : Finset (Fin n → ℂ), s.card ≤ 2 * n ∧
      Submodule.span ℤ (s : Set (Fin n → ℂ)) = pathPeriodLattice (fun i => (b i : Ω[F⁄ℂ])) := by
  classical
  set bΩ : Fin n → Ω[F⁄ℂ] := fun i => (b i : Ω[F⁄ℂ]) with hbΩ
  set Λ : Submodule ℤ (Fin n → ℂ) := pathPeriodLattice bΩ with hΛ

  haveI : DiscreteTopology Λ := by

    obtain ⟨v, hvinj, hdet, hnonspecial⟩ :=
      AlgebraicCurve.exists_isUnit_det_evalAt_differentialCoeff (K := ℂ) (F := F) hfg b

    haveI : Nonempty (Place ℂ F) := ConnectedSpace.toNonempty
    obtain ⟨P₀⟩ : Nonempty (Place ℂ F) := inferInstance

    obtain ⟨Φ, hΦv, hopen, hcong⟩ :=
      AlgebraicCurve.exists_abelJacobiDiv_sub_mem_pathPeriodLattice_and_image_mem_nhds F hfg hF
        bΩ (fun i => (b i).2) v hdet P₀

    obtain ⟨W, hW, hWeq⟩ := exists_nhds_eq_of_sum_single_eq (X := Place ℂ F) hvinj

    set U : Set (Fin n → Place ℂ F) := Set.pi Set.univ W ∩
      {P | abelJacobiDiv bΩ P₀ ((∑ j, Finsupp.single (P j) 1) - ∑ j, Finsupp.single (v j) 1) - Φ P
        ∈ pathPeriodLattice bΩ} with hU
    have hUmem : U ∈ 𝓝 v :=
      Filter.inter_mem (set_pi_mem_nhds Set.finite_univ fun j _ => hW j) hcong
    refine discreteTopology_of_nhds_inter Λ (hopen U hUmem) ?_
    rintro x hx ⟨P, ⟨hPW, hPcong⟩, rfl⟩

    set D : Divisor ℂ F := (∑ j, Finsupp.single (P j) 1) - ∑ j, Finsupp.single (v j) 1 with hD
    have hAJ : abelJacobiDiv bΩ P₀ D ∈ pathPeriodLattice bΩ := by
      have := (pathPeriodLattice bΩ).add_mem hPcong hx
      rwa [sub_add_cancel] at this

    have hdeg : Divisor.degree D = 0 := by
      simp only [hD, map_sub, map_sum, Divisor.degree_single,
        IsCurveOver.deg_eq_one_of_isAlgClosed, Nat.cast_one, mul_one, sub_self]

    obtain ⟨f, hf0, hf⟩ :=
      AlgebraicCurve.Divisor.isPrincipal_of_abelJacobiDiv_mem_pathPeriodLattice F hfg hF b P₀ D
        hdeg hAJ

    have hfL : ∀ w : Place ℂ F,
        -((∑ j, Finsupp.single (v j) (1 : ℤ) : Divisor ℂ F) w) ≤ w.ord f := by
      intro w
      rw [← hf w, hD, Finsupp.sub_apply]
      linarith [sum_single_apply_nonneg P w]
    obtain ⟨c, rfl⟩ := hnonspecial f hfL

    have hDzero : (∑ j, Finsupp.single (P j) (1 : ℤ) : Divisor ℂ F) =
        ∑ j, Finsupp.single (v j) (1 : ℤ) := by
      rw [← sub_eq_zero]
      ext w
      have := hf w
      rw [ord_algebraMap] at this
      simpa [hD] using this
    have hPv : P = v := hWeq P (fun j => hPW j (Set.mem_univ j)) hDzero
    rw [hPv, hΦv]

  obtain ⟨s, hs, hspan⟩ := exists_finset_card_le_span_eq_of_discrete (E := Fin n → ℂ) Λ
  refine ⟨s, ?_, hspan⟩
  have hfin : Module.finrank ℝ (Fin n → ℂ) = 2 * n := by
    rw [finrank_real_of_complex, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  omega

end

end S_AlgebraicCurve_exists_finset_card_le_span_eq_pathPeriodLattice
end P2MW
export P2MW.S_AlgebraicCurve_exists_finset_card_le_span_eq_pathPeriodLattice (solution)
