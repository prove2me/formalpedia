-- Prove2me | solution 1 for AlgebraicCurve.exists_loops_pathIntegral_reciprocity_raw
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/f6ea92e7-afca-5807-b612-9da3c6d97168

import Definitions.Def_AlgebraicCurve_CellDissection
import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_ComplexLineIntegral
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_exists_isPrimitiveAlong_of_forall_ordDifferential_nonneg
import Theorems.Thm_exists_fundamentalCycles_of_spanningTree
import Theorems.Thm_ZMod_chordMatrix_transpose_eq_neg
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_span_real_pathPeriodLattice_eq_top
import Theorems.Thm_AlgebraicCurve_coeffIn_local_calculus
import Theorems.Thm_AlgebraicCurve_CellDissection_two_pi_I_mul_sum_residue_mul_primitive_eq_sum_jump_mul_edgeInt
import Theorems.Thm_AlgebraicCurve_CellDissection_exists_int_pathIntegral_sub_primitive_eq_sum_jump
import Theorems.Thm_AlgebraicCurve_CellDissection_exists_loop_pathIntegral_eq_sum_cycle_mul_edgeInt
import Theorems.Thm_AlgebraicCurve_pathIntegral_finset_sum_smul
import Theorems.Thm_AlgebraicCurve_CellDissection_intervalIntegral_bdryIntegrand_neg_eq_neg_edgeInt
import Theorems.Thm_AlgebraicCurve_RadialRegion_exists_isOpen_starConvex_subset
import Theorems.Thm_AlgebraicCurve_CellDissection_exists_int_pathIntegral_eq_sum_periods_add_sum_residues
import Theorems.Thm_AlgebraicCurve_CellDissection_exists_primitives_jump_eq_zero_of_dualTree
import Theorems.Thm_AlgebraicCurve_CellDissection_jump_kirchhoff_and_wordFormula_of_primitives
import Theorems.Thm_AlgebraicCurve_exists_cellDissection
import Theorems.Thm_AlgebraicCurve_CellDissection_exists_tree_cotree
import Theorems.Thm_AlgebraicCurve_CellDissection_exists_polygonWord
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_loops_pathIntegral_reciprocity_raw
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "RadialRegion Cell CellDissection coeffIn CellDissection.skeleton Place.evalAt Place Place.FiniteResidue Divisor Place.FiniteResidue.finite IsPrimitiveAlong pathIntegral pathIntegral_def abelJacobiVec abelJacobiVec_def abelJacobiDiv abelJacobiDiv_apply pathPeriodLattice regularDifferentials IsCurveOver IsCurveOver.instNontrivialKaehler HasCanonicalDivisor dCoordGenerates_of_isCurveOver exists_isPrimitiveAlong_of_forall_ordDifferential_nonneg essFiniteType_of_transcendental_of_finiteDimensional span_real_pathPeriodLattice_eq_top coeffIn_local_calculus CellDissection.two_pi_I_mul_sum_residue_mul_primitive_eq_sum_jump_mul_edgeInt CellDissection.exists_int_pathIntegral_sub_primitive_eq_sum_jump CellDissection.exists_loop_pathIntegral_eq_sum_cycle_mul_edgeInt pathIntegral_finset_sum_smul CellDissection.intervalIntegral_bdryIntegrand_neg_eq_neg_edgeInt RadialRegion.exists_isOpen_starConvex_subset CellDissection.exists_int_pathIntegral_eq_sum_periods_add_sum_residues CellDissection.exists_primitives_jump_eq_zero_of_dualTree CellDissection.jump_kirchhoff_and_wordFormula_of_primitives exists_cellDissection CellDissection.exists_tree_cotree CellDissection.exists_polygonWord"
namespace Cell
p2m_export "AlgebraicCurve.Cell" "carrier interior' bdry arc bdryIntegrand mk mk.injEq hKt R"
p2m_open "AlgebraicCurve.Cell AlgebraicCurve"
variable {F : Type*} [Field F] [Algebra ℂ F] [TopologicalSpace (Place ℂ F)]
  [ChartedSpace ℂ (Place ℂ F)]

private def _root_.AlgebraicCurve.Cell.U (C : Cell F) : Set ℂ := C.ζ.target
p2m_export "AlgebraicCurve.Cell" "U"
theorem hU (C : Cell F) : IsOpen C.U := C.ζ.open_target
private theorem _root_.AlgebraicCurve.Cell.hKU (C : Cell F) : C.R.K ⊆ C.U := C.hKt
p2m_export "AlgebraicCurve.Cell" "hKU"
private theorem _root_.AlgebraicCurve.Cell.hUt (C : Cell F) : C.U ⊆ C.ζ.target := fun _ h => h
p2m_export "AlgebraicCurve.Cell" "hUt"
end AlgebraicCurve.Cell

section Part_coeff

open scoped Manifold ContDiff Topology
p2m_open "Set Filter AlgebraicCurve P2MW.S_AlgebraicCurve_exists_loops_pathIntegral_reciprocity_raw.AlgebraicCurve"

namespace ChartTransition

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

end ChartTransition

namespace CellCoeff

section Local

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

end Local

section PlaceAlgebra

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

theorem isRational_of_isAlgClosed [IsAlgClosed K] (w : Place K F) [w.FiniteResidue] :
    w.IsRational := by
  haveI : Module.Finite K w.ResidueField := Place.FiniteResidue.finite
  haveI : Algebra.IsIntegral K w.ResidueField := Algebra.IsIntegral.of_finite K _
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := w.ResidueField)).2

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

theorem differentialCoeff_mem (v : AlgebraicCurve.Place K F) [v.DCoordGenerates] {θ : Ω[F⁄K]}
    (hθ : 0 ≤ v.ordDifferential θ) : v.differentialCoeff θ ∈ v.toValuationSubring := by
  by_cases h0 : v.differentialCoeff θ = 0
  · rw [h0]; exact zero_mem _
  · exact v.mem_toValuationSubring_of_ord_nonneg_alt h0 hθ

theorem dCoordFn_mul_differentialCoeff_mem (v : AlgebraicCurve.Place K F) [v.DCoordGenerates]
    {θ : Ω[F⁄K]} (hθ : -1 ≤ v.ordDifferential θ) :
    v.dCoordFn * v.differentialCoeff θ ∈ v.toValuationSubring := by
  by_cases h0 : v.differentialCoeff θ = 0
  · rw [h0, mul_zero]; exact zero_mem _
  have h1 := v.ord_dCoordFn
  have hπ0 : v.dCoordFn ≠ 0 := by
    intro h'
    rw [h', v.ord_zero] at h1
    exact zero_ne_one h1
  refine v.mem_toValuationSubring_of_ord_nonneg_alt (mul_ne_zero hπ0 h0) ?_
  rw [v.ord_mul hπ0 h0, h1]
  have : -1 ≤ v.ord (v.differentialCoeff θ) := hθ
  omega

end Place

end PlaceAlgebra

section Analysis

end Analysis

section Spread

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [IsCurveOver ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

end Spread

section Main

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

variable
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))

end Main

end CellCoeff

end Part_coeff

section Part_book_cell

namespace CellPeriods

p2m_open "Complex MeasureTheory Set Filter intervalIntegral AlgebraicCurve P2MW.S_AlgebraicCurve_exists_loops_pathIntegral_reciprocity_raw.AlgebraicCurve"
open scoped Real Topology Interval Manifold ContDiff

noncomputable def γ (c : ℂ) (r : ℝ → ℝ) (φ : ℝ) : ℂ := c + (r φ : ℂ) * exp (φ * I)

theorem norm_exp_mul_I (φ : ℝ) : ‖exp (φ * I)‖ = 1 := norm_exp_ofReal_mul_I φ

theorem exp_mul_I_add_two_pi (φ : ℝ) : exp (((φ + 2 * π : ℝ) : ℂ) * I) = exp (φ * I) := by
  rw [ofReal_add, add_mul, exp_add]
  have : exp (((2 * π : ℝ) : ℂ) * I) = 1 := by
    rw [show ((2 * π : ℝ) : ℂ) * I = 2 * π * I by push_cast; ring]
    exact exp_two_pi_mul_I
  rw [this, mul_one]

theorem periodic_apply_arg {r : ℝ → ℝ} (hper : Function.Periodic r (2 * π)) {t : ℝ} (ht : 0 < t)
    (φ : ℝ) : r (arg ((t : ℂ) * exp (φ * I))) = r φ := by
  rw [arg_real_mul _ ht, arg_exp_mul_I, toIocMod]
  exact hper.sub_zsmul_eq _

section Loop

variable {c : ℂ} {r : ℝ → ℝ}
  (hcont : Continuous r) (hper : Function.Periodic r (2 * π)) (hpos : ∀ φ, 0 < r φ)

theorem γ_sub_c (φ : ℝ) : γ c r φ - c = (r φ : ℂ) * exp (φ * I) := by
  simp [γ]

include hpos in
theorem norm_γ_sub_c (φ : ℝ) : ‖γ c r φ - c‖ = r φ := by
  rw [γ_sub_c, norm_mul, norm_exp_mul_I, mul_one, Complex.norm_of_nonneg (hpos φ).le]

include hper hpos in
theorem r_arg_γ (φ : ℝ) : r (arg (γ c r φ - c)) = r φ := by
  rw [γ_sub_c]; exact periodic_apply_arg hper (hpos φ) φ

include hper hpos in

theorem γ_mem_K (φ : ℝ) : ‖γ c r φ - c‖ ≤ r (arg (γ c r φ - c)) := by
  rw [norm_γ_sub_c hpos, r_arg_γ hper hpos]

include hper in
theorem γ_add_two_pi (φ : ℝ) : γ c r (φ + 2 * π) = γ c r φ := by
  simp only [γ, hper φ, exp_mul_I_add_two_pi]

end Loop

section Analysis

end Analysis

section Weight

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

end Weight

section CellIdentity

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

variable
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))

theorem Kint_subset_K (R : AlgebraicCurve.RadialRegion) : R.Kint ⊆ R.K := fun z hz =>
  show ‖z - R.q‖ ≤ R.r (arg (z - R.q)) from le_of_lt hz

end CellIdentity

end CellPeriods

end Part_book_cell

section Part_book

namespace CellPeriods

p2m_open "Complex MeasureTheory Set Filter intervalIntegral AlgebraicCurve P2MW.S_AlgebraicCurve_exists_loops_pathIntegral_reciprocity_raw.AlgebraicCurve"
open scoped Real Topology Interval Manifold ContDiff

section Arc

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

theorem loop_mem_K (R : AlgebraicCurve.RadialRegion) (s : ℝ) : R.loop s ∈ R.K :=
  γ_mem_K R.hper R.hpos s

theorem arc_lt (R : AlgebraicCurve.RadialRegion) (k : Fin R.N) : R.φs k.castSucc < R.φs k.succ :=
  R.hmono Fin.castSucc_lt_succ

noncomputable abbrev gθ (C : AlgebraicCurve.Cell F) (θ : Ω[F⁄ℂ]) (s : ℝ) : ℂ := C.bdryIntegrand θ s

theorem bdry_mem (C : AlgebraicCurve.Cell F) (s : ℝ) :
    C.bdry s ∈ C.ζ.source ∧ C.ζ (C.bdry s) = C.R.loop s := by
  have ht : C.R.loop s ∈ C.ζ.target := C.hUt (C.hKU (loop_mem_K C.R s))
  exact ⟨C.ζ.map_target ht, C.ζ.right_inv ht⟩

end Arc

section Edge

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

variable
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))

end Edge

section Global

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

private noncomputable abbrev _root_.CellPeriods.arcOf (𝒟 : AlgebraicCurve.CellDissection F) (q : 𝒟.ιE × Bool) :
    Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N :=
  𝒟.arcOf q

p2m_export "CellPeriods" "arcOf"
omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem side_arcOf (𝒟 : AlgebraicCurve.CellDissection F) (q : 𝒟.ιE × Bool) :
    𝒟.side (arcOf 𝒟 q).1 (arcOf 𝒟 q).2 = q :=
  Function.surjInv_eq (f := fun p : (Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N) => 𝒟.side p.1 p.2)
    𝒟.side_bij.surjective q

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem arcOf_side (𝒟 : AlgebraicCurve.CellDissection F) (p : Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N) :
    arcOf 𝒟 (𝒟.side p.1 p.2) = p :=
  Function.leftInverse_surjInv 𝒟.side_bij p

private noncomputable abbrev _root_.CellPeriods.edgeInt (𝒟 : AlgebraicCurve.CellDissection F) (θ : Ω[F⁄ℂ]) (e : 𝒟.ιE) : ℂ :=
  𝒟.edgeInt θ e

p2m_export "CellPeriods" "edgeInt"
variable
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem bdry_not_mem_interior (C : AlgebraicCurve.Cell F) (s : ℝ) : C.bdry s ∉ C.interior' := by
  rintro ⟨w, hw, hw'⟩
  have hwt : w ∈ C.ζ.target := C.hUt (C.hKU (Kint_subset_K _ hw))
  have hlt : C.R.loop s ∈ C.ζ.target := C.hUt (C.hKU (loop_mem_K C.R s))
  have : w = C.R.loop s := C.ζ.symm.injOn hwt hlt hw'
  rw [this] at hw
  have h1 : ‖C.R.loop s - C.R.q‖ = C.R.r s := norm_γ_sub_c C.R.hpos s
  have h2 : C.R.r (arg (C.R.loop s - C.R.q)) = C.R.r s := r_arg_γ C.R.hper C.R.hpos s
  have h3 : ‖C.R.loop s - C.R.q‖ < C.R.r (arg (C.R.loop s - C.R.q)) := hw
  rw [h1, h2] at h3
  exact lt_irrefl _ h3

end Global

end CellPeriods

end Part_book

section Part_skel

namespace CellPeriods

p2m_open "Complex MeasureTheory Set Filter intervalIntegral AlgebraicCurve P2MW.S_AlgebraicCurve_exists_loops_pathIntegral_reciprocity_raw.AlgebraicCurve"
open scoped Real Topology Interval Manifold ContDiff

section Region

variable (R : AlgebraicCurve.RadialRegion)

theorem loop_add_two_pi (φ : ℝ) : R.loop (φ + 2 * π) = R.loop φ :=
  γ_add_two_pi R.hper φ

end Region

section CellTop

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

theorem exists_mem_arc_of_ne (𝒟 : AlgebraicCurve.CellDissection F) {x : Place ℂ F} {C C' : 𝒟.ιC}
    (hC : x ∈ (𝒟.cell C).carrier) (hC' : x ∈ (𝒟.cell C').carrier) (h : C ≠ C') :
    ∃ k : Fin (𝒟.cell C).R.N, x ∈ (𝒟.cell C).arc k := by
  obtain h0 | ⟨B, ⟨k, _, _, hk⟩, -⟩ := (𝒟.inter C C' x hC hC').cases_head
  · exact absurd h0 h
  · exact ⟨k, hk⟩

theorem arc_subset_carrier (C : AlgebraicCurve.Cell F) (k : Fin C.R.N) : C.arc k ⊆ C.carrier := by
  rintro x ⟨z, ⟨s, hs, rfl⟩, rfl⟩
  exact ⟨_, loop_mem_K _ s, rfl⟩

theorem bdry_add_two_pi (C : AlgebraicCurve.Cell F) (φ : ℝ) : C.bdry (φ + 2 * π) = C.bdry φ := by
  show C.ζ.symm (C.R.loop (φ + 2 * π)) = C.ζ.symm (C.R.loop φ)
  rw [loop_add_two_pi]

end CellTop

section Flows

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

variable
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
open scoped Classical in

theorem jump_kirchhoff (𝒟 : AlgebraicCurve.CellDissection F) (hvert : Function.Injective 𝒟.vert)
    (Ψ : 𝒟.ιC → ℂ → ℂ) (J : 𝒟.ιE → ℂ)
    (hJ : ∀ e : 𝒟.ιE, ∀ s ∈ Icc ((𝒟.cell (arcOf 𝒟 (e, true)).1).R.φs (arcOf 𝒟 (e, true)).2.castSucc)
        ((𝒟.cell (arcOf 𝒟 (e, true)).1).R.φs (arcOf 𝒟 (e, true)).2.succ),
      Ψ (arcOf 𝒟 (e, true)).1 ((𝒟.cell (arcOf 𝒟 (e, true)).1).R.loop s) -
        Ψ (arcOf 𝒟 (e, false)).1
          ((𝒟.cell (arcOf 𝒟 (e, false)).1).ζ ((𝒟.cell (arcOf 𝒟 (e, true)).1).bdry s)) = J e)
    (v : 𝒟.ιV) :
    (∑ e with (𝒟.ends e).2 = v, J e) = ∑ e with (𝒟.ends e).1 = v, J e := by

  set Vs : (Σ D : 𝒟.ιC, Fin (𝒟.cell D).R.N) → ℂ :=
    fun p => Ψ p.1 ((𝒟.cell p.1).R.loop ((𝒟.cell p.1).R.φs p.2.castSucc)) with hVs
  set Ve : (Σ D : 𝒟.ιC, Fin (𝒟.cell D).R.N) → ℂ :=
    fun p => Ψ p.1 ((𝒟.cell p.1).R.loop ((𝒟.cell p.1).R.φs p.2.succ)) with hVe
  set startV : 𝒟.ιE × Bool → 𝒟.ιV :=
    fun q => if q.2 then (𝒟.ends q.1).1 else (𝒟.ends q.1).2 with hstartV
  set endV : 𝒟.ιE × Bool → 𝒟.ιV :=
    fun q => if q.2 then (𝒟.ends q.1).2 else (𝒟.ends q.1).1 with hendV

  have hends : ∀ p : (Σ D : 𝒟.ιC, Fin (𝒟.cell D).R.N),
      (𝒟.cell p.1).bdry ((𝒟.cell p.1).R.φs p.2.castSucc) = 𝒟.vert (startV (𝒟.side p.1 p.2)) ∧
      (𝒟.cell p.1).bdry ((𝒟.cell p.1).R.φs p.2.succ) = 𝒟.vert (endV (𝒟.side p.1 p.2)) := by
    rintro ⟨D, k⟩
    exact 𝒟.arc_ends D k

  have hJe : ∀ e, J e = Ve (arcOf 𝒟 (e, true)) - Vs (arcOf 𝒟 (e, false)) := by
    intro e
    set p := arcOf 𝒟 (e, true) with hp
    set p' := arcOf 𝒟 (e, false) with hp'
    have h := hJ e _ (right_mem_Icc.2 (arc_lt _ p.2).le)
    rw [← h]
    congr 1
    simp only [hVs]
    congr 1

    have h1 := (hends p).2
    have h2 := (hends p').1
    rw [hp, side_arcOf] at h1
    rw [hp', side_arcOf] at h2
    simp only [hendV, hstartV, if_true, if_false, Bool.false_eq_true] at h1 h2
    rw [← hp] at h1
    rw [← hp'] at h2
    rw [h1, ← h2]
    exact (bdry_mem _ _).2
  have hJs : ∀ e, J e = Vs (arcOf 𝒟 (e, true)) - Ve (arcOf 𝒟 (e, false)) := by
    intro e
    set p := arcOf 𝒟 (e, true) with hp
    set p' := arcOf 𝒟 (e, false) with hp'
    have h := hJ e _ (left_mem_Icc.2 (arc_lt _ p.2).le)
    rw [← h]
    congr 1
    simp only [hVe]
    congr 1
    have h1 := (hends p).1
    have h2 := (hends p').2
    rw [hp, side_arcOf] at h1
    rw [hp', side_arcOf] at h2
    simp only [hendV, hstartV, if_true, if_false, Bool.false_eq_true] at h1 h2
    rw [← hp] at h1
    rw [← hp'] at h2
    rw [h1, ← h2]
    exact (bdry_mem _ _).2

  have hbij : Function.Bijective (arcOf 𝒟) :=
    Function.bijective_iff_has_inverse.2
      ⟨fun p => 𝒟.side p.1 p.2, fun q => side_arcOf 𝒟 q, fun p => arcOf_side 𝒟 p⟩
  set T : (Σ D : 𝒟.ιC, Fin (𝒟.cell D).R.N) → ℂ := fun p =>
    (if endV (𝒟.side p.1 p.2) = v then Ve p else 0) -
      (if startV (𝒟.side p.1 p.2) = v then Vs p else 0) with hT
  have hsumT : ∑ p : (Σ D : 𝒟.ιC, Fin (𝒟.cell D).R.N), T p = 0 := by
    rw [Fintype.sum_sigma]
    refine Finset.sum_eq_zero fun D _ => ?_

    set G : ℝ → ℂ := fun φ =>
      if (𝒟.cell D).bdry φ = 𝒟.vert v then Ψ D ((𝒟.cell D).R.loop φ) else 0 with hG
    have hTk : ∀ k : Fin (𝒟.cell D).R.N,
        T ⟨D, k⟩ = G ((𝒟.cell D).R.φs k.succ) - G ((𝒟.cell D).R.φs k.castSucc) := by
      intro k
      obtain ⟨h1, h2⟩ := hends ⟨D, k⟩
      dsimp only at h1 h2
      simp only [hT, hG, hVe, hVs]
      rw [h1, h2, hvert.eq_iff, hvert.eq_iff]
      split_ifs <;> rfl
    simp_rw [hTk]
    rw [Finset.sum_sub_distrib]
    have h2 := Fin.sum_univ_castSucc (fun i : Fin ((𝒟.cell D).R.N + 1) => G ((𝒟.cell D).R.φs i))
    have h3 := Fin.sum_univ_succ (fun i : Fin ((𝒟.cell D).R.N + 1) => G ((𝒟.cell D).R.φs i))
    try simp only at h2 h3
    have hlast : G ((𝒟.cell D).R.φs (Fin.last _)) = G ((𝒟.cell D).R.φs 0) := by
      rw [(𝒟.cell D).R.hφN, (𝒟.cell D).R.hφ0, show (2 * π : ℝ) = 0 + 2 * π by ring]
      simp only [hG, bdry_add_two_pi, loop_add_two_pi]
    linear_combination h2 - h3 + hlast
  have hsumT' : ∑ q : 𝒟.ιE × Bool, T (arcOf 𝒟 q) = 0 := by
    rw [hbij.sum_comp T]; exact hsumT
  rw [Fintype.sum_prod_type] at hsumT'
  simp only [Fintype.sum_bool, hT, side_arcOf, hendV, hstartV, if_true, if_false,
    Bool.false_eq_true] at hsumT'

  rw [Finset.sum_filter, Finset.sum_filter]
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
  refine Eq.trans ?_ hsumT'
  refine Finset.sum_congr rfl fun e _ => ?_
  have hE : Ve (arcOf 𝒟 (e, true)) - Vs (arcOf 𝒟 (e, false)) =
      Vs (arcOf 𝒟 (e, true)) - Ve (arcOf 𝒟 (e, false)) := by rw [← hJe, ← hJs]
  rw [hJe e]
  split_ifs <;> first | (linear_combination (-1 : ℂ) * hE) | ring1

end Flows

end CellPeriods

end Part_skel

section Part_g1

namespace CellPeriods

p2m_open "Complex Set Filter AlgebraicCurve P2MW.S_AlgebraicCurve_exists_loops_pathIntegral_reciprocity_raw.AlgebraicCurve"
open scoped Real Topology Manifold ContDiff

section Atlas

end Atlas

section G1

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

variable
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))

variable {κ : Type*} [Finite κ] (𝒟 : AlgebraicCurve.CellDissection F) (η : κ → Ω[F⁄ℂ])
    (V : 𝒟.ιC → Set ℂ) (Ψ : κ → 𝒟.ιC → ℂ → ℂ)

noncomputable def gvec (y : Place ℂ F) (C : 𝒟.ιC) : κ → ℂ := fun i => Ψ i C ((𝒟.cell C).ζ y)

structure PrimData : Prop where
  hVo : ∀ C, IsOpen (V C)
  hKV : ∀ C, (𝒟.cell C).R.K ⊆ V C
  hVt : ∀ C, V C ⊆ (𝒟.cell C).ζ.target
  hΨ : ∀ i C, ∀ w ∈ V C, HasDerivAt (Ψ i C) (coeffIn (𝒟.cell C).ζ (η i) w) w
  hη : ∀ i (Q : Place ℂ F), 0 ≤ Q.ordDifferential (η i)

variable {𝒟 η V Ψ}

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem exists_mem_carrier (𝒟 : AlgebraicCurve.CellDissection F) (y : Place ℂ F) :
    ∃ D : 𝒟.ιC, y ∈ (𝒟.cell D).carrier := by
  have : y ∈ ⋃ D, (𝒟.cell D).carrier := by rw [𝒟.cover]; exact mem_univ y
  exact mem_iUnion.1 this

noncomputable def cellOf (𝒟 : AlgebraicCurve.CellDissection F) (y : Place ℂ F) : 𝒟.ιC :=
  (exists_mem_carrier 𝒟 y).choose

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem mem_cellOf (𝒟 : AlgebraicCurve.CellDissection F) (y : Place ℂ F) :
    y ∈ (𝒟.cell (cellOf 𝒟 y)).carrier :=
  (exists_mem_carrier 𝒟 y).choose_spec

variable (J : 𝒟.ιE → κ → ℂ)

variable (𝒟 Ψ) in

def IsJump : Prop :=
  ∀ i (e : 𝒟.ιE), ∀ s ∈ Icc ((𝒟.cell (arcOf 𝒟 (e, true)).1).R.φs (arcOf 𝒟 (e, true)).2.castSucc)
      ((𝒟.cell (arcOf 𝒟 (e, true)).1).R.φs (arcOf 𝒟 (e, true)).2.succ),
    Ψ i (arcOf 𝒟 (e, true)).1 ((𝒟.cell (arcOf 𝒟 (e, true)).1).R.loop s) -
      Ψ i (arcOf 𝒟 (e, false)).1
        ((𝒟.cell (arcOf 𝒟 (e, false)).1).ζ ((𝒟.cell (arcOf 𝒟 (e, true)).1).bdry s)) = J e i

variable {J}

include hfg hF in

theorem path_sub_mem_closure_jumps (hP : PrimData 𝒟 η V Ψ) {J : 𝒟.ιE → κ → ℂ} (hJ : IsJump 𝒟 Ψ J)
    {P P' : Place ℂ F} (δ : Path P P') (g : κ → unitInterval → ℂ)
    (hg : ∀ i, IsPrimitiveAlong (η i) δ (g i)) :
    (fun i => g i 1 - g i 0) - (gvec 𝒟 Ψ P' (cellOf 𝒟 P') - gvec 𝒟 Ψ P (cellOf 𝒟 P)) ∈
      AddSubgroup.closure (Set.range J) := by
  obtain ⟨n, hn⟩ :=
    AlgebraicCurve.CellDissection.exists_int_pathIntegral_sub_primitive_eq_sum_jump F hfg hF 𝒟 κ η hP.hη V hP.hVo
      hP.hKV hP.hVt Ψ hP.hΨ J hJ δ g hg (cellOf 𝒟 P) (cellOf 𝒟 P') (mem_cellOf 𝒟 P)
      (mem_cellOf 𝒟 P')
  have : (fun i => g i 1 - g i 0) - (gvec 𝒟 Ψ P' (cellOf 𝒟 P') - gvec 𝒟 Ψ P (cellOf 𝒟 P)) =
      ∑ e, (n e : ℤ) • J e := by
    funext i
    simp only [Pi.sub_apply, Finset.sum_apply, zsmul_eq_mul, gvec]
    exact hn i
  rw [this]
  exact AddSubgroup.sum_mem _ fun e _ =>
    AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self e)) _

include hfg hF in

theorem period_mem_closure_jumps (hP : PrimData 𝒟 η V Ψ) (hJ : IsJump 𝒟 Ψ J)
    {P : Place ℂ F} (δ : Path P P) (g : κ → unitInterval → ℂ)
    (hg : ∀ i, IsPrimitiveAlong (η i) δ (g i)) :
    (fun i => g i 1 - g i 0) ∈ AddSubgroup.closure (Set.range J) := by
  have := path_sub_mem_closure_jumps hfg hF hP hJ δ g hg
  rwa [sub_self, sub_zero] at this

end G1

end CellPeriods

end Part_g1

section Part_loops

open scoped Manifold ContDiff Topology Real Interval
p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_exists_loops_pathIntegral_reciprocity_raw.AlgebraicCurve Filter Set Complex MeasureTheory intervalIntegral"

namespace CellPeriods

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
        simpa using (hball w hw).1.fun_sub (hball w hw).2
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
  exact hloc.apply_eq_of_preconnectedSpace (x := t) (y := 0)

theorem pathIntegral_eq_of_isPrimitiveAlong {θ : Ω[F⁄ℂ]} {P Q : Place ℂ F} {γ : Path P Q}
    {g : unitInterval → ℂ} (hg : IsPrimitiveAlong θ γ g) : pathIntegral θ γ = g 1 - g 0 := by
  classical
  have h : ∃ g, IsPrimitiveAlong θ γ g := ⟨g, hg⟩
  rw [pathIntegral_def, dif_pos h]
  have := sub_eq_sub_of_isPrimitiveAlong h.choose_spec hg 1
  linear_combination this

end Prim

section EdgePath

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

theorem not_mem_interior_of_mem_arc (𝒟 : AlgebraicCurve.CellDissection F) {C : 𝒟.ιC}
    {k : Fin (𝒟.cell C).R.N} {x : Place ℂ F} (hx : x ∈ (𝒟.cell C).arc k) (D : 𝒟.ιC) :
    x ∉ (𝒟.cell D).interior' := by
  intro hxD
  by_cases hDC : D = C
  · subst hDC
    obtain ⟨z, ⟨s, hs, rfl⟩, rfl⟩ := hx
    exact bdry_not_mem_interior _ s hxD
  · have hsub : (𝒟.cell D).interior' ⊆ (𝒟.cell D).carrier := by
      rintro y ⟨z, hz, rfl⟩; exact ⟨z, Kint_subset_K _ hz, rfl⟩
    obtain ⟨k', ⟨z, ⟨s, hs, rfl⟩, rfl⟩⟩ :=
      exists_mem_arc_of_ne 𝒟 (hsub hxD) (arc_subset_carrier _ k hx) hDC
    exact bdry_not_mem_interior _ s hxD

end EdgePath

section EdgeIntegral

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

variable
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))

end EdgeIntegral

section Walks

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

variable
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))

private abbrev _root_.CellPeriods.skeleton (𝒟 : AlgebraicCurve.CellDissection F) : Set (Place ℂ F) := 𝒟.skeleton

p2m_export "CellPeriods" "skeleton"

def RegOnSkeleton (𝒟 : AlgebraicCurve.CellDissection F) (θ : Ω[F⁄ℂ]) : Prop :=
  ∀ x ∈ skeleton 𝒟, 0 ≤ x.ordDifferential θ

end Walks

end CellPeriods

end Part_loops

section Part_norm

namespace CellPeriods

p2m_open "Complex Set Filter AlgebraicCurve P2MW.S_AlgebraicCurve_exists_loops_pathIntegral_reciprocity_raw.AlgebraicCurve"
open scoped Real Topology Manifold ContDiff

section Norm

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

variable
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))

variable {κ : Type*}

include hfg hF in

theorem exists_normalised (𝒟 : AlgebraicCurve.CellDissection F) (η : κ → Ω[F⁄ℂ])
    (hη : ∀ i (Q : Place ℂ F), 0 ≤ Q.ordDifferential (η i)) (𝒯s : Finset 𝒟.ιE)
    (h𝒯s : ∀ C C' : 𝒟.ιC, ∃! c : 𝒟.ιE → ℤ, (∀ e ∉ 𝒯s, c e = 0) ∧
      ∀ D, (∑ e with (arcOf 𝒟 (e, true)).1 = D, c e) - (∑ e with (arcOf 𝒟 (e, false)).1 = D, c e) =
        (if D = C' then (1 : ℤ) else 0) - (if D = C then 1 else 0))
    (C₀ : 𝒟.ιC) (w₀ : ℂ) :
    ∃ (V : 𝒟.ιC → Set ℂ) (Ψ : κ → 𝒟.ιC → ℂ → ℂ) (J : 𝒟.ιE → κ → ℂ),
      PrimData 𝒟 η V Ψ ∧ (∀ C, StarConvex ℝ (𝒟.cell C).R.q (V C)) ∧ IsJump 𝒟 Ψ J ∧
      (∀ e ∈ 𝒯s, J e = 0) ∧ ∀ i, Ψ i C₀ w₀ = 0 := by
  obtain ⟨V, Ψ, J, hVo, hKV, hVt, hstar, hΨ, hJ, hJ0, hΨ0⟩ :=
    AlgebraicCurve.CellDissection.exists_primitives_jump_eq_zero_of_dualTree F hfg hF 𝒟 κ η hη 𝒯s
      h𝒯s C₀ w₀
  exact ⟨V, Ψ, J, ⟨hVo, hKV, hVt, hΨ, hη⟩, hstar, hJ, hJ0, hΨ0⟩

end Norm

end CellPeriods

end Part_norm

section Part_theta

namespace CellPeriods

p2m_open "Complex Set Filter AlgebraicCurve P2MW.S_AlgebraicCurve_exists_loops_pathIntegral_reciprocity_raw.AlgebraicCurve"
open scoped Real Topology Manifold ContDiff

section PlaceAlg

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ordDifferential_nonneg_iff (v : Place K F) [v.DCoordGenerates] (θ : Ω[F⁄K]) :
    0 ≤ v.ordDifferential θ ↔ v.differentialCoeff θ ∈ v.toValuationSubring :=
  ⟨fun h => CellCoeff.Place.differentialCoeff_mem v h,
    fun h => CellCoeff.Place.ord_nonneg_of_mem v h⟩

theorem dCoordFn_ne_zero (v : Place K F) : v.dCoordFn ≠ 0 := by
  intro h0
  have h1 := v.ord_dCoordFn
  rw [h0, v.ord_zero] at h1
  exact zero_ne_one h1

theorem neg_one_le_ordDifferential_iff (v : Place K F) [v.DCoordGenerates] (θ : Ω[F⁄K]) :
    -1 ≤ v.ordDifferential θ ↔ v.dCoordFn * v.differentialCoeff θ ∈ v.toValuationSubring := by
  refine ⟨fun h => CellCoeff.Place.dCoordFn_mul_differentialCoeff_mem v h, fun h => ?_⟩
  by_cases h0 : v.differentialCoeff θ = 0
  · show -1 ≤ v.ord (v.differentialCoeff θ)
    rw [h0, v.ord_zero]; norm_num
  have := CellCoeff.Place.ord_nonneg_of_mem v h
  rw [v.ord_mul (dCoordFn_ne_zero v) h0, v.ord_dCoordFn] at this
  show -1 ≤ v.ord (v.differentialCoeff θ)
  omega

end PlaceAlg

section Read

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

variable
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))

end Read

section LinearPath

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

variable
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))

include hF in
theorem pathIntegral_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (θ : ι → Ω[F⁄ℂ])
    {P P' : Place ℂ F} (γ : Path P P')
    (hreg : ∀ i ∈ s, ∀ t, 0 ≤ (γ t).ordDifferential (θ i))
    (hprim : ∀ i ∈ s, ∃ g, IsPrimitiveAlong (θ i) γ g)
    (_hregsum : ∀ s' ⊆ s, ∀ t, 0 ≤ (γ t).ordDifferential (∑ i ∈ s', c i • θ i)) :
    (∃ g, IsPrimitiveAlong (∑ i ∈ s, c i • θ i) γ g) ∧
      pathIntegral (∑ i ∈ s, c i • θ i) γ = ∑ i ∈ s, c i * pathIntegral (θ i) γ :=
  AlgebraicCurve.pathIntegral_finset_sum_smul F hF ι s c θ γ hreg hprim

end LinearPath

section ThetaSpace

variable {F : Type*} [Field F] [Algebra ℂ F] [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]

theorem ordDifferential_nonneg_of_mem_regularDifferentials {θ : Ω[F⁄ℂ]}
    (h : θ ∈ regularDifferentials ℂ F) (v : Place ℂ F) : 0 ≤ v.ordDifferential θ := by
  haveI : v.DCoordGenerates := dCoordGenerates_of_isCurveOver (K := ℂ) (F := F) v
  haveI : Nontrivial Ω[F⁄ℂ] := IsCurveOver.instNontrivialKaehler
  obtain ⟨f, hf, hθ⟩ := h v
  rw [ordDifferential_nonneg_iff]
  have : v.differentialCoeff θ = f := v.differentialCoeff_unique hθ
  rw [this]; exact hf

theorem ordDifferential_nonneg_of_res_eq_zero (v : Place ℂ F) {θ : Ω[F⁄ℂ]}
    (h1 : -1 ≤ v.ordDifferential θ)
    (h0 : Place.evalAt v (v.dCoordFn * v.differentialCoeff θ) = 0) : 0 ≤ v.ordDifferential θ := by
  haveI : v.DCoordGenerates := dCoordGenerates_of_isCurveOver (K := ℂ) (F := F) v
  haveI : Nontrivial Ω[F⁄ℂ] := IsCurveOver.instNontrivialKaehler
  by_cases hh : v.differentialCoeff θ = 0
  · show 0 ≤ v.ord (v.differentialCoeff θ)
    rw [hh, v.ord_zero]
  have hu : v.dCoordFn * v.differentialCoeff θ ∈ v.toValuationSubring :=
    (neg_one_le_ordDifferential_iff v θ).1 h1
  have hu0 : v.dCoordFn * v.differentialCoeff θ ≠ 0 := mul_ne_zero (dCoordFn_ne_zero v) hh
  have hord := CellCoeff.Place.ord_nonneg_of_mem v hu
  have hne : v.ord (v.dCoordFn * v.differentialCoeff θ) ≠ 0 := by
    intro h
    exact v.evalAt_ne_zero_of_ord_eq_zero (CellCoeff.Place.isRational_of_isAlgClosed v) hu0 h h0
  rw [v.ord_mul (dCoordFn_ne_zero v) hh, v.ord_dCoordFn] at hord hne
  show 0 ≤ v.ord (v.differentialCoeff θ)
  omega

end ThetaSpace

end CellPeriods

end Part_theta

section Part_cycles

namespace CellPeriods

p2m_open "Complex Set Filter AlgebraicCurve P2MW.S_AlgebraicCurve_exists_loops_pathIntegral_reciprocity_raw.AlgebraicCurve"
open scoped Real Topology Manifold ContDiff

section Cycles

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

variable
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))

structure Flow (𝒟 : AlgebraicCurve.CellDissection F) (𝒯 : Finset 𝒟.ιE) (Z : 𝒟.ιE → 𝒟.ιE → ℤ) : Prop where
  kirchhoff : ∀ j w, (∑ e with (𝒟.ends e).2 = w, Z j e) = ∑ e with (𝒟.ends e).1 = w, Z j e
  delta : ∀ j ∈ 𝒯ᶜ, ∀ j' ∈ 𝒯ᶜ, Z j j' = if j = j' then 1 else 0
  zero : ∀ j ∈ 𝒯, Z j = 0

def FlowDecomp (A : Type*) [AddCommGroup A] (𝒟 : AlgebraicCurve.CellDissection F) (𝒯 : Finset 𝒟.ιE)
    (Z : 𝒟.ιE → 𝒟.ιE → ℤ) : Prop :=
  ∀ f : 𝒟.ιE → A,
    (∀ w, (∑ e with (𝒟.ends e).2 = w, f e) = ∑ e with (𝒟.ends e).1 = w, f e) →
    ∀ e, f e = ∑ j ∈ 𝒯ᶜ, Z j e • f j

include hfg hF in

theorem exists_loop (𝒟 : AlgebraicCurve.CellDissection F) {𝒯 : Finset 𝒟.ιE} {Z : 𝒟.ιE → 𝒟.ιE → ℤ}
    (hZ : Flow 𝒟 𝒯 Z)
    (h𝒯path : ∀ u v : 𝒟.ιV, ∃! c : 𝒟.ιE → ℤ, (∀ e ∉ 𝒯, c e = 0) ∧
      ∀ w, (∑ e with (𝒟.ends e).2 = w, c e) - (∑ e with (𝒟.ends e).1 = w, c e) =
        (if w = v then (1 : ℤ) else 0) - (if w = u then 1 else 0))
    (hwalk : ∀ u v : 𝒟.ιV, Relation.ReflTransGen
      (fun a b : 𝒟.ιV => ∃ e ∈ 𝒯, 𝒟.ends e = (a, b) ∨ 𝒟.ends e = (b, a)) u v)
    {j : 𝒟.ιE} (_hj : j ∉ 𝒯) :
    ∃ γ : Path (𝒟.vert (𝒟.ends j).1) (𝒟.vert (𝒟.ends j).1),
      (∀ t, γ t ∈ skeleton 𝒟) ∧
      ∀ θ : Ω[F⁄ℂ], RegOnSkeleton 𝒟 θ →
        (∃ g, IsPrimitiveAlong θ γ g) ∧
          pathIntegral θ γ = ∑ e, (Z j e : ℂ) * edgeInt 𝒟 θ e :=
  AlgebraicCurve.CellDissection.exists_loop_pathIntegral_eq_sum_cycle_mul_edgeInt F hfg hF 𝒟 𝒯 Z hZ.kirchhoff
    hZ.delta hZ.zero h𝒯path hwalk j

variable {κ : Type*}

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem jumps_kirchhoff (𝒟 : AlgebraicCurve.CellDissection F) (hvert : Function.Injective 𝒟.vert)
    {Ψ : κ → 𝒟.ιC → ℂ → ℂ} {J : 𝒟.ιE → κ → ℂ} (hJ : IsJump 𝒟 Ψ J) (w : 𝒟.ιV) :
    (∑ e with (𝒟.ends e).2 = w, J e) = ∑ e with (𝒟.ends e).1 = w, J e := by
  funext i
  simp only [Finset.sum_apply]
  exact jump_kirchhoff 𝒟 hvert (Ψ i) (fun e => J e i) (hJ i) w

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem closure_jumps_le (𝒟 : AlgebraicCurve.CellDissection F) (hvert : Function.Injective 𝒟.vert)
    {𝒯 𝒯s : Finset 𝒟.ιE} {Z : 𝒟.ιE → 𝒟.ιE → ℤ} (hZ : FlowDecomp (κ → ℂ) 𝒟 𝒯 Z)
    {Ψ : κ → 𝒟.ιC → ℂ → ℂ} {J : 𝒟.ιE → κ → ℂ} (hJ : IsJump 𝒟 Ψ J)
    (hJ0 : ∀ e ∈ 𝒯s, J e = 0) :
    AddSubgroup.closure (Set.range J) ≤
      AddSubgroup.closure ((fun j => J j) '' ((𝒯 ∪ 𝒯s)ᶜ : Finset 𝒟.ιE)) := by
  classical
  rw [AddSubgroup.closure_le]
  rintro _ ⟨f, rfl⟩
  have hdec : J f = ∑ j ∈ 𝒯ᶜ, Z j f • J j := hZ J (jumps_kirchhoff 𝒟 hvert hJ) f
  rw [hdec]
  refine AddSubgroup.sum_mem _ fun j hj => ?_
  by_cases hjs : j ∈ 𝒯s
  · rw [hJ0 j hjs, smul_zero]; exact zero_mem _
  · have hmem : J j ∈ (fun j => J j) '' ((𝒯 ∪ 𝒯s)ᶜ : Finset 𝒟.ιE) := by
      refine ⟨j, ?_, rfl⟩
      simp only [Finset.coe_compl, Finset.coe_union, Set.mem_compl_iff, Set.mem_union,
        Finset.mem_coe, not_or]
      exact ⟨Finset.mem_compl.1 hj, hjs⟩
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure hmem) _

end Cycles

end CellPeriods

end Part_cycles

section Part_wordid

namespace CellPeriods

p2m_open "Complex Set Filter AlgebraicCurve P2MW.S_AlgebraicCurve_exists_loops_pathIntegral_reciprocity_raw.AlgebraicCurve"
open scoped Real Topology Manifold ContDiff

section WordId

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

variable
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))

variable {κ : Type*} {𝒟 : AlgebraicCurve.CellDissection F} {η : κ → Ω[F⁄ℂ]} {V : 𝒟.ιC → Set ℂ}
  {Ψ : κ → 𝒟.ιC → ℂ → ℂ}

variable (𝒟 η) in

noncomputable def Ivec (e : 𝒟.ιE) : κ → ℂ := fun i => edgeInt 𝒟 (η i) e

def endV (𝒟 : AlgebraicCurve.CellDissection F) (q : 𝒟.ιE × Bool) : 𝒟.ιV :=
  if q.2 then (𝒟.ends q.1).2 else (𝒟.ends q.1).1

def startV (𝒟 : AlgebraicCurve.CellDissection F) (q : 𝒟.ιE × Bool) : 𝒟.ιV :=
  if q.2 then (𝒟.ends q.1).1 else (𝒟.ends q.1).2

end WordId

end CellPeriods

end Part_wordid

section Part_chords

namespace CellPeriods

section Chords

variable {E : Type*} [Fintype E] [DecidableEq E] {𝒯s : Finset E} {m : ℕ} [NeZero m]

def wordChain (wd : ZMod m ≃ {q : E × Bool // q.1 ∉ 𝒯s}) (e : E) (he : e ∉ 𝒯s) (f : E) : ℤ :=
  ∑ i ∈ Finset.univ.filter (fun i : ZMod m => i ≠ wd.symm ⟨(e, true), he⟩ ∧
      (i - wd.symm ⟨(e, true), he⟩).val <
        (wd.symm ⟨(e, false), he⟩ - wd.symm ⟨(e, true), he⟩).val),
    (if (wd i).1.2 then (1 : ℤ) else -1) * (if (wd i).1.1 = f then 1 else 0)

omit [Fintype E] in

theorem wordChain_eq (wd : ZMod m ≃ {q : E × Bool // q.1 ∉ 𝒯s}) (e : E) (he : e ∉ 𝒯s)
    (f : E) (hf : f ∉ 𝒯s) :
    wordChain wd e he f =
      (if wd.symm ⟨(f, true), hf⟩ ≠ wd.symm ⟨(e, true), he⟩ ∧
          (wd.symm ⟨(f, true), hf⟩ - wd.symm ⟨(e, true), he⟩).val <
            (wd.symm ⟨(e, false), he⟩ - wd.symm ⟨(e, true), he⟩).val then (1 : ℤ) else 0) -
      (if wd.symm ⟨(f, false), hf⟩ ≠ wd.symm ⟨(e, true), he⟩ ∧
          (wd.symm ⟨(f, false), hf⟩ - wd.symm ⟨(e, true), he⟩).val <
            (wd.symm ⟨(e, false), he⟩ - wd.symm ⟨(e, true), he⟩).val then (1 : ℤ) else 0) := by
  classical
  unfold wordChain
  set α := wd.symm ⟨(e, true), he⟩
  set β := wd.symm ⟨(e, false), he⟩
  set af := wd.symm ⟨(f, true), hf⟩
  set bf := wd.symm ⟨(f, false), hf⟩

  have hsplit : ∀ i : ZMod m,
      (if (wd i).1.2 then (1 : ℤ) else -1) * (if (wd i).1.1 = f then 1 else 0) =
        (if i = af then 1 else 0) - (if i = bf then 1 else 0) := by
    intro i
    have haf : i = af ↔ (wd i).1 = (f, true) := by
      constructor
      · rintro rfl; simp [af]
      · intro h
        apply wd.injective
        rw [Equiv.apply_symm_apply]
        exact Subtype.ext h
    have hbf : i = bf ↔ (wd i).1 = (f, false) := by
      constructor
      · rintro rfl; simp [bf]
      · intro h
        apply wd.injective
        rw [Equiv.apply_symm_apply]
        exact Subtype.ext h
    by_cases h1 : (wd i).1.1 = f
    · cases h2 : (wd i).1.2
      · have : (wd i).1 = (f, false) := Prod.ext h1 h2
        have hia : ¬ i = af := fun h => by rw [haf.1 h] at this; simp at this
        have hib : i = bf := hbf.2 this
        rw [if_neg hia, if_pos hib, if_pos h1]
        simp
      · have : (wd i).1 = (f, true) := Prod.ext h1 h2
        have hia : i = af := haf.2 this
        have hib : ¬ i = bf := fun h => by rw [hbf.1 h] at this; simp at this
        rw [if_pos hia, if_neg hib, if_pos h1]
        simp
    · have hia : ¬ i = af := fun h => h1 (by rw [haf.1 h])
      have hib : ¬ i = bf := fun h => h1 (by rw [hbf.1 h])
      rw [if_neg h1, mul_zero, if_neg hia, if_neg hib]
      simp
  simp_rw [hsplit]
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

omit [Fintype E] in

theorem wordChain_antisymm {m' : ℕ} [NeZero m'] (hm : m = 2 * m')
    (ιx : Fin m' ≃ {e : E // e ∉ 𝒯s})
    (wd : ZMod m ≃ {q : E × Bool // q.1 ∉ 𝒯s}) (e f : E) (he : e ∉ 𝒯s) (hf : f ∉ 𝒯s) :
    wordChain wd f hf e = -wordChain wd e he f := by
  classical
  subst hm
  set a : Fin m' → ZMod (2 * m') := fun p => wd.symm ⟨((ιx p : E), true), (ιx p).2⟩ with ha
  set b : Fin m' → ZMod (2 * m') := fun p => wd.symm ⟨((ιx p : E), false), (ιx p).2⟩ with hb
  have hdist : Function.Injective (fun p : Fin m' × Bool => bif p.2 then a p.1 else b p.1) := by
    rintro ⟨p, s⟩ ⟨p', s'⟩ h
    cases s <;> cases s' <;>
      simp only [ha, hb, Bool.cond_true, Bool.cond_false] at h <;>
      have h' := Subtype.ext_iff.1 (wd.symm.injective h) <;>
      simp only [Prod.mk.injEq] at h'
    · exact Prod.ext (ιx.injective (Subtype.ext h'.1)) rfl
    · exact absurd h'.2 (by simp)
    · exact absurd h'.2 (by simp)
    · exact Prod.ext (ιx.injective (Subtype.ext h'.1)) rfl
  have hP := ZMod.chordMatrix_transpose_eq_neg a b hdist
  simp only at hP

  set pe := ιx.symm ⟨e, he⟩ with hpe
  set pf := ιx.symm ⟨f, hf⟩ with hpf
  have hentry := congrFun (congrFun hP pe) pf
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at hentry
  have hae : a pe = wd.symm ⟨(e, true), he⟩ := by simp [ha, hpe]
  have hbe : b pe = wd.symm ⟨(e, false), he⟩ := by simp [hb, hpe]
  have haf : a pf = wd.symm ⟨(f, true), hf⟩ := by simp [ha, hpf]
  have hbf : b pf = wd.symm ⟨(f, false), hf⟩ := by simp [hb, hpf]
  rw [wordChain_eq wd f hf e he, wordChain_eq wd e he f hf, ← hae, ← hbe, ← haf, ← hbf]
  exact hentry

end Chords

end CellPeriods

end Part_chords

section Part_unimod

namespace CellPeriods

open Module

theorem isUnit_det_of_lattice {ι V : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup V]
    [Module ℝ V] [FiniteDimensional ℝ V] (z J : ι → V) (P : Matrix ι ι ℤ)
    (hJ : ∀ j, J j = -∑ l, P j l • z l)
    (hz : ∀ l, z l ∈ AddSubgroup.closure (Set.range J))
    (hspan : ⊤ ≤ Submodule.span ℝ (Set.range z))
    (hcard : Fintype.card ι = finrank ℝ V) : IsUnit P.det := by
  classical

  have hM : ∀ l, ∃ m : ι → ℤ, z l = ∑ j, m j • J j := by
    intro l
    have h := hz l
    rw [← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup,
      Submodule.mem_span_range_iff_exists_fun] at h
    obtain ⟨m, hm⟩ := h
    exact ⟨m, hm.symm⟩
  choose M hM using hM

  have hind : LinearIndependent ℝ z := linearIndependent_of_top_le_span_of_card_eq_finrank hspan hcard

  have hrow : ∀ l, ∑ k, (((1 : Matrix ι ι ℤ) + (Matrix.of M) * P) l k : ℝ) • z k = 0 := by
    intro l
    have h1 : z l = -∑ k, ((Matrix.of M * P) l k) • z k := by
      calc z l = ∑ j, M l j • J j := hM l
        _ = ∑ j, M l j • (-∑ k, P j k • z k) := by simp_rw [← hJ]
        _ = -∑ k, (∑ j, M l j * P j k) • z k := by
          simp only [smul_neg, Finset.sum_neg_distrib, Finset.smul_sum, smul_smul, neg_inj]
          rw [Finset.sum_comm]
          simp only [Finset.sum_smul]
        _ = -∑ k, ((Matrix.of M * P) l k) • z k := by
          simp only [Matrix.mul_apply, Matrix.of_apply]
    have h2 : ∑ k, (((1 : Matrix ι ι ℤ) + Matrix.of M * P) l k) • z k = 0 := by
      simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib, Matrix.one_apply, ite_smul,
        one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [h1]; abel
    rw [← h2]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Int.cast_smul_eq_zsmul ℝ]

  have hMP : (1 : Matrix ι ι ℤ) + Matrix.of M * P = 0 := by
    ext l k
    have := (linearIndependent_iff'.1 hind) Finset.univ
      (fun k => (((1 : Matrix ι ι ℤ) + Matrix.of M * P) l k : ℝ)) (hrow l) k (Finset.mem_univ k)
    have h' : (((1 : Matrix ι ι ℤ) + Matrix.of M * P) l k : ℝ) = 0 := this
    rw [Matrix.zero_apply]
    exact_mod_cast h'
  have hprod : Matrix.of M * P = -1 := eq_neg_of_add_eq_zero_right hMP
  have hdet : (Matrix.of M).det * P.det = (-1 : Matrix ι ι ℤ).det := by
    rw [← Matrix.det_mul, hprod]
  rw [Matrix.det_neg, Matrix.det_one, mul_one] at hdet

  have hu : IsUnit ((Matrix.of M).det * P.det) := by
    rw [hdet]; exact (isUnit_neg_one.pow _)
  exact isUnit_of_mul_isUnit_right hu

end CellPeriods

end Part_unimod

section Part_identity

namespace CellPeriods

p2m_open "Complex Set Filter AlgebraicCurve P2MW.S_AlgebraicCurve_exists_loops_pathIntegral_reciprocity_raw.AlgebraicCurve"
open scoped Real Topology Manifold ContDiff

section Identity

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

variable
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))

variable {κ : Type*} [Fintype κ]
variable {𝒟 : AlgebraicCurve.CellDissection F}

noncomputable def zv (Z : 𝒟.ιE → 𝒟.ιE → ℤ) (I : 𝒟.ιE → κ → ℂ) (l : 𝒟.ιE) : κ → ℂ :=
  ∑ e, (Z l e : ℂ) • I e

variable {η : κ → Ω[F⁄ℂ]} {V : 𝒟.ιC → Set ℂ} {Ψ : κ → 𝒟.ιC → ℂ → ℂ}

def JumpFormula (𝒯 𝒯s : Finset 𝒟.ιE) (Z : 𝒟.ιE → 𝒟.ιE → ℤ) (I : 𝒟.ιE → κ → ℂ)
    (J : 𝒟.ιE → κ → ℂ) (P : 𝒟.ιE → 𝒟.ιE → ℤ) : Prop :=
  ∀ j ∉ 𝒯s, J j = -∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ, (P j l : ℂ) • zv Z I l

noncomputable def wordMatrix {𝒯s : Finset 𝒟.ιE} {m : ℕ} [NeZero m]
    (wd : ZMod m ≃ {q : 𝒟.ιE × Bool // q.1 ∉ 𝒯s}) (j l : 𝒟.ιE) : ℤ :=
  if hj : j ∉ 𝒯s then wordChain wd j hj l else 0

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem wordMatrix_of_not_mem {𝒯s : Finset 𝒟.ιE} {m : ℕ} [NeZero m]
    (wd : ZMod m ≃ {q : 𝒟.ιE × Bool // q.1 ∉ 𝒯s}) {j : 𝒟.ιE} (hj : j ∉ 𝒯s) (l : 𝒟.ιE) :
    wordMatrix wd j l = wordChain wd j hj l := by
  simp [wordMatrix, hj]

include hfg hF in

theorem jump_formula (hvert : Function.Injective 𝒟.vert) (hP : PrimData 𝒟 η V Ψ) {J : 𝒟.ιE → κ → ℂ}
    (hJ : IsJump 𝒟 Ψ J) {𝒯 𝒯s : Finset 𝒟.ιE} (hJ0 : ∀ e ∈ 𝒯s, J e = 0)
    {Z : 𝒟.ιE → 𝒟.ιE → ℤ} (hZ : FlowDecomp ℤ 𝒟 𝒯 Z) (hZ' : FlowDecomp (κ → ℂ) 𝒟 𝒯 Z)
    {m : ℕ} [NeZero m] (wd : ZMod m ≃ {q : 𝒟.ιE × Bool // q.1 ∉ 𝒯s})
    (hW1 : ∀ i : ZMod m, endV 𝒟 (wd i).1 = startV 𝒟 (wd (i + 1)).1 ∧
      ∃ cs : List 𝒟.ιC, cs.head? = some (arcOf 𝒟 (wd i).1).1 ∧
        cs.getLast? = some (arcOf 𝒟 (wd (i + 1)).1).1 ∧
        cs.IsChain (fun D D' => ∃ g ∈ 𝒯s,
          (((arcOf 𝒟 (g, true)).1 = D ∧ (arcOf 𝒟 (g, false)).1 = D') ∨
            ((arcOf 𝒟 (g, true)).1 = D' ∧ (arcOf 𝒟 (g, false)).1 = D)) ∧
          (endV 𝒟 (wd i).1 = (𝒟.ends g).1 ∨ endV 𝒟 (wd i).1 = (𝒟.ends g).2)))
    (hW3 : ∀ (e : 𝒟.ιE) (he : e ∉ 𝒯s) (w : 𝒟.ιV),
      (∑ f with (𝒟.ends f).2 = w, wordChain wd e he f) =
        ∑ f with (𝒟.ends f).1 = w, wordChain wd e he f) :
    JumpFormula 𝒯 𝒯s Z (Ivec 𝒟 η) J (wordMatrix wd) := by
  intro j hj
  have h := (AlgebraicCurve.CellDissection.jump_kirchhoff_and_wordFormula_of_primitives F hfg hF 𝒟
    hvert κ η hP.hη V hP.hVo hP.hKV hP.hVt Ψ hP.hΨ J hJ 𝒯 𝒯s hJ0 Z hZ hZ'
    (fun _ => ⟨m, inferInstance, wd, hW1, hW3⟩)).2.2 m inferInstance wd hW1 hW3 j hj
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [wordMatrix_of_not_mem wd hj]
  rfl

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [Fintype κ] in

theorem closure_jumps_le_zv (hvert : Function.Injective 𝒟.vert) {Ψ : κ → 𝒟.ιC → ℂ → ℂ}
    {J : 𝒟.ιE → κ → ℂ} (hJ : IsJump 𝒟 Ψ J)
    {𝒯 𝒯s : Finset 𝒟.ιE} (hJ0 : ∀ e ∈ 𝒯s, J e = 0)
    {Z : 𝒟.ιE → 𝒟.ιE → ℤ} (hZ' : FlowDecomp (κ → ℂ) 𝒟 𝒯 Z) {I : 𝒟.ιE → κ → ℂ}
    {P : 𝒟.ιE → 𝒟.ιE → ℤ} (hJF : JumpFormula 𝒯 𝒯s Z I J P) :
    AddSubgroup.closure (Set.range J) ≤
      AddSubgroup.closure ((zv Z I) '' ((𝒯 ∪ 𝒯s)ᶜ : Finset 𝒟.ιE)) := by
  classical
  refine (closure_jumps_le 𝒟 hvert hZ' hJ hJ0).trans ?_
  rw [AddSubgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  have hj' : j ∉ 𝒯s := by
    simp only [Finset.coe_compl, Finset.coe_union, Set.mem_compl_iff, Set.mem_union,
      Finset.mem_coe, not_or] at hj
    exact hj.2
  have hJj : J j = -∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ, (P j l : ℂ) • zv Z I l := hJF j hj'
  simp only [hJj, Int.cast_smul_eq_zsmul]
  refine AddSubgroup.neg_mem _ (AddSubgroup.sum_mem _ fun l hl => ?_)
  have hmem : zv Z I l ∈ (zv Z I) '' ((𝒯 ∪ 𝒯s)ᶜ : Finset 𝒟.ιE) := ⟨l, hl, rfl⟩
  exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure hmem) _

noncomputable def per (Z : 𝒟.ιE → 𝒟.ιE → ℤ) (Iθ : 𝒟.ιE → ℂ) (j : 𝒟.ιE) : ℂ := ∑ e, (Z j e : ℂ) * Iθ e

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [Fintype κ] in

theorem sum_smul_eq_sum_per {𝒯 𝒯s : Finset 𝒟.ιE} {Z : 𝒟.ιE → 𝒟.ιE → ℤ}
    (hZ' : FlowDecomp (κ → ℂ) 𝒟 𝒯 Z) {J : 𝒟.ιE → κ → ℂ}
    (hK : ∀ w, (∑ e with (𝒟.ends e).2 = w, J e) = ∑ e with (𝒟.ends e).1 = w, J e)
    (hJ0 : ∀ e ∈ 𝒯s, J e = 0) (Iθ : 𝒟.ιE → ℂ) :
    ∑ e, Iθ e • J e = ∑ j ∈ (𝒯 ∪ 𝒯s)ᶜ, per Z Iθ j • J j := by
  classical
  have hdec : ∀ e, J e = ∑ l ∈ 𝒯ᶜ, Z l e • J l := hZ' J hK
  have hvec : ∑ e, Iθ e • J e = ∑ l ∈ 𝒯ᶜ, per Z Iθ l • J l := by
    calc ∑ e, Iθ e • J e = ∑ e, ∑ l ∈ 𝒯ᶜ, (Iθ e * Z l e) • J l := by
          refine Finset.sum_congr rfl fun e _ => ?_
          conv_lhs => rw [hdec e]
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [← Int.cast_smul_eq_zsmul ℂ, smul_smul]
      _ = ∑ l ∈ 𝒯ᶜ, ∑ e, (Iθ e * Z l e) • J l := Finset.sum_comm
      _ = ∑ l ∈ 𝒯ᶜ, per Z Iθ l • J l := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [← Finset.sum_smul]
          congr 1
          simp only [per]
          exact Finset.sum_congr rfl fun e _ => by ring
  rw [hvec, Finset.compl_union]
  refine (Finset.sum_subset Finset.inter_subset_left fun l hl hl' => ?_).symm
  have hls : l ∈ 𝒯s := by
    by_contra h
    exact hl' (Finset.mem_inter.2 ⟨hl, Finset.mem_compl.2 h⟩)
  rw [hJ0 l hls, smul_zero]

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [Fintype κ] in

theorem sum_mul_jump_eq (hvert : Function.Injective 𝒟.vert) {Ψ : κ → 𝒟.ιC → ℂ → ℂ}
    {J : 𝒟.ιE → κ → ℂ} (hJ : IsJump 𝒟 Ψ J)
    {𝒯 𝒯s : Finset 𝒟.ιE} (hJ0 : ∀ e ∈ 𝒯s, J e = 0)
    {Z : 𝒟.ιE → 𝒟.ιE → ℤ} (hZ' : FlowDecomp (κ → ℂ) 𝒟 𝒯 Z) {I : 𝒟.ιE → κ → ℂ}
    {P : 𝒟.ιE → 𝒟.ιE → ℤ} (hJF : JumpFormula 𝒯 𝒯s Z I J P) (Iθ : 𝒟.ιE → ℂ) (i : κ) :
    ∑ e, Iθ e * J e i =
      -∑ j ∈ (𝒯 ∪ 𝒯s)ᶜ, ∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ, per Z Iθ j * (P j l : ℂ) * zv Z I l i := by
  classical
  have hvec := congrFun (sum_smul_eq_sum_per hZ' (jumps_kirchhoff 𝒟 hvert hJ) hJ0 Iθ) i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hvec
  rw [hvec, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ∉ 𝒯s := by
    simp only [Finset.compl_union, Finset.mem_inter, Finset.mem_compl] at hj
    exact hj.2
  have hJj := congrFun (hJF j hj') i
  simp only [Pi.neg_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hJj
  rw [hJj, mul_neg, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun l _ => by ring

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [Fintype κ] in

theorem per_eq_zv (Z : 𝒟.ιE → 𝒟.ιE → ℤ) (η : κ → Ω[F⁄ℂ]) (j : 𝒟.ιE) (i : κ) :
    per Z (fun e => edgeInt 𝒟 (η i) e) j = zv Z (Ivec 𝒟 η) j i := by
  simp only [per, zv, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Ivec]

omit [Fintype κ] in
include hfg hF in

theorem riemann (hvert : Function.Injective 𝒟.vert) (hP : PrimData 𝒟 η V Ψ)
    {J : 𝒟.ιE → κ → ℂ} (hJ : IsJump 𝒟 Ψ J)
    {𝒯 𝒯s : Finset 𝒟.ιE} (hJ0 : ∀ e ∈ 𝒯s, J e = 0)
    {Z : 𝒟.ιE → 𝒟.ιE → ℤ} (hZ' : FlowDecomp (κ → ℂ) 𝒟 𝒯 Z)
    {P : 𝒟.ιE → 𝒟.ιE → ℤ} (hJF : JumpFormula 𝒯 𝒯s Z (Ivec 𝒟 η) J P)
    (hη : ∀ i (Q : Place ℂ F), 0 ≤ Q.ordDifferential (η i)) (i i' : κ) :
    ∑ j ∈ (𝒯 ∪ 𝒯s)ᶜ, ∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ,
      zv Z (Ivec 𝒟 η) j i' * (P j l : ℂ) * zv Z (Ivec 𝒟 η) l i = 0 := by
  classical

  obtain ⟨Ji, hJi, hbook⟩ := AlgebraicCurve.CellDissection.two_pi_I_mul_sum_residue_mul_primitive_eq_sum_jump_mul_edgeInt F hfg hF 𝒟 ∅
    (cellOf 𝒟) (fun v hv => absurd hv (Finset.notMem_empty v)) (η i')
    (fun v hv => absurd hv (Finset.notMem_empty v)) (fun Q _ => hη i' Q)
    (η i) V hP.hVo hP.hKV hP.hVt (Ψ i) (hP.hΨ i)
  have hJi' : ∀ e, Ji e = J e i := by
    intro e
    have h1 := hJi e _ (left_mem_Icc.2 (arc_lt _ _).le)
    have h2 := hJ i e _ (left_mem_Icc.2 (arc_lt _ _).le)
    rw [← h1, ← h2]
  have h0 : ∑ e, edgeInt 𝒟 (η i') e * J e i = 0 := by
    have : ∑ e, Ji e * edgeInt 𝒟 (η i') e = 0 := by
      rw [← hbook, Finset.sum_empty, mul_zero]
    rw [← this]
    exact Finset.sum_congr rfl fun e _ => by rw [hJi' e, mul_comm]
  have := sum_mul_jump_eq hvert hJ hJ0 hZ' hJF (fun e => edgeInt 𝒟 (η i') e) i
  rw [h0] at this
  have h' := (neg_eq_zero.1 this.symm)
  rw [← h']
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  rw [per_eq_zv]

end Identity

end CellPeriods

end Part_identity

section Part_recip

namespace CellPeriods

p2m_open "Complex Set Filter AlgebraicCurve P2MW.S_AlgebraicCurve_exists_loops_pathIntegral_reciprocity_raw.AlgebraicCurve"
open scoped Real Topology Manifold ContDiff

section Recip

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

variable
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))

variable {κ : Type*} [Fintype κ]
variable {𝒟 : AlgebraicCurve.CellDissection F}

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [Fintype κ] in

theorem eq_of_mem_interior' {x : Place ℂ F} {C D : 𝒟.ιC} (hC : x ∈ (𝒟.cell C).interior')
    (hD : x ∈ (𝒟.cell D).carrier) : D = C := by
  by_contra hDC
  have hxC : x ∈ (𝒟.cell C).carrier := by
    obtain ⟨z, hz, rfl⟩ := hC
    exact ⟨z, Kint_subset_K _ hz, rfl⟩
  obtain ⟨k, hk⟩ := exists_mem_arc_of_ne 𝒟 hD hxC hDC
  exact not_mem_interior_of_mem_arc 𝒟 hk C hC

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [Fintype κ] in
theorem cellOf_eq_of_mem_interior' {x : Place ℂ F} {C : 𝒟.ιC} (hC : x ∈ (𝒟.cell C).interior') :
    cellOf 𝒟 x = C :=
  eq_of_mem_interior' hC (mem_cellOf 𝒟 x)

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [Fintype κ] in
open scoped Classical in

theorem sum_cells_collapse (S : Finset (Place ℂ F)) (hS : ∀ v ∈ S, ∃ C : 𝒟.ιC, v ∈ (𝒟.cell C).interior')
    (f : 𝒟.ιC → Place ℂ F → ℂ) :
    ∑ C : 𝒟.ιC, ∑ v ∈ S.filter (fun v => v ∈ (𝒟.cell C).interior'), f C v =
      ∑ v ∈ S, f (cellOf 𝒟 v) v := by
  classical
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v hv => ?_
  obtain ⟨C, hC⟩ := hS v hv
  have hcv : cellOf 𝒟 v = C := cellOf_eq_of_mem_interior' hC
  have hiff : ∀ D : 𝒟.ιC, v ∈ (𝒟.cell D).interior' ↔ D = C :=
    fun D => ⟨fun hD => eq_of_mem_interior' hC (by
        obtain ⟨z, hz, rfl⟩ := hD
        exact ⟨z, Kint_subset_K _ hz, rfl⟩),
      fun h => h ▸ hC⟩
  simp_rw [hiff]
  simp [Finset.sum_ite_eq', hcv]

variable {η : κ → Ω[F⁄ℂ]} {V : 𝒟.ιC → Set ℂ} {Ψ : κ → 𝒟.ιC → ℂ → ℂ}

omit [Fintype κ] in
open scoped Classical in
include hfg hF in

theorem recip_core (hvert : Function.Injective 𝒟.vert) (hP : PrimData 𝒟 η V Ψ)
    {J : 𝒟.ιE → κ → ℂ} (hJ : IsJump 𝒟 Ψ J)
    {𝒯 𝒯s : Finset 𝒟.ιE} (hJ0 : ∀ e ∈ 𝒯s, J e = 0)
    {Z : 𝒟.ιE → 𝒟.ιE → ℤ} (hZ' : FlowDecomp (κ → ℂ) 𝒟 𝒯 Z)
    {P : 𝒟.ιE → 𝒟.ιE → ℤ} (hJF : JumpFormula 𝒯 𝒯s Z (Ivec 𝒟 η) J P)
    {θ : Ω[F⁄ℂ]} (S : Finset (Place ℂ F))
    (hθpol : ∀ v ∈ S, -1 ≤ v.ordDifferential θ)
    (hθreg : ∀ Q : Place ℂ F, Q ∉ S → 0 ≤ Q.ordDifferential θ)
    (hS : ∀ v ∈ S, ∃ C : 𝒟.ιC, v ∈ (𝒟.cell C).interior') (i : κ) :
    2 * π * I * ∑ v ∈ S, Place.evalAt v (v.dCoordFn * v.differentialCoeff θ) *
        gvec 𝒟 Ψ v (cellOf 𝒟 v) i =
      -∑ j ∈ (𝒯 ∪ 𝒯s)ᶜ, ∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ,
        per Z (fun e => edgeInt 𝒟 θ e) j * (P j l : ℂ) * zv Z (Ivec 𝒟 η) l i := by
  classical

  have hpolK : ∀ (C : 𝒟.ιC), ∀ v ∈ S, v ∈ (𝒟.cell C).carrier → v ∈ (𝒟.cell C).interior' := by
    intro C v hv hvC
    obtain ⟨C', hC'⟩ := hS v hv
    rwa [eq_of_mem_interior' hC' hvC]
  obtain ⟨Ji, hJi, hbook⟩ := AlgebraicCurve.CellDissection.two_pi_I_mul_sum_residue_mul_primitive_eq_sum_jump_mul_edgeInt F hfg hF 𝒟 S
    (cellOf 𝒟) (fun v hv => hpolK _ v hv (mem_cellOf 𝒟 v)) θ hθpol hθreg
    (η i) V hP.hVo hP.hKV hP.hVt (Ψ i) (hP.hΨ i)
  have hJi' : ∀ e, Ji e = J e i := by
    intro e
    have h1 := hJi e _ (left_mem_Icc.2 (arc_lt _ _).le)
    have h2 := hJ i e _ (left_mem_Icc.2 (arc_lt _ _).le)
    rw [← h1, ← h2]
  have hrhs : ∑ e, Ji e * edgeInt 𝒟 θ e = ∑ e, edgeInt 𝒟 θ e * J e i :=
    Finset.sum_congr rfl fun e _ => by rw [hJi' e, mul_comm]
  rw [hrhs, sum_mul_jump_eq hvert hJ hJ0 hZ' hJF _ i] at hbook
  rw [← hbook]
  rfl

end Recip

end CellPeriods

end Part_recip

section Part_g2prims

namespace CellPeriods

p2m_open "Complex Set Filter AlgebraicCurve P2MW.S_AlgebraicCurve_exists_loops_pathIntegral_reciprocity_raw.AlgebraicCurve Metric"
open scoped Real Topology Manifold ContDiff

section G2Prims

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

variable
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))

variable {R : Type*}
variable (𝒟 : AlgebraicCurve.CellDissection F) (S : Finset (Place ℂ F)) (θ : R → Ω[F⁄ℂ])

structure PolePos : Prop where
  hd2 : ∀ C : 𝒟.ιC, ((𝒟.cell C).carrier ∩ (S : Set (Place ℂ F))).Subsingleton
  hd5 : ∀ v ∈ S, ∃ C : 𝒟.ιC, v ∈ (𝒟.cell C).interior' ∧ (𝒟.cell C).ζ v = (𝒟.cell C).R.q

variable {𝒟 S}

variable (hθ : ∀ r v, -1 ≤ v.ordDifferential (θ r) ∧ (v ∉ S → 0 ≤ v.ordDifferential (θ r)))

end G2Prims

end CellPeriods

end Part_g2prims

section Part_g2final

namespace CellPeriods

p2m_open "Complex Set Filter AlgebraicCurve P2MW.S_AlgebraicCurve_exists_loops_pathIntegral_reciprocity_raw.AlgebraicCurve Metric"
open scoped Real Topology Manifold ContDiff

section G2Final

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

variable
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))

section Shift

variable {R : Type*} {𝒟 : AlgebraicCurve.CellDissection F} {S : Finset (Place ℂ F)} (θ : R → Ω[F⁄ℂ])

end Shift

section Quot

variable {R : Type} [Fintype R]
variable {𝒟 : AlgebraicCurve.CellDissection F} {S : Finset (Place ℂ F)} (θ : R → Ω[F⁄ℂ])
variable (hθ : ∀ r v, -1 ≤ v.ordDifferential (θ r) ∧ (v ∉ S → 0 ≤ v.ordDifferential (θ r)))

include hfg hF in

theorem g2_clause {n : ℕ} (b : Module.Basis (Fin n) ℂ ↥(regularDifferentials ℂ F))
    (S : Finset (Place ℂ F)) (𝒟 : AlgebraicCurve.CellDissection F)
    (hS : PolePos 𝒟 S) (hvert : Function.Injective 𝒟.vert) {𝒯 𝒯s : Finset 𝒟.ιE}
    (h𝒯s : ∀ C C' : 𝒟.ιC, ∃! c : 𝒟.ιE → ℤ, (∀ e ∉ 𝒯s, c e = 0) ∧
      ∀ D, (∑ e with (arcOf 𝒟 (e, true)).1 = D, c e) - (∑ e with (arcOf 𝒟 (e, false)).1 = D, c e) =
        (if D = C' then (1 : ℤ) else 0) - (if D = C then 1 else 0))
    {Z : 𝒟.ιE → 𝒟.ιE → ℤ} (hZ : FlowDecomp ℤ 𝒟 𝒯 Z)
    (hZall : ∀ (A : Type) [AddCommGroup A], FlowDecomp A 𝒟 𝒯 Z)
    (γ : ∀ l : 𝒟.ιE, Path (𝒟.vert (𝒟.ends l).1) (𝒟.vert (𝒟.ends l).1))
    (hγs : ∀ l ∉ 𝒯, ∀ t, γ l t ∈ skeleton 𝒟)
    (hγi : ∀ l ∉ 𝒯, ∀ θ : Ω[F⁄ℂ], RegOnSkeleton 𝒟 θ →
      (∃ g, IsPrimitiveAlong θ (γ l) g) ∧ pathIntegral θ (γ l) = ∑ e, (Z l e : ℂ) * edgeInt 𝒟 θ e)
    (hWD : (∃ e, e ∉ 𝒯s) → ∃ (m : ℕ) (_ : NeZero m) (wd : ZMod m ≃ {q : 𝒟.ιE × Bool // q.1 ∉ 𝒯s}),
      (∀ i : ZMod m, endV 𝒟 (wd i).1 = startV 𝒟 (wd (i + 1)).1 ∧
        ∃ cs : List 𝒟.ιC, cs.head? = some (arcOf 𝒟 (wd i).1).1 ∧
          cs.getLast? = some (arcOf 𝒟 (wd (i + 1)).1).1 ∧
          cs.IsChain (fun D D' => ∃ g ∈ 𝒯s,
            (((arcOf 𝒟 (g, true)).1 = D ∧ (arcOf 𝒟 (g, false)).1 = D') ∨
              ((arcOf 𝒟 (g, true)).1 = D' ∧ (arcOf 𝒟 (g, false)).1 = D)) ∧
            (endV 𝒟 (wd i).1 = (𝒟.ends g).1 ∨ endV 𝒟 (wd i).1 = (𝒟.ends g).2))) ∧
      ∀ (e : 𝒟.ιE) (he : e ∉ 𝒯s) (w : 𝒟.ιV),
        (∑ f with (𝒟.ends f).2 = w, wordChain wd e he f) =
          ∑ f with (𝒟.ends f).1 = w, wordChain wd e he f)
    {Pt : Place ℂ F} (δ : Path Pt Pt) (hδ : ∀ t, δ t ∉ S) :
    ∃ (c : 𝒟.ιE → ℤ) (w : Place ℂ F → ℤ), ∀ ϑ : Ω[F⁄ℂ],
      (∀ v : Place ℂ F, -1 ≤ v.ordDifferential ϑ) →
      (∀ v : Place ℂ F, v ∉ S → 0 ≤ v.ordDifferential ϑ) →
      pathIntegral ϑ δ = ∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ, (c l : ℂ) * pathIntegral ϑ (γ l) +
        2 * Real.pi * Complex.I *
          ∑ v ∈ S, (w v : ℂ) * Place.evalAt v (v.dCoordFn * v.differentialCoeff ϑ) :=
  haveI : Module.Finite ℂ ↥(regularDifferentials ℂ F) := Module.Finite.of_basis b
  AlgebraicCurve.CellDissection.exists_int_pathIntegral_eq_sum_periods_add_sum_residues F hfg hF 𝒟 hvert S
    hS.hd2 hS.hd5 𝒯 𝒯s h𝒯s Z hZ hZall γ hγs hγi hWD δ hδ

end Quot

end G2Final

end CellPeriods

end Part_g2final

section Part_final

namespace CellPeriods

p2m_open "Complex Set Filter AlgebraicCurve P2MW.S_AlgebraicCurve_exists_loops_pathIntegral_reciprocity_raw.AlgebraicCurve"
open scoped Real Topology Manifold ContDiff

section Final

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

variable
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))

noncomputable abbrev bfam {n : ℕ} (b : Module.Basis (Fin n) ℂ ↥(regularDifferentials ℂ F)) :
    Fin n → Ω[F⁄ℂ] :=
  fun i => (b i : Ω[F⁄ℂ])

omit [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem bfam_regular {n : ℕ} (b : Module.Basis (Fin n) ℂ ↥(regularDifferentials ℂ F))
    (i : Fin n) (Q : Place ℂ F) : 0 ≤ Q.ordDifferential (bfam b i) :=
  ordDifferential_nonneg_of_mem_regularDifferentials (b i).2 Q

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem not_mem_of_mem_skeleton (𝒟 : AlgebraicCurve.CellDissection F) {T : Set (Place ℂ F)}
    (hd1 : ∀ v ∈ T, ∃ C : 𝒟.ιC, v ∈ (𝒟.cell C).interior') {x : Place ℂ F}
    (hx : x ∈ skeleton 𝒟) : x ∉ T := by
  intro hxT
  obtain ⟨C, hC⟩ := hd1 x hxT
  simp only [skeleton, AlgebraicCurve.CellDissection.skeleton, mem_iUnion] at hx
  obtain ⟨p, hp⟩ := hx
  exact not_mem_interior_of_mem_arc 𝒟 hp C hC

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem regOnSkeleton_of (𝒟 : AlgebraicCurve.CellDissection F) {T : Set (Place ℂ F)}
    (hd1 : ∀ v ∈ T, ∃ C : 𝒟.ιC, v ∈ (𝒟.cell C).interior') {θ : Ω[F⁄ℂ]}
    (hθ : ∀ Q : Place ℂ F, Q ∉ T → 0 ≤ Q.ordDifferential θ) : RegOnSkeleton 𝒟 θ :=
  fun _ hx => hθ _ (not_mem_of_mem_skeleton 𝒟 hd1 hx)

include hfg hF in

theorem pathIntegral_expand {n : ℕ} (b : Module.Basis (Fin n) ℂ ↥(regularDifferentials ℂ F))
    {ξ : Ω[F⁄ℂ]} (hξ : ξ ∈ regularDifferentials ℂ F) {P P' : Place ℂ F} (δ : Path P P') :
    pathIntegral ξ δ = ∑ i, b.repr ⟨ξ, hξ⟩ i * pathIntegral (bfam b i) δ := by
  classical
  have hexp : ξ = ∑ i, b.repr ⟨ξ, hξ⟩ i • bfam b i := by
    have := b.sum_repr ⟨ξ, hξ⟩
    have h := congrArg Subtype.val this
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    exact h.symm
  have hsum := pathIntegral_sum hF Finset.univ (fun i => b.repr ⟨ξ, hξ⟩ i) (bfam b) δ
    (fun i _ t => bfam_regular b i _)
    (fun i _ => (AlgebraicCurve.exists_isPrimitiveAlong_of_forall_ordDifferential_nonneg F hfg hF
      (bfam b i) δ fun t => bfam_regular b i _).1)
    (fun s _ t => by
      refine ordDifferential_nonneg_of_mem_regularDifferentials ?_ _
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (b i).2)
  conv_lhs => rw [hexp]
  exact hsum.2

variable {n : ℕ} (b : Module.Basis (Fin n) ℂ ↥(regularDifferentials ℂ F))
variable (P₀ : Place ℂ F) (S : Finset (Place ℂ F))
variable (𝒟 : AlgebraicCurve.CellDissection F)
variable (hd1 : ∀ v ∈ insert P₀ (S : Set (Place ℂ F)), ∃ C : 𝒟.ιC, v ∈ (𝒟.cell C).interior')
variable (hvert : Function.Injective 𝒟.vert)
variable (𝒯 𝒯s : Finset 𝒟.ιE)
variable (Z : 𝒟.ιE → 𝒟.ιE → ℤ) (hZ : FlowDecomp ℤ 𝒟 𝒯 Z) (hZ' : FlowDecomp (Fin n → ℂ) 𝒟 𝒯 Z)
variable (γ : ∀ l : 𝒟.ιE, Path (𝒟.vert (𝒟.ends l).1) (𝒟.vert (𝒟.ends l).1))
variable (hγs : ∀ l ∉ 𝒯, ∀ t, γ l t ∈ skeleton 𝒟)
variable (hγi : ∀ l ∉ 𝒯, ∀ θ : Ω[F⁄ℂ], RegOnSkeleton 𝒟 θ →
  (∃ g, IsPrimitiveAlong θ (γ l) g) ∧ pathIntegral θ (γ l) = ∑ e, (Z l e : ℂ) * edgeInt 𝒟 θ e)
variable (V : 𝒟.ιC → Set ℂ) (Ψ : Fin n → 𝒟.ιC → ℂ → ℂ) (J : 𝒟.ιE → Fin n → ℂ)
variable (hP : PrimData 𝒟 (bfam b) V Ψ) (hJ : IsJump 𝒟 Ψ J) (hJ0 : ∀ e ∈ 𝒯s, J e = 0)
variable (hΨ0 : ∀ i, Ψ i (cellOf 𝒟 P₀) ((𝒟.cell (cellOf 𝒟 P₀)).ζ P₀) = 0)
variable (P : 𝒟.ιE → 𝒟.ιE → ℤ) (hJF : JumpFormula 𝒯 𝒯s Z (Ivec 𝒟 (bfam b)) J P)
variable (hPalt : ∀ j ∈ (𝒯 ∪ 𝒯s)ᶜ, ∀ l ∈ (𝒯 ∪ 𝒯s)ᶜ, P l j = -P j l)

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem mem_Jx {j : 𝒟.ιE} (hj : j ∈ (𝒯 ∪ 𝒯s)ᶜ) : j ∉ 𝒯 ∧ j ∉ 𝒯s := by
  simpa [Finset.compl_union, Finset.mem_inter] using hj

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem image_finset_eq_range {β : Type*} (f : 𝒟.ιE → β) (s : Finset 𝒟.ιE) :
    f '' (s : Set 𝒟.ιE) = Set.range (fun l : s => f l) := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, Finset.mem_coe.1 ha⟩, rfl⟩
  · rintro ⟨⟨a, ha⟩, rfl⟩
    exact ⟨a, Finset.mem_coe.2 ha, rfl⟩

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
include hγi in

theorem per_eq_pathIntegral {l : 𝒟.ιE} (hl : l ∉ 𝒯) {θ : Ω[F⁄ℂ]} (hθ : RegOnSkeleton 𝒟 θ) :
    per Z (fun e => edgeInt 𝒟 θ e) l = pathIntegral θ (γ l) := by
  rw [(hγi l hl θ hθ).2]; rfl

omit [T2Space (Place ℂ F)] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
include hγi in
theorem zv_eq_pathIntegral {l : 𝒟.ιE} (hl : l ∉ 𝒯) (i : Fin n) :
    zv Z (Ivec 𝒟 (bfam b)) l i = pathIntegral (bfam b i) (γ l) := by
  rw [← per_eq_zv, per_eq_pathIntegral 𝒟 𝒯 Z γ hγi hl (fun Q _ => bfam_regular b i Q)]

include hfg hF hvert hγi hP hJ hJ0 hZ' hJF in

theorem g1_basis {Pt : Place ℂ F} (δ : Path Pt Pt) :
    ∃ c : 𝒟.ιE → ℤ, ∀ i, pathIntegral (bfam b i) δ =
      ∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ, c l * pathIntegral (bfam b i) (γ l) := by
  classical

  have hg := fun i => (AlgebraicCurve.exists_isPrimitiveAlong_of_forall_ordDifferential_nonneg
    F hfg hF (bfam b i) δ fun t => bfam_regular b i _).1
  choose g hg using hg
  have hmem := period_mem_closure_jumps hfg hF hP hJ δ g hg
  have hmem' := closure_jumps_le_zv hvert hJ hJ0 hZ' hJF hmem
  rw [← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup,
    image_finset_eq_range, Submodule.mem_span_range_iff_exists_fun] at hmem'
  obtain ⟨c, hc⟩ := hmem'
  refine ⟨fun l => if hl : l ∈ (𝒯 ∪ 𝒯s)ᶜ then c ⟨l, hl⟩ else 0, fun i => ?_⟩
  have hci := congrFun hc i
  simp only [Finset.sum_apply, Pi.smul_apply] at hci
  simp only [zsmul_eq_mul] at hci
  rw [pathIntegral_eq_of_isPrimitiveAlong (hg i), ← hci, ← Finset.sum_coe_sort ((𝒯 ∪ 𝒯s)ᶜ)]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [dif_pos l.2]
  rw [zv_eq_pathIntegral b 𝒟 𝒯 Z γ hγi (mem_Jx 𝒟 𝒯 𝒯s l.2).1]

include hfg hF hvert hγi hP hJ hJ0 hZ' hJF in

theorem g1_clause {Pt : Place ℂ F} (δ : Path Pt Pt) :
    ∃ c : 𝒟.ιE → ℤ, ∀ ξ ∈ regularDifferentials ℂ F, pathIntegral ξ δ =
      ∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ, c l * pathIntegral ξ (γ l) := by
  obtain ⟨c, hc⟩ := g1_basis hfg hF b 𝒟 hvert 𝒯 𝒯s Z hZ' γ hγi V Ψ J hP hJ hJ0 P hJF δ
  refine ⟨c, fun ξ hξ => ?_⟩
  rw [pathIntegral_expand hfg hF b hξ δ]
  simp_rw [hc, pathIntegral_expand hfg hF b hξ (γ _), Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => ?_
  ring

include hfg hF hvert hγi hP hJ hJ0 hZ' hJF in
theorem riemann_clause {ξ : Ω[F⁄ℂ]} (hξ : ξ ∈ regularDifferentials ℂ F)
    {ξ' : Ω[F⁄ℂ]} (hξ' : ξ' ∈ regularDifferentials ℂ F) :
    ∑ j ∈ (𝒯 ∪ 𝒯s)ᶜ, ∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ,
      (P j l : ℂ) * pathIntegral ξ (γ j) * pathIntegral ξ' (γ l) = 0 := by
  classical
  have hR := fun i i' => riemann hfg hF hvert hP hJ hJ0 hZ' hJF (fun i Q => bfam_regular b i Q) i i'

  have hx : ∀ j ∈ (𝒯 ∪ 𝒯s)ᶜ, pathIntegral ξ (γ j) =
      ∑ i', b.repr ⟨ξ, hξ⟩ i' * zv Z (Ivec 𝒟 (bfam b)) j i' := by
    intro j hj
    rw [pathIntegral_expand hfg hF b hξ (γ j)]
    exact Finset.sum_congr rfl fun i' _ => by
      rw [zv_eq_pathIntegral b 𝒟 𝒯 Z γ hγi (mem_Jx 𝒟 𝒯 𝒯s hj).1]
  have hx' : ∀ l ∈ (𝒯 ∪ 𝒯s)ᶜ, pathIntegral ξ' (γ l) =
      ∑ i, b.repr ⟨ξ', hξ'⟩ i * zv Z (Ivec 𝒟 (bfam b)) l i := by
    intro l hl
    rw [pathIntegral_expand hfg hF b hξ' (γ l)]
    exact Finset.sum_congr rfl fun i _ => by
      rw [zv_eq_pathIntegral b 𝒟 𝒯 Z γ hγi (mem_Jx 𝒟 𝒯 𝒯s hl).1]
  calc ∑ j ∈ (𝒯 ∪ 𝒯s)ᶜ, ∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ,
        (P j l : ℂ) * pathIntegral ξ (γ j) * pathIntegral ξ' (γ l)
      = ∑ j ∈ (𝒯 ∪ 𝒯s)ᶜ, ∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ, ∑ i', ∑ i,
          b.repr ⟨ξ, hξ⟩ i' * b.repr ⟨ξ', hξ'⟩ i *
            (zv Z (Ivec 𝒟 (bfam b)) j i' * (P j l : ℂ) * zv Z (Ivec 𝒟 (bfam b)) l i) := by
        refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun l hl => ?_
        rw [hx j hj, hx' l hl, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i' _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ i', ∑ i, b.repr ⟨ξ, hξ⟩ i' * b.repr ⟨ξ', hξ'⟩ i *
          ∑ j ∈ (𝒯 ∪ 𝒯s)ᶜ, ∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ,
            zv Z (Ivec 𝒟 (bfam b)) j i' * (P j l : ℂ) * zv Z (Ivec 𝒟 (bfam b)) l i := by

        have e1 : ∀ j ∈ (𝒯 ∪ 𝒯s)ᶜ, (∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ, ∑ i', ∑ i,
            b.repr ⟨ξ, hξ⟩ i' * b.repr ⟨ξ', hξ'⟩ i *
              (zv Z (Ivec 𝒟 (bfam b)) j i' * (P j l : ℂ) * zv Z (Ivec 𝒟 (bfam b)) l i)) =
            ∑ i', ∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ, ∑ i,
              b.repr ⟨ξ, hξ⟩ i' * b.repr ⟨ξ', hξ'⟩ i *
                (zv Z (Ivec 𝒟 (bfam b)) j i' * (P j l : ℂ) * zv Z (Ivec 𝒟 (bfam b)) l i) :=
          fun j _ => Finset.sum_comm
        rw [Finset.sum_congr rfl e1, Finset.sum_comm]
        refine Finset.sum_congr rfl fun i' _ => ?_
        have e2 : ∀ j ∈ (𝒯 ∪ 𝒯s)ᶜ, (∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ, ∑ i,
            b.repr ⟨ξ, hξ⟩ i' * b.repr ⟨ξ', hξ'⟩ i *
              (zv Z (Ivec 𝒟 (bfam b)) j i' * (P j l : ℂ) * zv Z (Ivec 𝒟 (bfam b)) l i)) =
            ∑ i, ∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ,
              b.repr ⟨ξ, hξ⟩ i' * b.repr ⟨ξ', hξ'⟩ i *
                (zv Z (Ivec 𝒟 (bfam b)) j i' * (P j l : ℂ) * zv Z (Ivec 𝒟 (bfam b)) l i) :=
          fun j _ => Finset.sum_comm
        rw [Finset.sum_congr rfl e2, Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
    _ = 0 := by
        refine Finset.sum_eq_zero fun i' _ => Finset.sum_eq_zero fun i _ => ?_
        rw [hR i i', mul_zero]

include hfg hF hvert hγi hP hJ hJ0 hZ' hJF in
theorem unimod_clause (hcard : ((𝒯 ∪ 𝒯s)ᶜ).card = 2 * n)
    (hspan : Submodule.span ℝ (pathPeriodLattice (bfam b) : Set (Fin n → ℂ)) = ⊤) :
    IsUnit (Matrix.of fun j l : ((𝒯 ∪ 𝒯s)ᶜ : Finset 𝒟.ιE) => P j l).det := by
  classical
  refine isUnit_det_of_lattice (V := Fin n → ℂ)
    (fun l : ((𝒯 ∪ 𝒯s)ᶜ : Finset 𝒟.ιE) => zv Z (Ivec 𝒟 (bfam b)) l)
    (fun j : ((𝒯 ∪ 𝒯s)ᶜ : Finset 𝒟.ιE) => J j) _ ?_ ?_ ?_ ?_
  · intro j
    simp only [Matrix.of_apply]
    rw [hJF j (mem_Jx 𝒟 𝒯 𝒯s j.2).2, ← Finset.sum_coe_sort ((𝒯 ∪ 𝒯s)ᶜ)]
    simp only [Int.cast_smul_eq_zsmul]
  ·
    intro l
    have hl := (mem_Jx 𝒟 𝒯 𝒯s l.2).1
    have hg := fun i => (hγi l hl (bfam b i)
      (regOnSkeleton_of 𝒟 (T := ∅) (fun v hv => absurd hv (Set.notMem_empty v))
        (fun Q _ => bfam_regular b i Q))).1
    choose g hg using hg
    have hmem := period_mem_closure_jumps hfg hF hP hJ (γ l) g hg
    have hmem' := closure_jumps_le 𝒟 hvert hZ' hJ hJ0 hmem
    have heq : (fun i => g i 1 - g i 0) = zv Z (Ivec 𝒟 (bfam b)) l := by
      funext i
      rw [zv_eq_pathIntegral b 𝒟 𝒯 Z γ hγi hl, pathIntegral_eq_of_isPrimitiveAlong (hg i)]
    rw [heq, image_finset_eq_range] at hmem'
    exact hmem'
  ·
    rw [← hspan, Submodule.span_le]
    intro u hu
    refine Submodule.span_induction (p := fun u _ => u ∈ (Submodule.span ℝ (Set.range
      fun l : ((𝒯 ∪ 𝒯s)ᶜ : Finset 𝒟.ιE) => zv Z (Ivec 𝒟 (bfam b)) l) : Set (Fin n → ℂ)))
      ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨Pt, δ, rfl⟩
      obtain ⟨c, hc⟩ := g1_basis hfg hF b 𝒟 hvert 𝒯 𝒯s Z hZ' γ hγi V Ψ J hP hJ hJ0 P hJF δ
      have : (fun i => pathIntegral (bfam b i) δ) =
          ∑ l : ((𝒯 ∪ 𝒯s)ᶜ : Finset 𝒟.ιE), (c l : ℝ) • zv Z (Ivec 𝒟 (bfam b)) l := by
        funext i
        rw [hc i, ← Finset.sum_coe_sort ((𝒯 ∪ 𝒯s)ᶜ)]
        simp only [Finset.sum_apply, Pi.smul_apply]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [zv_eq_pathIntegral b 𝒟 𝒯 Z γ hγi (mem_Jx 𝒟 𝒯 𝒯s l.2).1, Complex.real_smul]
        push_cast; rfl
      rw [SetLike.mem_coe, this]
      exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
    · exact zero_mem _
    · intro x y _ _ hx hy; exact add_mem hx hy
    · intro m x _ hx
      rw [SetLike.mem_coe] at hx ⊢
      rw [← Int.cast_smul_eq_zsmul ℝ]
      exact Submodule.smul_mem _ _ hx
  · rw [Fintype.card_coe, hcard, finrank_real_of_complex, Module.finrank_pi, Fintype.card_fin]

include hfg hF hvert hγi hP hJ hJ0 hZ' hJF hd1 hΨ0 hPalt in
theorem recip_clause [ConnectedSpace (Place ℂ F)] (E : Divisor ℂ F) (θ : Ω[F⁄ℂ])
    (hθ1 : ∀ v : Place ℂ F, -1 ≤ v.ordDifferential θ)
    (hres : ∀ v : Place ℂ F, Place.evalAt v (v.dCoordFn * v.differentialCoeff θ) = (E v : ℂ))
    (hE : ∀ v : Place ℂ F, E v ≠ 0 → v ∈ S) :
    ∃ c : 𝒟.ιE → ℤ, ∀ i : Fin n,
      ∑ j ∈ (𝒯 ∪ 𝒯s)ᶜ, ∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ,
          (P j l : ℂ) * pathIntegral (bfam b i) (γ j) * pathIntegral θ (γ l) =
        2 * π * I * (abelJacobiDiv (bfam b) P₀ E i +
          ∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ, c l * pathIntegral (bfam b i) (γ l)) := by
  classical
  haveI : LocallyPathConnectedSpace (Place ℂ F) := ChartedSpace.locallyPathConnectedSpace ℂ (Place ℂ F)
  haveI : PathConnectedSpace (Place ℂ F) := pathConnectedSpace_iff_connectedSpace.2 inferInstance

  have hθreg : ∀ Q : Place ℂ F, Q ∉ S → 0 ≤ Q.ordDifferential θ := by
    intro Q hQ
    refine ordDifferential_nonneg_of_res_eq_zero Q (hθ1 Q) ?_
    rw [hres]
    have : E Q = 0 := by
      by_contra h
      exact hQ (hE Q h)
    simp [this]
  have hθsk : RegOnSkeleton 𝒟 θ :=
    regOnSkeleton_of 𝒟 hd1 fun Q hQ => hθreg Q fun h => hQ (Set.mem_insert_of_mem _ h)
  have hS : ∀ v ∈ S, ∃ C : 𝒟.ιC, v ∈ (𝒟.cell C).interior' :=
    fun v hv => hd1 v (Set.mem_insert_of_mem _ hv)

  have core := recip_core hfg hF hvert hP hJ hJ0 hZ' hJF S (fun v hv => hθ1 v) hθreg hS

  have hAJ : ∀ v : Place ℂ F, ∃ c : ((𝒯 ∪ 𝒯s)ᶜ : Finset 𝒟.ιE) → ℤ,
      abelJacobiVec (bfam b) P₀ v =
        gvec 𝒟 Ψ v (cellOf 𝒟 v) + ∑ l, c l • zv Z (Ivec 𝒟 (bfam b)) l := by
    intro v
    have hne : Nonempty (Path P₀ v) := ⟨(PathConnectedSpace.joined P₀ v).somePath⟩
    rw [abelJacobiVec_def, dif_pos hne]
    set γv := Classical.choice hne
    have hg := fun i => (AlgebraicCurve.exists_isPrimitiveAlong_of_forall_ordDifferential_nonneg
      F hfg hF (bfam b i) γv fun t => bfam_regular b i _).1
    choose g hg using hg
    have hmem := path_sub_mem_closure_jumps hfg hF hP hJ γv g hg
    have hmem' := closure_jumps_le_zv hvert hJ hJ0 hZ' hJF hmem
    rw [← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup,
      image_finset_eq_range, Submodule.mem_span_range_iff_exists_fun] at hmem'
    obtain ⟨c, hc⟩ := hmem'
    refine ⟨c, ?_⟩
    have h0 : gvec 𝒟 Ψ P₀ (cellOf 𝒟 P₀) = 0 := by
      funext i; exact hΨ0 i
    rw [h0, sub_zero] at hc
    have hint : (fun i => pathIntegral (bfam b i) γv) = fun i => g i 1 - g i 0 := by
      funext i; exact pathIntegral_eq_of_isPrimitiveAlong (hg i)
    rw [hint, hc]
    abel
  choose cv hcv using hAJ
  refine ⟨fun l => if hl : l ∈ (𝒯 ∪ 𝒯s)ᶜ then -∑ v ∈ S, E v * cv v ⟨l, hl⟩ else 0, fun i => ?_⟩

  have e1 : ∀ j ∈ (𝒯 ∪ 𝒯s)ᶜ, pathIntegral (bfam b i) (γ j) = zv Z (Ivec 𝒟 (bfam b)) j i :=
    fun j hj => (zv_eq_pathIntegral b 𝒟 𝒯 Z γ hγi (mem_Jx 𝒟 𝒯 𝒯s hj).1 i).symm
  have e2 : ∀ l ∈ (𝒯 ∪ 𝒯s)ᶜ, pathIntegral θ (γ l) = per Z (fun e => edgeInt 𝒟 θ e) l :=
    fun l hl => (per_eq_pathIntegral 𝒟 𝒯 Z γ hγi (mem_Jx 𝒟 𝒯 𝒯s hl).1 hθsk).symm
  have hLHS : ∑ j ∈ (𝒯 ∪ 𝒯s)ᶜ, ∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ,
      (P j l : ℂ) * pathIntegral (bfam b i) (γ j) * pathIntegral θ (γ l) =
      -∑ j ∈ (𝒯 ∪ 𝒯s)ᶜ, ∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ,
        per Z (fun e => edgeInt 𝒟 θ e) j * (P j l : ℂ) * zv Z (Ivec 𝒟 (bfam b)) l i := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [e1 j hj, e2 l hl, hPalt l hl j hj]
    push_cast
    ring
  rw [hLHS, ← core i]

  have hg : ∀ v, gvec 𝒟 Ψ v (cellOf 𝒟 v) i =
      abelJacobiVec (bfam b) P₀ v i - ∑ l, cv v l * zv Z (Ivec 𝒟 (bfam b)) l i := by
    intro v
    have := congrFun (hcv v) i
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply] at this
    simp only [zsmul_eq_mul] at this
    rw [this]; ring
  have hAJD : abelJacobiDiv (bfam b) P₀ E i = ∑ v ∈ S, (E v : ℂ) * abelJacobiVec (bfam b) P₀ v i := by
    rw [abelJacobiDiv_apply, Finsupp.sum, Finset.sum_apply]
    have hsub : E.support ⊆ S := fun v hv => hE v (Finsupp.mem_support_iff.1 hv)
    rw [Finset.sum_subset hsub (f := fun v => (E v • abelJacobiVec (bfam b) P₀ v) i)
      (fun v _ hv => by simp only [Finsupp.notMem_support_iff.1 hv, zero_smul, Pi.zero_apply])]
    exact Finset.sum_congr rfl fun v _ => by simp [zsmul_eq_mul]
  simp_rw [hres, hg]
  rw [hAJD]

  have hκ : ∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ,
      ((if hl : l ∈ (𝒯 ∪ 𝒯s)ᶜ then -∑ v ∈ S, E v * cv v ⟨l, hl⟩ else 0 : ℤ) : ℂ) *
        pathIntegral (bfam b i) (γ l) =
      -∑ v ∈ S, (E v : ℂ) * ∑ l, cv v l * zv Z (Ivec 𝒟 (bfam b)) l i := by
    rw [← Finset.sum_coe_sort ((𝒯 ∪ 𝒯s)ᶜ)]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [dif_pos l.2, e1 l l.2, ← Finset.sum_neg_distrib]
    push_cast
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    ring
  rw [hκ]
  rw [show ∑ v ∈ S, (E v : ℂ) * abelJacobiVec (bfam b) P₀ v i +
      -∑ v ∈ S, (E v : ℂ) * ∑ l, cv v l * zv Z (Ivec 𝒟 (bfam b)) l i =
      ∑ v ∈ S, (E v : ℂ) * (abelJacobiVec (bfam b) P₀ v i -
        ∑ l, cv v l * zv Z (Ivec 𝒟 (bfam b)) l i) by
    rw [← sub_eq_add_neg, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun v _ => by ring]

include hfg hF hvert hγs hγi hP hJ hJ0 hZ' hJF hd1 hΨ0 hPalt in

theorem i1_core [ConnectedSpace (Place ℂ F)] (hcard : ((𝒯 ∪ 𝒯s)ᶜ).card = 2 * n)
    (hspan : Submodule.span ℝ (pathPeriodLattice (bfam b) : Set (Fin n → ℂ)) = ⊤)
    (hG2 : ∀ (Pt : Place ℂ F) (δ : Path Pt Pt), (∀ t, δ t ∉ S) →
      ∃ (c : 𝒟.ιE → ℤ) (w : Place ℂ F → ℤ), ∀ θ : Ω[F⁄ℂ],
        (∀ v : Place ℂ F, -1 ≤ v.ordDifferential θ) →
        (∀ v : Place ℂ F, v ∉ S → 0 ≤ v.ordDifferential θ) →
        pathIntegral θ δ = ∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ, (c l : ℂ) * pathIntegral θ (γ l) +
          2 * Real.pi * Complex.I *
            ∑ v ∈ S, (w v : ℂ) * Place.evalAt v (v.dCoordFn * v.differentialCoeff θ)) :
    ∃ (Pz : Fin n ⊕ Fin n → Place ℂ F) (Zk : ∀ k, Path (Pz k) (Pz k))
      (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ),
      (∀ k t, Zk k t ∉ S ∧ Zk k t ≠ P₀) ∧ Q.transpose = -Q ∧ IsUnit Q.det ∧
      (∀ (Pt : Place ℂ F) (δ : Path Pt Pt), ∃ κ : Fin n ⊕ Fin n → ℤ,
        ∀ ξ ∈ regularDifferentials ℂ F,
          pathIntegral ξ δ = ∑ k, ((κ k : ℂ) * pathIntegral ξ (Zk k))) ∧
      (∀ (Pt : Place ℂ F) (δ : Path Pt Pt), (∀ t, δ t ∉ S) →
        ∃ (κ : Fin n ⊕ Fin n → ℤ) (w : Place ℂ F → ℤ), ∀ θ : Ω[F⁄ℂ],
          (∀ v : Place ℂ F, -1 ≤ v.ordDifferential θ) →
          (∀ v : Place ℂ F, v ∉ S → 0 ≤ v.ordDifferential θ) →
          pathIntegral θ δ =
            ∑ k, ((κ k : ℂ) * pathIntegral θ (Zk k)) +
              2 * Real.pi * Complex.I *
                ∑ v ∈ S, (w v : ℂ) * Place.evalAt v (v.dCoordFn * v.differentialCoeff θ)) ∧
      (∀ ξ ∈ regularDifferentials ℂ F, ∀ ξ' ∈ regularDifferentials ℂ F,
        ∑ k, ∑ l, (Q k l : ℂ) * pathIntegral ξ (Zk k) * pathIntegral ξ' (Zk l) = 0) ∧
      (∀ (E : Divisor ℂ F) (θ : Ω[F⁄ℂ]),
        (∀ v : Place ℂ F, -1 ≤ v.ordDifferential θ) →
        (∀ v : Place ℂ F, Place.evalAt v (v.dCoordFn * v.differentialCoeff θ) = (E v : ℂ)) →
        (∀ v : Place ℂ F, E v ≠ 0 → v ∈ S) →
        ∃ κ : Fin n ⊕ Fin n → ℤ, ∀ i : Fin n,
          ∑ k, ∑ l, (Q k l : ℂ) * pathIntegral (b i : Ω[F⁄ℂ]) (Zk k) * pathIntegral θ (Zk l) =
            2 * Real.pi * Complex.I *
              (abelJacobiDiv (fun i => (b i : Ω[F⁄ℂ])) P₀ E i +
                ∑ k, ((κ k : ℂ) * pathIntegral (b i : Ω[F⁄ℂ]) (Zk k)))) := by
  classical

  have hcard' : Fintype.card (Fin n ⊕ Fin n) = Fintype.card ((𝒯 ∪ 𝒯s)ᶜ : Finset 𝒟.ιE) := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_coe, hcard]; ring
  set eJ : Fin n ⊕ Fin n ≃ ((𝒯 ∪ 𝒯s)ᶜ : Finset 𝒟.ιE) := Fintype.equivOfCardEq hcard' with heJ
  have hre : ∀ f : 𝒟.ιE → ℂ, ∑ k, f (eJ k) = ∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ, f l := fun f => by
    rw [Equiv.sum_comp eJ (fun j : ((𝒯 ∪ 𝒯s)ᶜ : Finset 𝒟.ιE) => f j)]
    exact Finset.sum_coe_sort _ f
  have hmemJ : ∀ k, (eJ k : 𝒟.ιE) ∉ 𝒯 ∧ (eJ k : 𝒟.ιE) ∉ 𝒯s := fun k => mem_Jx 𝒟 𝒯 𝒯s (eJ k).2
  refine ⟨fun k => 𝒟.vert (𝒟.ends (eJ k)).1, fun k => γ (eJ k),
    Matrix.of fun k l => P (eJ k) (eJ l), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro k t
    have h := not_mem_of_mem_skeleton 𝒟 hd1 (hγs _ (hmemJ k).1 t)
    simp only [Set.mem_insert_iff, Finset.mem_coe, not_or] at h
    exact ⟨h.2, h.1⟩
  ·
    ext k l
    simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.of_apply]
    exact hPalt _ (eJ k).2 _ (eJ l).2
  ·
    have hsub : (Matrix.of fun k l => P (eJ k) (eJ l)) =
        (Matrix.of fun j l : ((𝒯 ∪ 𝒯s)ᶜ : Finset 𝒟.ιE) => P j l).submatrix eJ eJ := by
      ext k l; rfl
    rw [hsub, Matrix.det_submatrix_equiv_self]
    exact unimod_clause hfg hF b 𝒟 hvert 𝒯 𝒯s Z hZ' γ hγi V Ψ J hP hJ hJ0 P hJF hcard hspan
  ·
    intro Pt δ
    beta_reduce
    obtain ⟨c, hc⟩ := g1_clause hfg hF b 𝒟 hvert 𝒯 𝒯s Z hZ' γ hγi V Ψ J hP hJ hJ0 P hJF δ
    refine ⟨fun k => c (eJ k), fun ξ hξ => ?_⟩
    rw [hc ξ hξ, ← hre (fun l => (c l : ℂ) * pathIntegral ξ (γ l))]
  ·
    intro Pt δ hδ
    beta_reduce
    obtain ⟨c, w, hcw⟩ := hG2 Pt δ hδ
    refine ⟨fun k => c (eJ k), w, fun θ h1 h2 => ?_⟩
    rw [hcw θ h1 h2, ← hre (fun l => (c l : ℂ) * pathIntegral θ (γ l))]
  ·
    intro ξ hξ ξ' hξ'
    beta_reduce
    have h := riemann_clause hfg hF b 𝒟 hvert 𝒯 𝒯s Z hZ' γ hγi V Ψ J hP hJ hJ0 P hJF hξ hξ'
    rw [← hre (fun j => ∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ,
      (P j l : ℂ) * pathIntegral ξ (γ j) * pathIntegral ξ' (γ l))] at h
    rw [← h]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hre (fun l => (P (eJ k) l : ℂ) * pathIntegral ξ (γ (eJ k)) * pathIntegral ξ' (γ l))]
    rfl
  ·
    intro E θ h1 hres hE
    beta_reduce
    obtain ⟨c, hc⟩ := recip_clause hfg hF b P₀ S 𝒟 hd1 hvert 𝒯 𝒯s Z hZ' γ hγi V Ψ J hP hJ hJ0
      hΨ0 P hJF hPalt E θ h1 hres hE
    refine ⟨fun k => c (eJ k), fun i => ?_⟩
    have h := hc i
    rw [← hre (fun j => ∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ,
      (P j l : ℂ) * pathIntegral (bfam b i) (γ j) * pathIntegral θ (γ l)),
      ← hre (fun l => (c l : ℂ) * pathIntegral (bfam b i) (γ l))] at h
    rw [← h]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hre (fun l => (P (eJ k) l : ℂ) * pathIntegral (bfam b i) (γ (eJ k)) * pathIntegral θ (γ l))]
    rfl

include hfg hF hvert hγs hγi hP hJ hJ0 hZ' hJF hd1 hΨ0 hPalt in

theorem i1_full [ConnectedSpace (Place ℂ F)] (hcard : ((𝒯 ∪ 𝒯s)ᶜ).card = 2 * n)
    (hspan : Submodule.span ℝ (pathPeriodLattice (bfam b) : Set (Fin n → ℂ)) = ⊤)
    (hS : PolePos 𝒟 S)
    (h𝒯s : ∀ C C' : 𝒟.ιC, ∃! c : 𝒟.ιE → ℤ, (∀ e ∉ 𝒯s, c e = 0) ∧
      ∀ D, (∑ e with (arcOf 𝒟 (e, true)).1 = D, c e) - (∑ e with (arcOf 𝒟 (e, false)).1 = D, c e) =
        (if D = C' then (1 : ℤ) else 0) - (if D = C then 1 else 0))
    (hZ : FlowDecomp ℤ 𝒟 𝒯 Z) (hZall : ∀ (A : Type) [AddCommGroup A], FlowDecomp A 𝒟 𝒯 Z)
    (hWD : (∃ e, e ∉ 𝒯s) → ∃ (m : ℕ) (_ : NeZero m) (wd : ZMod m ≃ {q : 𝒟.ιE × Bool // q.1 ∉ 𝒯s}),
      (∀ i : ZMod m, endV 𝒟 (wd i).1 = startV 𝒟 (wd (i + 1)).1 ∧
        ∃ cs : List 𝒟.ιC, cs.head? = some (arcOf 𝒟 (wd i).1).1 ∧
          cs.getLast? = some (arcOf 𝒟 (wd (i + 1)).1).1 ∧
          cs.IsChain (fun D D' => ∃ g ∈ 𝒯s,
            (((arcOf 𝒟 (g, true)).1 = D ∧ (arcOf 𝒟 (g, false)).1 = D') ∨
              ((arcOf 𝒟 (g, true)).1 = D' ∧ (arcOf 𝒟 (g, false)).1 = D)) ∧
            (endV 𝒟 (wd i).1 = (𝒟.ends g).1 ∨ endV 𝒟 (wd i).1 = (𝒟.ends g).2))) ∧
      ∀ (e : 𝒟.ιE) (he : e ∉ 𝒯s) (w : 𝒟.ιV),
        (∑ f with (𝒟.ends f).2 = w, wordChain wd e he f) =
          ∑ f with (𝒟.ends f).1 = w, wordChain wd e he f) :
    ∃ (Pz : Fin n ⊕ Fin n → Place ℂ F) (Zk : ∀ k, Path (Pz k) (Pz k))
      (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ),
      (∀ k t, Zk k t ∉ S ∧ Zk k t ≠ P₀) ∧ Q.transpose = -Q ∧ IsUnit Q.det ∧
      (∀ (Pt : Place ℂ F) (δ : Path Pt Pt), ∃ κ : Fin n ⊕ Fin n → ℤ,
        ∀ ξ ∈ regularDifferentials ℂ F,
          pathIntegral ξ δ = ∑ k, ((κ k : ℂ) * pathIntegral ξ (Zk k))) ∧
      (∀ (Pt : Place ℂ F) (δ : Path Pt Pt), (∀ t, δ t ∉ S) →
        ∃ (κ : Fin n ⊕ Fin n → ℤ) (w : Place ℂ F → ℤ), ∀ θ : Ω[F⁄ℂ],
          (∀ v : Place ℂ F, -1 ≤ v.ordDifferential θ) →
          (∀ v : Place ℂ F, v ∉ S → 0 ≤ v.ordDifferential θ) →
          pathIntegral θ δ =
            ∑ k, ((κ k : ℂ) * pathIntegral θ (Zk k)) +
              2 * Real.pi * Complex.I *
                ∑ v ∈ S, (w v : ℂ) * Place.evalAt v (v.dCoordFn * v.differentialCoeff θ)) ∧
      (∀ ξ ∈ regularDifferentials ℂ F, ∀ ξ' ∈ regularDifferentials ℂ F,
        ∑ k, ∑ l, (Q k l : ℂ) * pathIntegral ξ (Zk k) * pathIntegral ξ' (Zk l) = 0) ∧
      (∀ (E : Divisor ℂ F) (θ : Ω[F⁄ℂ]),
        (∀ v : Place ℂ F, -1 ≤ v.ordDifferential θ) →
        (∀ v : Place ℂ F, Place.evalAt v (v.dCoordFn * v.differentialCoeff θ) = (E v : ℂ)) →
        (∀ v : Place ℂ F, E v ≠ 0 → v ∈ S) →
        ∃ κ : Fin n ⊕ Fin n → ℤ, ∀ i : Fin n,
          ∑ k, ∑ l, (Q k l : ℂ) * pathIntegral (b i : Ω[F⁄ℂ]) (Zk k) * pathIntegral θ (Zk l) =
            2 * Real.pi * Complex.I *
              (abelJacobiDiv (fun i => (b i : Ω[F⁄ℂ])) P₀ E i +
                ∑ k, ((κ k : ℂ) * pathIntegral (b i : Ω[F⁄ℂ]) (Zk k)))) :=
  i1_core hfg hF b P₀ S 𝒟 hd1 hvert 𝒯 𝒯s Z hZ' γ hγs hγi V Ψ J hP hJ hJ0 hΨ0 P hJF hPalt hcard hspan
    fun _ δ hδ => g2_clause hfg hF b S 𝒟 hS hvert h𝒯s hZ hZall γ hγs hγi hWD δ hδ

end Final

end CellPeriods

end Part_final

section Part_asm

namespace CellPeriods

p2m_open "Complex Set Filter AlgebraicCurve P2MW.S_AlgebraicCurve_exists_loops_pathIntegral_reciprocity_raw.AlgebraicCurve"
open scoped Real Topology Manifold ContDiff

theorem i1
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
    (S : Finset (Place ℂ F)) :
    ∃ (Pz : Fin n ⊕ Fin n → Place ℂ F) (Z : ∀ k, Path (Pz k) (Pz k))
      (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ),
      (∀ k t, Z k t ∉ S ∧ Z k t ≠ P₀) ∧ Q.transpose = -Q ∧ IsUnit Q.det ∧
      (∀ (P : Place ℂ F) (δ : Path P P), ∃ κ : Fin n ⊕ Fin n → ℤ,
        ∀ ξ ∈ regularDifferentials ℂ F,
          pathIntegral ξ δ = ∑ k, ((κ k : ℂ) * pathIntegral ξ (Z k))) ∧
      (∀ (P : Place ℂ F) (δ : Path P P), (∀ t, δ t ∉ S) →
        ∃ (κ : Fin n ⊕ Fin n → ℤ) (w : Place ℂ F → ℤ), ∀ θ : Ω[F⁄ℂ],
          (∀ v : Place ℂ F, -1 ≤ v.ordDifferential θ) →
          (∀ v : Place ℂ F, v ∉ S → 0 ≤ v.ordDifferential θ) →
          pathIntegral θ δ =
            ∑ k, ((κ k : ℂ) * pathIntegral θ (Z k)) +
              2 * Real.pi * Complex.I *
                ∑ v ∈ S, (w v : ℂ) * Place.evalAt v (v.dCoordFn * v.differentialCoeff θ)) ∧
      (∀ ξ ∈ regularDifferentials ℂ F, ∀ ξ' ∈ regularDifferentials ℂ F,
        ∑ k, ∑ l, (Q k l : ℂ) * pathIntegral ξ (Z k) * pathIntegral ξ' (Z l) = 0) ∧
      (∀ (E : Divisor ℂ F) (θ : Ω[F⁄ℂ]),
        (∀ v : Place ℂ F, -1 ≤ v.ordDifferential θ) →
        (∀ v : Place ℂ F, Place.evalAt v (v.dCoordFn * v.differentialCoeff θ) = (E v : ℂ)) →
        (∀ v : Place ℂ F, E v ≠ 0 → v ∈ S) →
        ∃ κ : Fin n ⊕ Fin n → ℤ, ∀ i : Fin n,
          ∑ k, ∑ l, (Q k l : ℂ) * pathIntegral (b i : Ω[F⁄ℂ]) (Z k) * pathIntegral θ (Z l) =
            2 * Real.pi * Complex.I *
              (abelJacobiDiv (fun i => (b i : Ω[F⁄ℂ])) P₀ E i +
                ∑ k, ((κ k : ℂ) * pathIntegral (b i : Ω[F⁄ℂ]) (Z k)))) := by
  classical
  have hfg' := hfg
  obtain ⟨x, hx, hfd⟩ := hfg'
  haveI : Algebra.EssFiniteType ℂ F := essFiniteType_of_transcendental_of_finiteDimensional hx hfd

  obtain ⟨𝒟, hd1, hd2, hEuler, hd5, hvert, hends⟩ := exists_cellDissection F hfg hF P₀ S
  obtain ⟨C₀, _hC₀⟩ := hd1 P₀ (Set.mem_insert _ _)
  haveI : Nonempty 𝒟.ιC := ⟨C₀⟩

  obtain ⟨𝒯, 𝒯s, h𝒯path, h𝒯s, _hdisj, hcard, hwalk⟩ :=
    AlgebraicCurve.CellDissection.exists_tree_cotree 𝒟 hvert hends hEuler
  have hcard' : ((𝒯 ∪ 𝒯s)ᶜ).card = 2 * n := by
    rw [hcard, Module.finrank_eq_card_basis b, Fintype.card_fin]

  obtain ⟨Z, hZk, hZd, hZ0, hZdec⟩ := exists_fundamentalCycles_of_spanningTree
    (fun e => (𝒟.ends e).2) (fun e => (𝒟.ends e).1) 𝒯 h𝒯path
  have hZA : ∀ (A : Type) [AddCommGroup A], FlowDecomp A 𝒟 𝒯 Z := fun A _ f hf e => hZdec f hf e
  have hZℤ : FlowDecomp ℤ 𝒟 𝒯 Z := hZA ℤ
  have hZ' : FlowDecomp (Fin n → ℂ) 𝒟 𝒯 Z := hZA _

  have hloops : ∀ l : 𝒟.ιE, ∃ γ : Path (𝒟.vert (𝒟.ends l).1) (𝒟.vert (𝒟.ends l).1),
      l ∉ 𝒯 → (∀ t, γ t ∈ skeleton 𝒟) ∧ ∀ θ : Ω[F⁄ℂ], RegOnSkeleton 𝒟 θ →
        (∃ g, IsPrimitiveAlong θ γ g) ∧ pathIntegral θ γ = ∑ e, (Z l e : ℂ) * edgeInt 𝒟 θ e := by
    intro l
    by_cases hl : l ∈ 𝒯
    · exact ⟨Path.refl _, fun h => (h hl).elim⟩
    · obtain ⟨γ, hγ⟩ := exists_loop hfg hF 𝒟 ⟨hZk, hZd, hZ0⟩ h𝒯path hwalk hl
      exact ⟨γ, fun _ => hγ⟩
  choose γ hγ using hloops
  have hγs : ∀ l ∉ 𝒯, ∀ t, γ l t ∈ skeleton 𝒟 := fun l hl => (hγ l hl).1
  have hγi : ∀ l ∉ 𝒯, ∀ θ : Ω[F⁄ℂ], RegOnSkeleton 𝒟 θ →
      (∃ g, IsPrimitiveAlong θ (γ l) g) ∧ pathIntegral θ (γ l) = ∑ e, (Z l e : ℂ) * edgeInt 𝒟 θ e :=
    fun l hl => (hγ l hl).2

  obtain ⟨V, Ψ, J, hP, -, hJ, hJ0, hΨ0⟩ := exists_normalised hfg hF 𝒟 (bfam b) (bfam_regular b) 𝒯s
    h𝒯s (cellOf 𝒟 P₀) ((𝒟.cell (cellOf 𝒟 P₀)).ζ P₀)

  have hS : PolePos 𝒟 S := ⟨hd2, hd5⟩
  have hspan := span_real_pathPeriodLattice_eq_top F hfg hF b

  by_cases hL : ∃ e, e ∉ 𝒯s
  · obtain ⟨hne, wd, hW1, hW3⟩ := AlgebraicCurve.CellDissection.exists_polygonWord 𝒟 hvert 𝒯s h𝒯s hL
    haveI := hne
    have hW1' : ∀ i : ZMod (Fintype.card {q : 𝒟.ιE × Bool // q.1 ∉ 𝒯s}),
        endV 𝒟 (wd i).1 = startV 𝒟 (wd (i + 1)).1 ∧
        ∃ cs : List 𝒟.ιC, cs.head? = some (arcOf 𝒟 (wd i).1).1 ∧
          cs.getLast? = some (arcOf 𝒟 (wd (i + 1)).1).1 ∧
          cs.IsChain (fun D D' => ∃ g ∈ 𝒯s,
            (((arcOf 𝒟 (g, true)).1 = D ∧ (arcOf 𝒟 (g, false)).1 = D') ∨
              ((arcOf 𝒟 (g, true)).1 = D' ∧ (arcOf 𝒟 (g, false)).1 = D)) ∧
            (endV 𝒟 (wd i).1 = (𝒟.ends g).1 ∨ endV 𝒟 (wd i).1 = (𝒟.ends g).2)) := hW1
    have hW3' : ∀ (e : 𝒟.ιE) (he : e ∉ 𝒯s) (w : 𝒟.ιV),
        (∑ f with (𝒟.ends f).2 = w, wordChain wd e he f) =
          ∑ f with (𝒟.ends f).1 = w, wordChain wd e he f := hW3
    have hJF := jump_formula hfg hF hvert hP hJ hJ0 hZℤ hZ' wd hW1' hW3'

    set m' := Fintype.card {e : 𝒟.ιE // e ∉ 𝒯s} with hm'
    haveI : NeZero m' := ⟨(Fintype.card_pos_iff.2 ⟨⟨hL.choose, hL.choose_spec⟩⟩).ne'⟩
    have hm : Fintype.card {q : 𝒟.ιE × Bool // q.1 ∉ 𝒯s} = 2 * m' := by
      rw [Fintype.card_congr (Equiv.prodSubtypeFstEquivSubtypeProd (p := fun e : 𝒟.ιE => e ∉ 𝒯s)),
        Fintype.card_prod, Fintype.card_bool, mul_comm]
    have ιx : Fin m' ≃ {e : 𝒟.ιE // e ∉ 𝒯s} := (Fintype.equivFin _).symm
    have hPalt : ∀ j ∈ (𝒯 ∪ 𝒯s)ᶜ, ∀ l ∈ (𝒯 ∪ 𝒯s)ᶜ, wordMatrix wd l j = -wordMatrix wd j l := by
      intro j hj l hl
      have hj' := (mem_Jx 𝒟 𝒯 𝒯s hj).2
      have hl' := (mem_Jx 𝒟 𝒯 𝒯s hl).2
      simp only [wordMatrix, dif_pos hj', dif_pos hl']
      exact wordChain_antisymm hm ιx wd j l hj' hl'
    have hWD : (∃ e, e ∉ 𝒯s) → ∃ (m : ℕ) (_ : NeZero m)
        (wd : ZMod m ≃ {q : 𝒟.ιE × Bool // q.1 ∉ 𝒯s}),
        (∀ i : ZMod m, endV 𝒟 (wd i).1 = startV 𝒟 (wd (i + 1)).1 ∧
          ∃ cs : List 𝒟.ιC, cs.head? = some (arcOf 𝒟 (wd i).1).1 ∧
            cs.getLast? = some (arcOf 𝒟 (wd (i + 1)).1).1 ∧
            cs.IsChain (fun D D' => ∃ g ∈ 𝒯s,
              (((arcOf 𝒟 (g, true)).1 = D ∧ (arcOf 𝒟 (g, false)).1 = D') ∨
                ((arcOf 𝒟 (g, true)).1 = D' ∧ (arcOf 𝒟 (g, false)).1 = D)) ∧
              (endV 𝒟 (wd i).1 = (𝒟.ends g).1 ∨ endV 𝒟 (wd i).1 = (𝒟.ends g).2))) ∧
        ∀ (e : 𝒟.ιE) (he : e ∉ 𝒯s) (w : 𝒟.ιV),
          (∑ f with (𝒟.ends f).2 = w, wordChain wd e he f) =
            ∑ f with (𝒟.ends f).1 = w, wordChain wd e he f :=
      fun _ => ⟨_, hne, wd, hW1', hW3'⟩
    exact i1_full hfg hF b P₀ S 𝒟 hd1 hvert 𝒯 𝒯s Z hZ' γ hγs hγi V Ψ J hP hJ hJ0 hΨ0
      (wordMatrix wd) hJF hPalt hcard' hspan hS h𝒯s hZℤ hZA hWD
  ·
    have hJF : JumpFormula 𝒯 𝒯s Z (Ivec 𝒟 (bfam b)) J 0 :=
      fun j hj => (hL ⟨j, hj⟩).elim
    have hPalt : ∀ j ∈ (𝒯 ∪ 𝒯s)ᶜ, ∀ l ∈ (𝒯 ∪ 𝒯s)ᶜ, (0 : 𝒟.ιE → 𝒟.ιE → ℤ) l j = -0 := by
      intro j hj; exact (hL ⟨j, (mem_Jx 𝒟 𝒯 𝒯s hj).2⟩).elim
    exact i1_full hfg hF b P₀ S 𝒟 hd1 hvert 𝒯 𝒯s Z hZ' γ hγs hγi V Ψ J hP hJ hJ0 hΨ0
      0 hJF hPalt hcard' hspan hS h𝒯s hZℤ hZA (fun h => (hL h).elim)

end CellPeriods

end Part_asm

open scoped Manifold ContDiff Topology Real
p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_exists_loops_pathIntegral_reciprocity_raw.AlgebraicCurve Complex Set"

universe u

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
    (S : Finset (Place ℂ F)) :
    ∃ (Pz : Fin n ⊕ Fin n → Place ℂ F) (Z : ∀ k, Path (Pz k) (Pz k))
      (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ),
      (∀ k t, Z k t ∉ S ∧ Z k t ≠ P₀) ∧ Q.transpose = -Q ∧ IsUnit Q.det ∧
      (∀ (P : Place ℂ F) (δ : Path P P), ∃ κ : Fin n ⊕ Fin n → ℤ,
        ∀ ξ ∈ regularDifferentials ℂ F,
          pathIntegral ξ δ = ∑ k, ((κ k : ℂ) * pathIntegral ξ (Z k))) ∧
      (∀ (P : Place ℂ F) (δ : Path P P), (∀ t, δ t ∉ S) →
        ∃ (κ : Fin n ⊕ Fin n → ℤ) (w : Place ℂ F → ℤ), ∀ θ : Ω[F⁄ℂ],
          (∀ v : Place ℂ F, -1 ≤ v.ordDifferential θ) →
          (∀ v : Place ℂ F, v ∉ S → 0 ≤ v.ordDifferential θ) →
          pathIntegral θ δ =
            ∑ k, ((κ k : ℂ) * pathIntegral θ (Z k)) +
              2 * Real.pi * Complex.I *
                ∑ v ∈ S, (w v : ℂ) * Place.evalAt v (v.dCoordFn * v.differentialCoeff θ)) ∧
      (∀ ξ ∈ regularDifferentials ℂ F, ∀ ξ' ∈ regularDifferentials ℂ F,
        ∑ k, ∑ l, (Q k l : ℂ) * pathIntegral ξ (Z k) * pathIntegral ξ' (Z l) = 0) ∧
      (∀ (E : Divisor ℂ F) (θ : Ω[F⁄ℂ]),
        (∀ v : Place ℂ F, -1 ≤ v.ordDifferential θ) →
        (∀ v : Place ℂ F, Place.evalAt v (v.dCoordFn * v.differentialCoeff θ) = (E v : ℂ)) →
        (∀ v : Place ℂ F, E v ≠ 0 → v ∈ S) →
        ∃ κ : Fin n ⊕ Fin n → ℤ, ∀ i : Fin n,
          ∑ k, ∑ l, (Q k l : ℂ) * pathIntegral (b i : Ω[F⁄ℂ]) (Z k) * pathIntegral θ (Z l) =
            2 * Real.pi * Complex.I *
              (abelJacobiDiv (fun i => (b i : Ω[F⁄ℂ])) P₀ E i +
                ∑ k, ((κ k : ℂ) * pathIntegral (b i : Ω[F⁄ℂ]) (Z k)))) :=
  CellPeriods.i1 F hfg hF b P₀ S

end S_AlgebraicCurve_exists_loops_pathIntegral_reciprocity_raw
end P2MW
export P2MW.S_AlgebraicCurve_exists_loops_pathIntegral_reciprocity_raw (solution)
