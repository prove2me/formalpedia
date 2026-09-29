-- Prove2me | solution 1 for AlgebraicCurve.Pic0.exists_addEquiv_quotient_submodule_of_chartedSpace_complex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/a698db43-3f0c-52af-8fc3-6a9a5e54e8cc

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_ComplexLineIntegral
import Theorems.Thm_AlgebraicCurve_discreteTopology_pathPeriodLattice_and_span_eq_top
import Theorems.Thm_AlgebraicCurve_abelJacobiDiv_mem_pathPeriodLattice_of_isPrincipal
import Theorems.Thm_AlgebraicCurve_Divisor_isPrincipal_of_abelJacobiDiv_mem_pathPeriodLattice
import Theorems.Thm_AlgebraicCurve_exists_degree_eq_zero_and_abelJacobiDiv_sub_mem_pathPeriodLattice
import Theorems.Thm_AlgebraicCurve_finite_and_finrank_regularDifferentials_eq_genus
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Pic0_exists_addEquiv_quotient_submodule_of_chartedSpace_complex
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion"
p2m_attr_erase "instance" "AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Pic0_exists_addEquiv_quotient_submodule_of_chartedSpace_complex.AlgebraicCurve"
open scoped Manifold ContDiff

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor Divisor.degree Divisor.degZero Divisor.mem_degZero Divisor.IsPrincipal Divisor.mem_principal Pic Pic0 Pic0.mk Pic0.mk_surjective IsCurveOver HasCanonicalDivisor genus Place.evalAt regularDifferentials abelJacobiDiv pathPeriodLattice discreteTopology_pathPeriodLattice_and_span_eq_top abelJacobiDiv_mem_pathPeriodLattice_of_isPrincipal Divisor.isPrincipal_of_abelJacobiDiv_mem_pathPeriodLattice exists_degree_eq_zero_and_abelJacobiDiv_sub_mem_pathPeriodLattice finite_and_finrank_regularDifferentials_eq_genus essFiniteType_of_transcendental_of_finiteDimensional"
namespace Pic0ComplexTorusProof
p2m_open "AlgebraicCurve"

theorem free_finite_finrank_of_discrete_of_span_eq_top {n : ℕ} (L : Submodule ℤ (Fin n → ℂ))
    [DiscreteTopology L] (hspan : Submodule.span ℝ (L : Set (Fin n → ℂ)) = ⊤) :
    Module.Free ℤ L ∧ Module.Finite ℤ L ∧ Module.finrank ℤ L = 2 * n := by
  haveI : IsZLattice ℝ L := ⟨hspan⟩
  haveI hfin : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  haveI hfree : Module.Free ℤ L := ZLattice.module_free ℝ L
  refine ⟨hfree, hfin, ?_⟩
  rw [ZLattice.rank ℝ L, finrank_real_of_complex, Module.finrank_fin_fun]

section AbelJacobi

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

def ajDegZero {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) (P₀ : Place ℂ F) :
    Divisor.degZero (K := ℂ) (F := F) →+ (Fin n → ℂ) ⧸ pathPeriodLattice b :=
  ((pathPeriodLattice b).mkQ.toAddMonoidHom.comp (abelJacobiDiv b P₀)).comp
    (Divisor.degZero (K := ℂ) (F := F)).subtype

theorem ajDegZero_apply {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) (P₀ : Place ℂ F)
    (D : Divisor.degZero (K := ℂ) (F := F)) :
    ajDegZero b P₀ D = (pathPeriodLattice b).mkQ (abelJacobiDiv b P₀ (D : Divisor ℂ F)) := rfl

theorem ajDegZero_eq_zero_iff {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) (P₀ : Place ℂ F)
    (D : Divisor.degZero (K := ℂ) (F := F)) :
    ajDegZero b P₀ D = 0 ↔ abelJacobiDiv b P₀ (D : Divisor ℂ F) ∈ pathPeriodLattice b := by
  rw [ajDegZero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

def ajPic0 {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) (P₀ : Place ℂ F)
    (habel : ∀ D : Divisor ℂ F, Divisor.IsPrincipal D →
      abelJacobiDiv b P₀ D ∈ pathPeriodLattice b) :
    Pic0 ℂ F →+ (Fin n → ℂ) ⧸ pathPeriodLattice b :=
  QuotientAddGroup.lift _ (ajDegZero b P₀) fun D hD => by
    rw [AddSubgroup.mem_addSubgroupOf, Divisor.mem_principal] at hD
    exact (ajDegZero_eq_zero_iff b P₀ D).2 (habel _ hD)

theorem ajPic0_mk {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) (P₀ : Place ℂ F)
    (habel : ∀ D : Divisor ℂ F, Divisor.IsPrincipal D →
      abelJacobiDiv b P₀ D ∈ pathPeriodLattice b)
    (D : Divisor.degZero (K := ℂ) (F := F)) :
    ajPic0 b P₀ habel (Pic0.mk D) = ajDegZero b P₀ D := rfl

theorem ajPic0_injective {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) (P₀ : Place ℂ F)
    (habel : ∀ D : Divisor ℂ F, Divisor.IsPrincipal D →
      abelJacobiDiv b P₀ D ∈ pathPeriodLattice b)
    (hconv : ∀ D : Divisor ℂ F, Divisor.degree D = 0 →
      abelJacobiDiv b P₀ D ∈ pathPeriodLattice b → Divisor.IsPrincipal D) :
    Function.Injective (ajPic0 b P₀ habel) := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective q
  rw [ajPic0_mk, ajDegZero_eq_zero_iff] at hq
  have hD0 : Divisor.degree (D : Divisor ℂ F) = 0 := Divisor.mem_degZero.1 D.2
  change (QuotientAddGroup.mk D : Pic0 ℂ F) = 0
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, Divisor.mem_principal]
  exact hconv _ hD0 hq

theorem ajPic0_surjective {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) (P₀ : Place ℂ F)
    (habel : ∀ D : Divisor ℂ F, Divisor.IsPrincipal D →
      abelJacobiDiv b P₀ D ∈ pathPeriodLattice b)
    (hjac : ∀ u : Fin n → ℂ, ∃ D : Divisor ℂ F, Divisor.degree D = 0 ∧
      abelJacobiDiv b P₀ D - u ∈ pathPeriodLattice b) :
    Function.Surjective (ajPic0 b P₀ habel) := by
  intro q
  obtain ⟨u, rfl⟩ := (pathPeriodLattice b).mkQ_surjective q
  obtain ⟨D, hD0, hDu⟩ := hjac u
  refine ⟨Pic0.mk ⟨D, Divisor.mem_degZero.2 hD0⟩, ?_⟩
  rw [ajPic0_mk, ajDegZero_apply, Submodule.mkQ_apply, Submodule.mkQ_apply]
  exact (Submodule.Quotient.eq _).2 hDu

end AbelJacobi

end AlgebraicCurve.Pic0ComplexTorusProof

open AlgebraicCurve.Pic0ComplexTorusProof in

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
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ)) :
    ∃ (L : Submodule ℤ (Fin (genus ℂ F) → ℂ)),
      Module.Free ℤ L ∧ Module.Finite ℤ L ∧
      Module.finrank ℤ L = 2 * genus ℂ F ∧
      Nonempty (Pic0 ℂ F ≃+ (Fin (genus ℂ F) → ℂ) ⧸ L) := by
  classical

  obtain ⟨x, hx, hfd⟩ := id hfg
  haveI : Algebra.EssFiniteType ℂ F :=
    essFiniteType_of_transcendental_of_finiteDimensional hx hfd
  obtain ⟨hfinΩ, hrk⟩ := finite_and_finrank_regularDifferentials_eq_genus (K := ℂ) (F := F)
  haveI := hfinΩ
  let b : Module.Basis (Fin (genus ℂ F)) ℂ ↥(regularDifferentials ℂ F) :=
    Module.finBasisOfFinrankEq ℂ _ hrk

  obtain ⟨P₀⟩ : Nonempty (Place ℂ F) := inferInstance

  obtain ⟨hdisc, hspan⟩ := discreteTopology_pathPeriodLattice_and_span_eq_top F hfg hF b
  haveI := hdisc
  obtain ⟨hfree, hfin, hrank⟩ :=
    free_finite_finrank_of_discrete_of_span_eq_top (pathPeriodLattice fun i => (b i : Ω[F⁄ℂ])) hspan

  have habel : ∀ D : Divisor ℂ F, Divisor.IsPrincipal D →
      abelJacobiDiv (fun i => (b i : Ω[F⁄ℂ])) P₀ D ∈ pathPeriodLattice fun i => (b i : Ω[F⁄ℂ]) :=
    fun D hD => abelJacobiDiv_mem_pathPeriodLattice_of_isPrincipal F hfg hF (fun i => b i) P₀ D hD
  have hconv : ∀ D : Divisor ℂ F, Divisor.degree D = 0 →
      abelJacobiDiv (fun i => (b i : Ω[F⁄ℂ])) P₀ D ∈ pathPeriodLattice (fun i => (b i : Ω[F⁄ℂ])) →
        Divisor.IsPrincipal D :=
    fun D hD0 hD => Divisor.isPrincipal_of_abelJacobiDiv_mem_pathPeriodLattice F hfg hF b P₀ D hD0 hD
  have hjac : ∀ u : Fin (genus ℂ F) → ℂ, ∃ D : Divisor ℂ F, Divisor.degree D = 0 ∧
      abelJacobiDiv (fun i => (b i : Ω[F⁄ℂ])) P₀ D - u ∈ pathPeriodLattice fun i => (b i : Ω[F⁄ℂ]) :=
    fun u => exists_degree_eq_zero_and_abelJacobiDiv_sub_mem_pathPeriodLattice F hfg hF b P₀ u

  exact ⟨pathPeriodLattice fun i => (b i : Ω[F⁄ℂ]), hfree, hfin, hrank,
    ⟨AddEquiv.ofBijective (ajPic0 (fun i => (b i : Ω[F⁄ℂ])) P₀ habel)
      ⟨ajPic0_injective _ P₀ habel hconv, ajPic0_surjective _ P₀ habel hjac⟩⟩⟩

end
end S_AlgebraicCurve_Pic0_exists_addEquiv_quotient_submodule_of_chartedSpace_complex
end P2MW
export P2MW.S_AlgebraicCurve_Pic0_exists_addEquiv_quotient_submodule_of_chartedSpace_complex (solution)
