-- Prove2me | solution 1 for AlgebraicCurve.exists_pairedCellFamily
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/3bd7058e-c566-53a3-82e8-72c5147e4913

import Mathlib
import Definitions.Def_AlgebraicCurve_CellDissection
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_of_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_sum_fiber_ord_eq_finrank
import Theorems.Thm_AlgebraicCurve_Place_sum_ramification_evalAt_eq
import Theorems.Thm_AlgebraicCurve_CellDissection_euler_count_grid
import Theorems.Thm_AlgebraicCurve_Place_analyticCoord_of_center
import Theorems.Thm_AlgebraicCurve_Place_analyticCoord_of_agree
import Theorems.Thm_AlgebraicCurve_RadialRegion_exists_rect_sixArcs
import Theorems.Thm_AlgebraicCurve_RadialRegion_exists_recip
import Theorems.Thm_AlgebraicCurve_RadialRegion_exists_pow_pullback_laps
import Theorems.Thm_AlgebraicCurve_RadialRegion_exists_window_perimeter
import Theorems.Thm_AlgebraicCurve_RadialRegion_exists_reparam_across_edge
import Theorems.Thm_AlgebraicCurve_RadialRegion_exists_reparam_same_side
import Theorems.Thm_AlgebraicCurve_exists_dissectionScaleData
import Theorems.Thm_AlgebraicCurve_RadialRegion_exists_grid_geometry
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_pairedCellFamily
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe"
p2m_attr_erase "simp" "AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option Elab.async false

section Part_D1Scale

set_option autoImplicit false

p2m_open "AlgebraicCurve~H1 Set"
open scoped Manifold ContDiff Topology

namespace PlaneGrid

def gridSquare (o h : ℝ) (j k : ℤ) : Set ℂ :=
  {z : ℂ | z.re ∈ Set.Icc (o + j * h) (o + (j + 1) * h)
    ∧ z.im ∈ Set.Icc (o + k * h) (o + (k + 1) * h)}

end PlaneGrid

namespace DissectionMaterials

variable {F : Type*} [Field F] [Algebra ℂ F] [TopologicalSpace (Place ℂ F)]
variable [ChartedSpace ℂ (Place ℂ F)]

structure IsSheetFamily (x : F) (n : ℕ) (V : Set ℂ)
    (ζ : Fin n → OpenPartialHomeomorph (Place ℂ F) ℂ) : Prop where
  target : ∀ i, (ζ i).target = V
  forward : ∀ i, ∀ P ∈ (ζ i).source, x ∈ P.toValuationSubring ∧ ζ i P = Place.evalAt P x
  disjoint : Pairwise fun i j => Disjoint (ζ i).source (ζ j).source
  exhaust : ∀ P : Place ℂ F, x ∈ P.toValuationSubring → Place.evalAt P x ∈ V →
    ∃ i, P ∈ (ζ i).source

structure IsNormalChart (g : F) (w : Place ℂ F) (ζ : OpenPartialHomeomorph (Place ℂ F) ℂ) (ρ : ℝ)
    (e : ℕ) : Prop where
  ρ_pos : 0 < ρ
  e_pos : 0 < e
  mem : w ∈ ζ.source
  centre : ζ w = 0
  target : ζ.target = Metric.ball 0 ρ
  sub_chart : ζ.source ⊆ (extChartAt 𝓘(ℂ, ℂ) w).source
  analytic : AnalyticOnNhd ℂ (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) w).symm) (extChartAt 𝓘(ℂ, ℂ) w '' ζ.source)
  deriv_ne : ∀ z ∈ extChartAt 𝓘(ℂ, ℂ) w '' ζ.source, deriv (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) w).symm) z ≠ 0
  form : ∀ P ∈ ζ.source, g ∈ P.toValuationSubring ∧ Place.evalAt P g = (ζ P) ^ e

structure Materials (F : Type*) [Field F] [Algebra ℂ F] [TopologicalSpace (Place ℂ F)]
    [ChartedSpace ℂ (Place ℂ F)] (S : Finset (Place ℂ F)) (P₀ : Place ℂ F) where

  x : F
  hx : Transcendental ℂ x
  hfd : FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F
  n : ℕ
  hn : 0 < n
  hdeg : n = Module.finrank (IntermediateField.adjoin ℂ ({x} : Set F)) F

  Bad : Finset ℂ
  hfib : ∀ b : ℂ, {w : Place ℂ F | x ∈ w.toValuationSubring ∧ Place.evalAt w x = b}.Finite
  hcard : ∀ t : ℂ, t ∉ Bad →
    (hfib t).toFinset.card = n
  hpoles : {w : Place ℂ F | x ∉ w.toValuationSubring}.Finite

  o : ℝ
  hm : ℝ
  hhm : 0 < hm
  jlo : ℤ
  jhi : ℤ
  klo : ℤ
  khi : ℤ
  hjlt : jlo + 1 < jhi
  hklt : klo + 1 < khi

  Rw : ℝ
  hRw : 1 < Rw
  hwin : ∀ z : ℂ, ‖z‖ ≤ Rw →
    (o + jlo * hm < z.re ∧ z.re < o + (jhi + 1) * hm) ∧ (o + klo * hm < z.im ∧ z.im < o + (khi + 1) * hm)
  hinner : ∀ z : ℂ, ‖z‖ < Rw - 1 →
    (o + (jlo + 1) * hm < z.re ∧ z.re < o + jhi * hm) ∧ (o + (klo + 1) * hm < z.im ∧ z.im < o + khi * hm)
  hbadR : ∀ b ∈ Bad, ‖b‖ < Rw - 1

  hbad_off : ∀ b ∈ Bad, ∀ j : ℤ, b.re - o ≠ j * hm ∧ b.im - o ≠ j * hm
  hbad_sep : ∀ b ∈ Bad, ∀ b' ∈ Bad, b ≠ b' →
    2 ≤ |⌊(b.re - o) / hm⌋ - ⌊(b'.re - o) / hm⌋| ∨ 2 ≤ |⌊(b.im - o) / hm⌋ - ⌊(b'.im - o) / hm⌋|

  capAt : ℤ × ℤ → Option ℂ
  hcap : ∀ (p : ℤ × ℤ) (b : ℂ), capAt p = some b ↔
    b ∈ Bad ∧ ⌊(b.re - o) / hm⌋ = p.1 ∧ ⌊(b.im - o) / hm⌋ = p.2

  hperim_plain : ∀ p : ℤ × ℤ, p.1 = jlo ∨ p.1 = jhi ∨ p.2 = klo ∨ p.2 = khi → capAt p = none

  margin : ℤ × ℤ → Set ℂ
  sheet : ℤ × ℤ → Fin n → OpenPartialHomeomorph (Place ℂ F) ℂ
  hmargin_open : ∀ p : ℤ × ℤ, p ∈ Icc jlo jhi ×ˢ Icc klo khi → capAt p = none → IsOpen (margin p)
  hmargin_sq : ∀ p : ℤ × ℤ, p ∈ Icc jlo jhi ×ˢ Icc klo khi → capAt p = none →
    PlaneGrid.gridSquare o hm p.1 p.2 ⊆ margin p
  hmargin_bad : ∀ p : ℤ × ℤ, p ∈ Icc jlo jhi ×ˢ Icc klo khi → capAt p = none → ∀ b ∈ Bad, b ∉ margin p
  hsheet : ∀ p : ℤ × ℤ, p ∈ Icc jlo jhi ×ˢ Icc klo khi → capAt p = none →
    IsSheetFamily x n (margin p) (sheet p)

  capζ : ℂ → Place ℂ F → OpenPartialHomeomorph (Place ℂ F) ℂ
  capρ : ℂ → Place ℂ F → ℝ
  cape : ℂ → Place ℂ F → ℕ
  cs : ℂ → ℝ
  hcs : ∀ b ∈ Bad, 4 * hm < cs b
  hcs_sep : ∀ b ∈ Bad, ∀ b' ∈ Bad, b' ≠ b → 2 * cs b ≤ dist b b'
  hcapchart : ∀ b ∈ Bad, ∀ w : Place ℂ F, x ∈ w.toValuationSubring → Place.evalAt w x = b →
    IsNormalChart (x - algebraMap ℂ F b) w (capζ b w) (capρ b w) (cape b w)
  hcapbig : ∀ b ∈ Bad, ∀ w : Place ℂ F, x ∈ w.toValuationSubring → Place.evalAt w x = b →
    2 * cs b < capρ b w ^ cape b w
  hcapdisj : ∀ b ∈ Bad, ∀ w w' : Place ℂ F,
    x ∈ w.toValuationSubring → Place.evalAt w x = b →
    x ∈ w'.toValuationSubring → Place.evalAt w' x = b → w ≠ w' →
    Disjoint (capζ b w).source (capζ b w').source
  hcapexhaust : ∀ b ∈ Bad, ∀ P : Place ℂ F, x ∈ P.toValuationSubring →
    ‖Place.evalAt P x - b‖ < 2 * cs b →
    ∃ w : Place ℂ F, x ∈ w.toValuationSubring ∧ Place.evalAt w x = b ∧ P ∈ (capζ b w).source

  infζ : Place ℂ F → OpenPartialHomeomorph (Place ℂ F) ℂ
  infρ : Place ℂ F → ℝ
  infe : Place ℂ F → ℕ
  hinfchart : ∀ w : Place ℂ F, x ∉ w.toValuationSubring → IsNormalChart x⁻¹ w (infζ w) (infρ w) (infe w)
  hinfbig : ∀ w : Place ℂ F, x ∉ w.toValuationSubring → 1 / Rw < infρ w ^ infe w
  hinfdisj : ∀ w w' : Place ℂ F, x ∉ w.toValuationSubring → x ∉ w'.toValuationSubring → w ≠ w' →
    Disjoint (infζ w).source (infζ w').source
  hinfexhaust : ∀ P : Place ℂ F, x ∈ P.toValuationSubring → Rw ≤ ‖Place.evalAt P x‖ →
    ∃ w : Place ℂ F, x ∉ w.toValuationSubring ∧ P ∈ (infζ w).source

  centre : ℤ × ℤ → ℂ
  hcentre : ∀ p : ℤ × ℤ, (o + p.1 * hm < (centre p).re ∧ (centre p).re < o + (p.1 + 1) * hm) ∧
    (o + p.2 * hm < (centre p).im ∧ (centre p).im < o + (p.2 + 1) * hm)

  hcentre0 : ∀ p : ℤ × ℤ, p.1 = jhi → o + p.2 * hm < 0 → 0 < o + (p.2 + 1) * hm → (centre p).im = 0
  hmarked : ∀ v ∈ insert P₀ (S : Set (Place ℂ F)), x ∈ v.toValuationSubring → Place.evalAt v x ∉ Bad →
    ‖Place.evalAt v x‖ < Rw - 1 ∧
    (∀ j : ℤ, (Place.evalAt v x).re - o ≠ j * hm ∧ (Place.evalAt v x).im - o ≠ j * hm) ∧
    capAt (⌊((Place.evalAt v x).re - o) / hm⌋, ⌊((Place.evalAt v x).im - o) / hm⌋) = none ∧
    centre (⌊((Place.evalAt v x).re - o) / hm⌋, ⌊((Place.evalAt v x).im - o) / hm⌋) = Place.evalAt v x
  hmarked_sep : ∀ v ∈ insert P₀ (S : Set (Place ℂ F)), ∀ v' ∈ insert P₀ (S : Set (Place ℂ F)), x ∈ v.toValuationSubring → x ∈ v'.toValuationSubring →
    Place.evalAt v x ∉ Bad → Place.evalAt v' x ∉ Bad → Place.evalAt v x ≠ Place.evalAt v' x →
    (⌊((Place.evalAt v x).re - o) / hm⌋, ⌊((Place.evalAt v x).im - o) / hm⌋) ≠
      (⌊((Place.evalAt v' x).re - o) / hm⌋, ⌊((Place.evalAt v' x).im - o) / hm⌋)
  hmarked_R : ∀ v ∈ insert P₀ (S : Set (Place ℂ F)), x ∈ v.toValuationSubring → ‖Place.evalAt v x‖ < Rw - 1

end DissectionMaterials

namespace CurveCellFamily

variable {F : Type*} [Field F] [Algebra ℂ F] [TopologicalSpace (Place ℂ F)]
variable [ChartedSpace ℂ (Place ℂ F)]

structure AssemblyData (F : Type*) [Field F] [Algebra ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] where

  x : F

  n : ℕ
  hn : 0 < n

  jlo : ℤ
  jhi : ℤ
  klo : ℤ
  khi : ℤ
  o : ℝ
  hm : ℝ
  hhm : 0 < hm

  capAt : ℤ × ℤ → Option ℂ

  hfib : ∀ b : ℂ, {w : Place ℂ F | x ∈ w.toValuationSubring ∧ Place.evalAt w x = b}.Finite

  margin : ℤ × ℤ → Set ℂ

  sheetζ : ℤ × ℤ → Fin n → OpenPartialHomeomorph (Place ℂ F) ℂ
  hmargin : ∀ p : ℤ × ℤ, p ∈ Set.Icc jlo jhi ×ˢ Set.Icc klo khi → capAt p = none →
    PlaneGrid.gridSquare o hm p.1 p.2 ⊆ margin p
  hζtarget : ∀ p : ℤ × ℤ, p ∈ Set.Icc jlo jhi ×ˢ Set.Icc klo khi → capAt p = none → ∀ i : Fin n, (sheetζ p i).target = margin p
  hζanalytic : ∀ p : ℤ × ℤ, p ∈ Set.Icc jlo jhi ×ˢ Set.Icc klo khi → capAt p = none → ∀ i : Fin n,
    ∀ P ∈ (sheetζ p i).source,
      AnalyticAt ℂ (sheetζ p i ∘ (extChartAt 𝓘(ℂ, ℂ) P).symm) (extChartAt 𝓘(ℂ, ℂ) P P)
  hζderiv : ∀ p : ℤ × ℤ, p ∈ Set.Icc jlo jhi ×ˢ Set.Icc klo khi → capAt p = none → ∀ i : Fin n,
    ∀ P ∈ (sheetζ p i).source,
      deriv (sheetζ p i ∘ (extChartAt 𝓘(ℂ, ℂ) P).symm) (extChartAt 𝓘(ℂ, ℂ) P P) ≠ 0

  rad : ℤ × ℤ → Fin n → RadialRegion
  hradK : ∀ p : ℤ × ℤ, p ∈ Set.Icc jlo jhi ×ˢ Set.Icc klo khi → capAt p = none → ∀ i : Fin n,
    (rad p i).K = PlaneGrid.gridSquare o hm p.1 p.2

  capζ : ℤ × ℤ → Place ℂ F → OpenPartialHomeomorph (Place ℂ F) ℂ
  capRad : ℤ × ℤ → Place ℂ F → RadialRegion
  hcapanalytic : ∀ p : ℤ × ℤ, capAt p ≠ none → ∀ w : Place ℂ F,
    x ∈ w.toValuationSubring → Place.evalAt w x = (capAt p).getD 0 →
    ∀ P ∈ (capζ p w).source,
      AnalyticAt ℂ (capζ p w ∘ (extChartAt 𝓘(ℂ, ℂ) P).symm) (extChartAt 𝓘(ℂ, ℂ) P P)
  hcapderiv : ∀ p : ℤ × ℤ, capAt p ≠ none → ∀ w : Place ℂ F,
    x ∈ w.toValuationSubring → Place.evalAt w x = (capAt p).getD 0 →
    ∀ P ∈ (capζ p w).source,
      deriv (capζ p w ∘ (extChartAt 𝓘(ℂ, ℂ) P).symm) (extChartAt 𝓘(ℂ, ℂ) P P) ≠ 0
  hcapKt : ∀ p : ℤ × ℤ, capAt p ≠ none → ∀ w : Place ℂ F,
    x ∈ w.toValuationSubring → Place.evalAt w x = (capAt p).getD 0 →
    (capRad p w).K ⊆ (capζ p w).target

  hpoles : {w : Place ℂ F | x ∉ w.toValuationSubring}.Finite

  infζ : Place ℂ F → OpenPartialHomeomorph (Place ℂ F) ℂ
  infRad : Place ℂ F → RadialRegion
  hinfanalytic : ∀ w : Place ℂ F, x ∉ w.toValuationSubring →
    ∀ P ∈ (infζ w).source,
      AnalyticAt ℂ (infζ w ∘ (extChartAt 𝓘(ℂ, ℂ) P).symm) (extChartAt 𝓘(ℂ, ℂ) P P)
  hinfderiv : ∀ w : Place ℂ F, x ∉ w.toValuationSubring →
    ∀ P ∈ (infζ w).source,
      deriv (infζ w ∘ (extChartAt 𝓘(ℂ, ℂ) P).symm) (extChartAt 𝓘(ℂ, ℂ) P P) ≠ 0
  hinfKt : ∀ w : Place ℂ F, x ∉ w.toValuationSubring → (infRad w).K ⊆ (infζ w).target

namespace AssemblyData

variable (A : AssemblyData F)

def Win : Set (ℤ × ℤ) := Set.Icc A.jlo A.jhi ×ˢ Set.Icc A.klo A.khi

theorem win_finite : A.Win.Finite := (Set.finite_Icc _ _).prod (Set.finite_Icc _ _)

def Plain : Set (ℤ × ℤ) := {p ∈ A.Win | A.capAt p = none}

def Caps : Set (ℤ × ℤ) := {p ∈ A.Win | A.capAt p ≠ none}

theorem plain_finite : A.Plain.Finite := A.win_finite.subset (sep_subset _ _)
theorem caps_finite : A.Caps.Finite := A.win_finite.subset (sep_subset _ _)

def capVal (p : ℤ × ℤ) : ℂ := (A.capAt p).getD 0

def Fib (b : ℂ) : Type _ :=
  {w : Place ℂ F // A.x ∈ w.toValuationSubring ∧ Place.evalAt w A.x = b}

noncomputable scoped instance (b : ℂ) : Fintype (A.Fib b) :=
  (A.hfib b).fintype

noncomputable scoped instance (b : ℂ) : DecidableEq (A.Fib b) := Classical.decEq _

def FibInf : Type _ := {w : Place ℂ F // A.x ∉ w.toValuationSubring}

noncomputable scoped instance : Fintype A.FibInf := A.hpoles.fintype

noncomputable scoped instance : DecidableEq A.FibInf := Classical.decEq _

def IdxC : Type _ :=
  (Σ _Q : A.plain_finite.toFinset, Fin A.n) ⊕
  (Σ Q : A.caps_finite.toFinset, A.Fib (A.capVal Q)) ⊕
  A.FibInf

noncomputable scoped instance : Fintype A.IdxC := by
  unfold IdxC
  infer_instance

noncomputable scoped instance : DecidableEq A.IdxC := Classical.decEq _

noncomputable def cellPlain (p : ℤ × ℤ) (hw : p ∈ A.Win) (hp : A.capAt p = none) (i : Fin A.n) :
    Cell F where
  ζ := A.sheetζ p i
  analytic := A.hζanalytic p hw hp i
  deriv_ne := A.hζderiv p hw hp i
  R := A.rad p i
  hKt := by
    rw [A.hζtarget p hw hp i, A.hradK p hw hp i]
    exact A.hmargin p hw hp

theorem mem_plain_iff {p : ℤ × ℤ} : p ∈ A.Plain ↔ p ∈ A.Win ∧ A.capAt p = none :=
  Set.mem_sep_iff

theorem mem_caps_iff {p : ℤ × ℤ} : p ∈ A.Caps ↔ p ∈ A.Win ∧ A.capAt p ≠ none :=
  Set.mem_sep_iff

noncomputable def cellCap (p : ℤ × ℤ) (hp : A.capAt p ≠ none)
    (w : A.Fib (A.capVal p)) : Cell F where
  ζ := A.capζ p w.1
  analytic := A.hcapanalytic p hp w.1 w.2.1 w.2.2
  deriv_ne := A.hcapderiv p hp w.1 w.2.1 w.2.2
  R := A.capRad p w.1
  hKt := A.hcapKt p hp w.1 w.2.1 w.2.2

noncomputable def cellInf (w : A.FibInf) : Cell F where
  ζ := A.infζ w.1
  analytic := A.hinfanalytic w.1 w.2
  deriv_ne := A.hinfderiv w.1 w.2
  R := A.infRad w.1
  hKt := A.hinfKt w.1 w.2

noncomputable def cellOf : A.IdxC → Cell F
  | .inl ⟨Q, i⟩ => A.cellPlain Q.1 (A.mem_plain_iff.mp (A.plain_finite.mem_toFinset.mp Q.2)).1
      (A.mem_plain_iff.mp (A.plain_finite.mem_toFinset.mp Q.2)).2 i
  | .inr (.inl ⟨Q, w⟩) =>
      A.cellCap Q.1 ((A.mem_caps_iff.mp (A.caps_finite.mem_toFinset.mp Q.2)).2) w
  | .inr (.inr w) => A.cellInf w

end AssemblyData
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.AssemblyData"

end CurveCellFamily
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.AssemblyData P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily"

end Part_D1Scale
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.AssemblyData P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily"

section Part_D1PairKit

set_option autoImplicit false

p2m_open "AlgebraicCurve~H1 Set Complex"
open scoped Real

namespace ArcPairing

theorem exists_subset_of_isPreconnected {X ι : Type*} [TopologicalSpace X] {L : Set X}
    {U : ι → Set X} (hL : IsPreconnected L) (hne : L.Nonempty) (hopen : ∀ i, IsOpen (U i))
    (hdisj : Pairwise fun i j => Disjoint (U i) (U j)) (hcover : L ⊆ ⋃ i, U i) :
    ∃ i, L ⊆ U i := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover hx)
  refine ⟨i, ?_⟩
  have hrest : IsOpen (⋃ j ∈ ({i}ᶜ : Set ι), U j) := isOpen_biUnion fun j _ => hopen j
  have hsub : L ⊆ U i ∪ ⋃ j ∈ ({i}ᶜ : Set ι), U j := by
    intro y hy
    obtain ⟨j, hyj⟩ := mem_iUnion.mp (hcover hy)
    by_cases hj : j = i
    · exact Or.inl (hj ▸ hyj)
    · exact Or.inr (mem_iUnion₂.mpr ⟨j, hj, hyj⟩)
  have huv : Disjoint (U i) (⋃ j ∈ ({i}ᶜ : Set ι), U j) := by
    rw [Set.disjoint_left]
    intro y hyi hyrest
    obtain ⟨j, hj, hyj⟩ := mem_iUnion₂.mp hyrest
    have hij : i ≠ j := fun h => hj (by simp [h])
    exact Set.disjoint_left.mp (hdisj hij) hyi hyj
  exact hL.subset_left_of_subset_union (hopen i) hrest huv hsub ⟨x, hx, hxi⟩

theorem eq_of_image_subset_of_injOn {α β : Type*} {f : α → β} {L T : Set α} (hLT : L ⊆ T)
    (himage : f '' T ⊆ f '' L) (hinj : InjOn f T) : L = T := by
  refine Subset.antisymm hLT fun t ht => ?_
  obtain ⟨l, hl, hfl⟩ := himage ⟨t, ht, rfl⟩
  exact (hinj (hLT hl) ht hfl) ▸ hl

end ArcPairing
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.AssemblyData P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily"

namespace CellFacts

theorem periodic_apply_arg {r : ℝ → ℝ} (hper : Function.Periodic r (2 * π)) {t : ℝ} (ht : 0 < t)
    (φ : ℝ) : r (arg ((t : ℂ) * exp (φ * I))) = r φ := by
  rw [arg_real_mul _ ht, arg_exp_mul_I, toIocMod]
  exact hper.sub_zsmul_eq _

section Region

variable (R : RadialRegion)

theorem loop_mem_K (φ : ℝ) : R.loop φ ∈ R.K := by
  show ‖R.loop φ - R.q‖ ≤ R.r (arg (R.loop φ - R.q))
  have h : R.loop φ - R.q = ((R.r φ : ℝ) : ℂ) * exp (φ * I) := by
    unfold RadialRegion.loop
    ring
  rw [h, periodic_apply_arg R.hper (R.hpos φ), norm_mul, norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (R.hpos φ)]

theorem continuous_loop : Continuous R.loop := by
  have hr := R.hcont
  unfold RadialRegion.loop
  fun_prop

theorem arcSet_subset_K (k : Fin R.N) : R.arcSet k ⊆ R.K := by
  rintro _ ⟨φ, -, rfl⟩
  exact loop_mem_K R φ

theorem castSucc_mem_arcIcc (k : Fin R.N) : R.φs k.castSucc ∈ R.arcIcc k :=
  left_mem_Icc.mpr (R.hmono Fin.castSucc_lt_succ).le

theorem arcSet_nonempty (k : Fin R.N) : (R.arcSet k).Nonempty :=
  ⟨_, _, castSucc_mem_arcIcc R k, rfl⟩

theorem isPreconnected_arcSet (k : Fin R.N) : IsPreconnected (R.arcSet k) :=
  isPreconnected_Icc.image _ (continuous_loop R).continuousOn

end Region
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.AssemblyData P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily"

section CellSide

variable {F : Type*} [Field F] [Algebra ℂ F] [TopologicalSpace (Place ℂ F)]
variable [ChartedSpace ℂ (Place ℂ F)]

omit [ChartedSpace ℂ (Place ℂ F)] in

theorem symm_image_eq {ζ : OpenPartialHomeomorph (Place ℂ F) ℂ} {s : Set ℂ} (hs : s ⊆ ζ.target) :
    ζ.symm '' s = {P | P ∈ ζ.source ∧ ζ P ∈ s} := by
  ext P
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨ζ.map_target (hs hz), by rwa [ζ.right_inv (hs hz)]⟩
  · rintro ⟨hP, hz⟩
    exact ⟨ζ P, hz, ζ.left_inv hP⟩

variable (C : Cell F)

theorem arcSet_subset_target (k : Fin C.R.N) : C.R.arcSet k ⊆ C.ζ.target :=
  (arcSet_subset_K C.R k).trans C.hKt

theorem arc_eq (k : Fin C.R.N) : C.arc k = {P | P ∈ C.ζ.source ∧ C.ζ P ∈ C.R.arcSet k} :=
  symm_image_eq (arcSet_subset_target C k)

theorem arc_subset_source (k : Fin C.R.N) : C.arc k ⊆ C.ζ.source := by
  rw [arc_eq]
  exact fun _ h => h.1

theorem arc_subset_carrier (k : Fin C.R.N) : C.arc k ⊆ C.carrier :=
  image_mono (arcSet_subset_K C.R k)

theorem image_arc (k : Fin C.R.N) : C.ζ '' C.arc k = C.R.arcSet k := by
  ext z
  constructor
  · rintro ⟨P, hP, rfl⟩
    rw [arc_eq] at hP
    exact hP.2
  · intro hz
    exact ⟨C.ζ.symm z, ⟨z, hz, rfl⟩, C.ζ.right_inv (arcSet_subset_target C k hz)⟩

theorem arc_nonempty (k : Fin C.R.N) : (C.arc k).Nonempty :=
  (arcSet_nonempty C.R k).image _

theorem isPreconnected_arc (k : Fin C.R.N) : IsPreconnected (C.arc k) :=
  (isPreconnected_arcSet C.R k).image _ (C.ζ.continuousOn_symm.mono (arcSet_subset_target C k))

theorem bdry_mem_arc {k : Fin C.R.N} {φ : ℝ} (hφ : φ ∈ C.R.arcIcc k) : C.bdry φ ∈ C.arc k :=
  ⟨C.R.loop φ, ⟨φ, hφ, rfl⟩, rfl⟩

end CellSide
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.AssemblyData P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily"

end CellFacts
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.AssemblyData P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily"

end Part_D1PairKit
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.AssemblyData P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily"

section Part_D1Fibre

noncomputable section

namespace FibreDegree
p2m_open "AlgebraicCurve~H1 Polynomial"

variable {F : Type*} [Field F] [Algebra ℂ F]
variable (x : F)

def fib (b : ℂ) : Set (Place ℂ F) := {w | x ∈ w.toValuationSubring ∧ Place.evalAt w x = b}

def poles : Set (Place ℂ F) := {w | x ∉ w.toValuationSubring}

noncomputable def eFin (w : Place ℂ F) (b : ℂ) : ℕ := (w.ord (x - algebraMap ℂ F b)).toNat

noncomputable def eInf (w : Place ℂ F) : ℕ := (w.ord x⁻¹).toNat

noncomputable abbrev deg : ℕ := Module.finrank (IntermediateField.adjoin ℂ ({x} : Set F)) F

private theorem mem_fib_iff {w : Place ℂ F} {b : ℂ} :
    w ∈ fib x b ↔ x ∈ w.toValuationSubring ∧ Place.evalAt w x = b := Iff.rfl

private theorem mem_poles_iff {w : Place ℂ F} : w ∈ poles x ↔ x ∉ w.toValuationSubring := Iff.rfl

private theorem _root_.FibreDegree.evalAt_sub_algebraMap (v : Place ℂ F) (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) (c : ℂ) :
    v.evalAt (f - algebraMap ℂ F c) = v.evalAt f - c := by
  have hcm : algebraMap ℂ F c ∈ v.toValuationSubring := v.algebraMap_mem' c
  have hmem : f - algebraMap ℂ F c ∈ v.toValuationSubring := sub_mem hf hcm
  apply v.algebraMap_residueField_injective
  rw [map_sub, v.algebraMap_evalAt hv hmem, v.algebraMap_evalAt hv hf]
  have hsub : (⟨f - algebraMap ℂ F c, hmem⟩ : v.toValuationSubring)
      = ⟨f, hf⟩ - ⟨algebraMap ℂ F c, hcm⟩ := rfl
  rw [hsub, map_sub]
  congr 1

p2m_export "FibreDegree" "evalAt_sub_algebraMap"
private theorem evalAt_eq_zero_of_ord_pos (v : Place ℂ F) {g : F} (hg : g ≠ 0)
    (h : 0 < v.ord g) : v.evalAt g = 0 := by
  have hmem : g ∈ v.toValuationSubring := v.mem_of_ord_nonneg hg h.le
  have hm : (⟨g, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := v.ord_coe_unit hu.unit
    simp only [IsUnit.unit_spec] at this
    omega
  rw [v.evalAt_of_mem hmem]
  have hres0 : IsLocalRing.residue v.toValuationSubring ⟨g, hmem⟩ = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hm
  rw [hres0]
  have := v.residueInv_algebraMap 0
  rwa [map_zero] at this

private theorem ord_pos_of_evalAt_eq_zero (v : Place ℂ F) (hv : v.IsRational) {g : F} (hg : g ≠ 0)
    (hmem : g ∈ v.toValuationSubring) (hz : v.evalAt g = 0) : 0 < v.ord g := by
  have h0 : 0 ≤ v.ord g := (v.mem_iff_ord_nonneg hg).mp hmem
  rcases h0.lt_or_eq with h | h
  · exact h
  · exact absurd hz (v.evalAt_ne_zero_of_ord_eq_zero hv hg h.symm)

private theorem isRational_of_finite {L : Type*} [Field L] [Algebra ℂ L] (v : Place ℂ L)
    (hfin : Module.Finite ℂ v.ResidueField) : v.IsRational := by
  haveI := hfin
  haveI : Algebra.IsIntegral ℂ v.ResidueField := Algebra.IsIntegral.of_finite ℂ v.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ) (K := v.ResidueField)).2

private theorem ne_zero_of_transcendental {g : F} (hg : Transcendental ℂ g) : g ≠ 0 := by
  intro h
  apply hg
  rw [h]
  exact isAlgebraic_zero

theorem sub_ne_zero (htr : Transcendental ℂ x) (b : ℂ) : x - algebraMap ℂ F b ≠ 0 :=
  fun h => htr (sub_eq_zero.mp h ▸ isAlgebraic_algebraMap b)

theorem inv_ne_zero (htr : Transcendental ℂ x) : x⁻¹ ≠ 0 :=
  _root_.inv_ne_zero (ne_zero_of_transcendental htr)

theorem sub_mem_of_mem_fib {w : Place ℂ F} {b : ℂ} (hw : w ∈ fib x b) :
    x - algebraMap ℂ F b ∈ w.toValuationSubring :=
  sub_mem ((mem_fib_iff x).mp hw).1 (w.algebraMap_mem' b)

private theorem ne_zero_of_mem_poles {w : Place ℂ F} (hw : w ∈ poles x) : x ≠ 0 := by
  intro h
  apply (mem_poles_iff x).mp hw
  rw [h]
  exact zero_mem _

private theorem ord_neg_of_mem_poles {w : Place ℂ F} (hw : w ∈ poles x) : w.ord x < 0 := by
  have hx0 : x ≠ 0 := ne_zero_of_mem_poles x hw
  by_contra h
  exact (mem_poles_iff x).mp hw ((w.mem_iff_ord_nonneg hx0).mpr (not_lt.mp h))

private theorem ord_inv_pos_of_mem_poles {w : Place ℂ F} (hw : w ∈ poles x) : 0 < w.ord x⁻¹ := by
  rw [w.ord_inv]
  have := ord_neg_of_mem_poles x hw
  omega

theorem evalAt_inv_of_mem_poles {w : Place ℂ F} (hw : w ∈ poles x) : Place.evalAt w x⁻¹ = 0 :=
  evalAt_eq_zero_of_ord_pos w (_root_.inv_ne_zero (ne_zero_of_mem_poles x hw))
    (ord_inv_pos_of_mem_poles x hw)

variable [IsCurveOver ℂ F]

private theorem place_isRational (w : Place ℂ F) : w.IsRational :=
  isRational_of_finite w (IsCurveOver.finiteResidue w)

theorem evalAt_sub_of_mem_fib {w : Place ℂ F} {b : ℂ} (hw : w ∈ fib x b) :
    Place.evalAt w (x - algebraMap ℂ F b) = 0 := by
  rw [evalAt_sub_algebraMap w (place_isRational w) ((mem_fib_iff x).mp hw).1,
    ((mem_fib_iff x).mp hw).2, sub_self]

theorem eFin_pos (htr : Transcendental ℂ x) {w : Place ℂ F} {b : ℂ} (hw : w ∈ fib x b) :
    0 < eFin x w b := by
  have hpos : 0 < w.ord (x - algebraMap ℂ F b) :=
    ord_pos_of_evalAt_eq_zero w (place_isRational w) (FibreDegree.sub_ne_zero x htr b)
      (sub_mem_of_mem_fib x hw) (evalAt_sub_of_mem_fib x hw)
  show 0 < (w.ord (x - algebraMap ℂ F b)).toNat
  omega

theorem sum_eFin (htr : Transcendental ℂ x)
    [FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F] (b : ℂ)
    (s : Finset (Place ℂ F))
    (hs : ∀ w, w ∈ s ↔ w ∈ fib x b) : ∑ w ∈ s, eFin x w b = deg x :=
  (AlgebraicCurve.Place.sum_fiber_ord_eq_finrank htr).1 b s hs

theorem sum_eInf (htr : Transcendental ℂ x)
    [FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F] (s : Finset (Place ℂ F))
    (hs : ∀ w, w ∈ s ↔ w ∈ poles x) : ∑ w ∈ s, eInf x w = deg x :=
  (AlgebraicCurve.Place.sum_fiber_ord_eq_finrank htr).2 s hs

theorem eFin_eq_one_of_card (htr : Transcendental ℂ x)
    [FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F] {b : ℂ}
    (s : Finset (Place ℂ F))
    (hs : ∀ w, w ∈ s ↔ w ∈ fib x b) (hcard : s.card = deg x) {w : Place ℂ F} (hw : w ∈ fib x b) :
    eFin x w b = 1 := by
  have hsum := sum_eFin x htr b s hs
  have hle : ∀ w ∈ s, (1 : ℕ) ≤ eFin x w b := fun w hw => eFin_pos x htr ((hs w).mp hw)
  have hall := (Finset.sum_eq_sum_iff_of_le hle).mp
    (by rw [hsum, ← hcard, Finset.card_eq_sum_ones])
  exact (hall w ((hs w).mpr hw)).symm

section RiemannHurwitz

variable [HasCanonicalDivisor (K := ℂ) (F := F)]

theorem rh_count (htr : Transcendental ℂ x)
    [FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F] (B : Finset ℂ)
    (hB : ∀ b w, w ∈ fib x b → eFin x w b ≠ 1 → b ∈ B)
    (t : ℂ → Finset (Place ℂ F)) (ht : ∀ b w, w ∈ t b ↔ w ∈ fib x b)
    (p : Finset (Place ℂ F)) (hp : ∀ w, w ∈ p ↔ w ∈ poles x) :
    (∑ b ∈ B, ∑ w ∈ t b, ((eFin x w b : ℤ) - 1)) + ∑ w ∈ p, ((eInf x w : ℤ) - 1)
      = 2 * (Module.finrank ℂ ↥(regularDifferentials ℂ F) : ℤ) - 2 + 2 * (deg x : ℤ) :=
  AlgebraicCurve.Place.sum_ramification_evalAt_eq htr B
    (fun b w hxw hev hne => hB b w ((mem_fib_iff x).mpr ⟨hxw, hev⟩) hne) t (fun b _ w => ht b w) p hp

end RiemannHurwitz
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.AssemblyData P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily"

end FibreDegree
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.AssemblyData P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.AssemblyData P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily"

end Part_D1Fibre
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.AssemblyData P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily"

section Part_D1Cap2

set_option autoImplicit false

p2m_open "AlgebraicCurve~H1 Set"
open scoped Manifold ContDiff Topology

namespace CentreChart

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

theorem analyticCoord_fields_of_center {v : Place ℂ F}
    (ζ : OpenPartialHomeomorph (Place ℂ F) ℂ)
    (hsub : ζ.source ⊆ (extChartAt 𝓘(ℂ, ℂ) v).source)
    (han : AnalyticOnNhd ℂ (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) v).symm)
      (extChartAt 𝓘(ℂ, ℂ) v '' ζ.source))
    (hder : ∀ z ∈ extChartAt 𝓘(ℂ, ℂ) v '' ζ.source,
      deriv (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) v).symm) z ≠ 0)
    (P : Place ℂ F) (hP : P ∈ ζ.source) :
    AnalyticAt ℂ (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) P).symm) (extChartAt 𝓘(ℂ, ℂ) P P) ∧
    deriv (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) P).symm) (extChartAt 𝓘(ℂ, ℂ) P P) ≠ 0 :=
  AlgebraicCurve.Place.analyticCoord_of_center (ζ := ζ) (hsub := hsub) (han := han) (hder := hder) (P := P) (hP := hP)

end CentreChart
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.AssemblyData P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily"

end Part_D1Cap2
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.AssemblyData P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily"

section Part_C0RegionB

set_option autoImplicit false

p2m_open "AlgebraicCurve~H1"
open scoped Manifold ContDiff

namespace PlaceCoordinate

p2m_open "AlgebraicCurve.Place"

theorem evalAt_sub_algebraMap {F : Type*} [Field F] [Algebra ℂ F]
    (v : Place ℂ F) (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) (c : ℂ) :
    v.evalAt (f - algebraMap ℂ F c) = v.evalAt f - c := by
  have hcm : algebraMap ℂ F c ∈ v.toValuationSubring := v.algebraMap_mem' c
  have hmem : f - algebraMap ℂ F c ∈ v.toValuationSubring := sub_mem hf hcm
  apply v.algebraMap_residueField_injective
  rw [map_sub, v.algebraMap_evalAt hv hmem, v.algebraMap_evalAt hv hf]
  have hsub : (⟨f - algebraMap ℂ F c, hmem⟩ : v.toValuationSubring)
      = ⟨f, hf⟩ - ⟨algebraMap ℂ F c, hcm⟩ := rfl
  rw [hsub, map_sub]
  congr 1

theorem analyticCoord_fields_of_agree {F : Type*} [Field F] [Algebra ℂ F]
    [IsCurveOver ℂ F] [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [T2Space (Place ℂ F)]
    (hF : ∀ g : F, g ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) g)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) g)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord g : WithTop ℤ))
    (hrat : ∀ P : Place ℂ F, P.IsRational)
    {f : F} (hf : Transcendental ℂ f)
    (ζ : OpenPartialHomeomorph (Place ℂ F) ℂ)
    (hread : ∀ Q ∈ ζ.source, ζ Q = Place.evalAt Q f)
    (P : Place ℂ F) (hP : P ∈ ζ.source)
    (hfP : f ∈ P.toValuationSubring)
    (hord : P.ord (f - algebraMap ℂ F (P.evalAt f)) = 1) :
    AnalyticAt ℂ (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) P).symm) (extChartAt 𝓘(ℂ, ℂ) P P) ∧
    deriv (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) P).symm) (extChartAt 𝓘(ℂ, ℂ) P P) ≠ 0 :=
  AlgebraicCurve.Place.analyticCoord_of_agree (hF := hF) (hrat := hrat) (hf := hf) (ζ := ζ) (hread := hread) (P := P) (hP := hP) (hfP := hfP) (hord := hord)

end PlaceCoordinate
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.AssemblyData P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily"

end Part_C0RegionB
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.AssemblyData P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily"

section Part_l3_cells

set_option autoImplicit false

p2m_open "AlgebraicCurve~H1 Set P2MW.S_AlgebraicCurve_exists_pairedCellFamily.DissectionMaterials P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily"
open scoped Manifold ContDiff Topology Real

namespace PlanarRegions

abbrev RectClauses (x₀ x₁ y₀ y₁ : ℝ) (p : ℂ) (yL : ℝ) (_hx₀ : x₀ < p.re) (_hx₁ : p.re < x₁) (_hy₀ : y₀ < p.im) (_hy₁ : p.im < y₁) (_hL₀ : y₀ < yL) (_hL₁ : yL < y₁) (R : RadialRegion) : Prop :=
  R.q = p ∧ R.N = 6 ∧
  R.K = {z : ℂ | z.re ∈ Icc x₀ x₁ ∧ z.im ∈ Icc y₀ y₁} ∧
  R.Kint = {z : ℂ | z.re ∈ Ioo x₀ x₁ ∧ z.im ∈ Ioo y₀ y₁} ∧
  (∀ k : Fin R.N, k.val = 0 → R.arcSet k = {z : ℂ | z.re = x₁ ∧ z.im ∈ Icc p.im y₁}) ∧
  (∀ k : Fin R.N, k.val = 1 → R.arcSet k = {z : ℂ | z.im = y₁ ∧ z.re ∈ Icc x₀ x₁}) ∧
  (∀ k : Fin R.N, k.val = 2 → R.arcSet k = {z : ℂ | z.re = x₀ ∧ z.im ∈ Icc yL y₁}) ∧
  (∀ k : Fin R.N, k.val = 3 → R.arcSet k = {z : ℂ | z.re = x₀ ∧ z.im ∈ Icc y₀ yL}) ∧
  (∀ k : Fin R.N, k.val = 4 → R.arcSet k = {z : ℂ | z.im = y₀ ∧ z.re ∈ Icc x₀ x₁}) ∧
  (∀ k : Fin R.N, k.val = 5 → R.arcSet k = {z : ℂ | z.re = x₁ ∧ z.im ∈ Icc y₀ p.im}) ∧
  (∀ k : Fin (R.N + 1), k.val = 0 → R.loop (R.φs k) = ⟨x₁, p.im⟩) ∧
  (∀ k : Fin (R.N + 1), k.val = 1 → R.loop (R.φs k) = ⟨x₁, y₁⟩) ∧
  (∀ k : Fin (R.N + 1), k.val = 2 → R.loop (R.φs k) = ⟨x₀, y₁⟩) ∧
  (∀ k : Fin (R.N + 1), k.val = 3 → R.loop (R.φs k) = ⟨x₀, yL⟩) ∧
  (∀ k : Fin (R.N + 1), k.val = 4 → R.loop (R.φs k) = ⟨x₀, y₀⟩) ∧
  (∀ k : Fin (R.N + 1), k.val = 5 → R.loop (R.φs k) = ⟨x₁, y₀⟩) ∧
  (∀ k : Fin (R.N + 1), k.val = 6 → R.loop (R.φs k) = ⟨x₁, p.im⟩) ∧
  (∀ k : Fin R.N, k.val = 0 ∨ k.val = 5 →
  (∀ t ∈ R.arcIcc k, R.r t = (Real.cos t / (x₁ - p.re))⁻¹)) ∧
  (∀ k : Fin R.N, k.val = 1 → ∀ t ∈ R.arcIcc k, R.r t = (Real.sin t / (y₁ - p.im))⁻¹) ∧
  (∀ k : Fin R.N, k.val = 2 ∨ k.val = 3 →
  (∀ t ∈ R.arcIcc k, R.r t = (-Real.cos t / (p.re - x₀))⁻¹)) ∧
  (∀ k : Fin R.N, k.val = 4 → ∀ t ∈ R.arcIcc k, R.r t = (-Real.sin t / (p.im - y₀))⁻¹) ∧
  (∀ k : Fin R.N, k.val = 0 → R.arcIcc k ⊆ Ico 0 (π / 2)) ∧
  (∀ k : Fin R.N, k.val = 1 → R.arcIcc k ⊆ Ioo 0 π) ∧
  (∀ k : Fin R.N, k.val = 2 ∨ k.val = 3 → R.arcIcc k ⊆ Ioo (π / 2) (3 * π / 2)) ∧
  (∀ k : Fin R.N, k.val = 4 → R.arcIcc k ⊆ Ioo π (2 * π)) ∧
  (∀ k : Fin R.N, k.val = 5 → R.arcIcc k ⊆ Ioc (3 * π / 2) (2 * π)) ∧
  (∀ z ∈ R.K, z ∉ R.Kint →
  R.loop (if Complex.arg (z - p) < 0 then Complex.arg (z - p) + 2 * π else Complex.arg (z - p))
  = z) ∧
  (∀ (k : Fin R.N) (t₁ t₂ : ℝ), t₁ ∈ R.arcIcc k → t₂ ∈ R.arcIcc k → t₁ ≤ t₂ →
  R.loop '' Icc t₁ t₂ = segment ℝ (R.loop t₁) (R.loop t₂))

abbrev WindowClauses (o hm : ℝ) (_hhm : 0 < hm) (jlo jhi klo khi : ℤ) (_hj : jlo ≤ jhi) (_hk : klo ≤ khi) (cy : ℤ × ℤ → ℝ) (_hcy : ∀ p : ℤ × ℤ, o + p.2 * hm < cy p ∧ cy p < o + (p.2 + 1) * hm) (_hx₀ : o + jlo * hm < 0) (_hx₁ : 0 < o + (jhi + 1) * hm) (_hy₀ : o + klo * hm < 0) (_hy₁ : 0 < o + (khi + 1) * hm) (_hcy0 : ∀ k : ℤ, o + k * hm < 0 → 0 < o + (k + 1) * hm → cy (jhi, k) = 0) (R : RadialRegion) : Prop :=
  R.q = 0 ∧
  R.K = {z : ℂ | z.re ∈ Icc (o + jlo * hm) (o + (jhi + 1) * hm) ∧
  z.im ∈ Icc (o + klo * hm) (o + (khi + 1) * hm)} ∧
  R.Kint = {z : ℂ | z.re ∈ Ioo (o + jlo * hm) (o + (jhi + 1) * hm) ∧
  z.im ∈ Ioo (o + klo * hm) (o + (khi + 1) * hm)} ∧
  R.N = 2 * (jhi - jlo + 1).toNat + 4 * (khi - klo + 1).toNat ∧
  (∀ k k' : Fin R.N, R.arcSet k = R.arcSet k' → k = k') ∧
  (∀ k : Fin R.N,
  (∃ j : ℤ, jlo ≤ j ∧ j ≤ jhi ∧
  R.arcSet k = {z : ℂ | z.im = o + klo * hm ∧ z.re ∈ Icc (o + j * hm) (o + (j + 1) * hm)} ∧
  R.loop (R.φs k.castSucc) = ⟨o + j * hm, o + klo * hm⟩ ∧
  R.loop (R.φs k.succ) = ⟨o + (j + 1) * hm, o + klo * hm⟩ ∧
  (∀ t ∈ R.arcIcc k, R.r t = (-Real.sin t / (-(o + klo * hm)))⁻¹) ∧
  R.arcIcc k ⊆ Ioo π (2 * π)) ∨
  (∃ j : ℤ, jlo ≤ j ∧ j ≤ jhi ∧
  R.arcSet k = {z : ℂ | z.im = o + (khi + 1) * hm ∧
  z.re ∈ Icc (o + j * hm) (o + (j + 1) * hm)} ∧
  R.loop (R.φs k.castSucc) = ⟨o + (j + 1) * hm, o + (khi + 1) * hm⟩ ∧
  R.loop (R.φs k.succ) = ⟨o + j * hm, o + (khi + 1) * hm⟩ ∧
  (∀ t ∈ R.arcIcc k, R.r t = (Real.sin t / (o + (khi + 1) * hm))⁻¹) ∧
  R.arcIcc k ⊆ Ioo 0 π) ∨
  (∃ k₀ : ℤ, klo ≤ k₀ ∧ k₀ ≤ khi ∧
  R.arcSet k = {z : ℂ | z.re = o + jlo * hm ∧ z.im ∈ Icc (cy (jlo, k₀)) (o + (k₀ + 1) * hm)} ∧
  R.loop (R.φs k.castSucc) = ⟨o + jlo * hm, o + (k₀ + 1) * hm⟩ ∧
  R.loop (R.φs k.succ) = ⟨o + jlo * hm, cy (jlo, k₀)⟩ ∧
  (∀ t ∈ R.arcIcc k, R.r t = (-Real.cos t / (-(o + jlo * hm)))⁻¹) ∧
  R.arcIcc k ⊆ Ioo (π / 2) (3 * π / 2)) ∨
  (∃ k₀ : ℤ, klo ≤ k₀ ∧ k₀ ≤ khi ∧
  R.arcSet k = {z : ℂ | z.re = o + jlo * hm ∧ z.im ∈ Icc (o + k₀ * hm) (cy (jlo, k₀))} ∧
  R.loop (R.φs k.castSucc) = ⟨o + jlo * hm, cy (jlo, k₀)⟩ ∧
  R.loop (R.φs k.succ) = ⟨o + jlo * hm, o + k₀ * hm⟩ ∧
  (∀ t ∈ R.arcIcc k, R.r t = (-Real.cos t / (-(o + jlo * hm)))⁻¹) ∧
  R.arcIcc k ⊆ Ioo (π / 2) (3 * π / 2)) ∨
  (∃ k₀ : ℤ, klo ≤ k₀ ∧ k₀ ≤ khi ∧
  R.arcSet k = {z : ℂ | z.re = o + (jhi + 1) * hm ∧ z.im ∈ Icc (o + k₀ * hm) (cy (jhi, k₀))} ∧
  R.loop (R.φs k.castSucc) = ⟨o + (jhi + 1) * hm, o + k₀ * hm⟩ ∧
  R.loop (R.φs k.succ) = ⟨o + (jhi + 1) * hm, cy (jhi, k₀)⟩ ∧
  (∀ t ∈ R.arcIcc k, R.r t = (Real.cos t / (o + (jhi + 1) * hm))⁻¹) ∧
  (R.arcIcc k ⊆ Ioo (-(π / 2)) (π / 2) ∨ R.arcIcc k ⊆ Ioo (3 * π / 2) (5 * π / 2))) ∨
  (∃ k₀ : ℤ, klo ≤ k₀ ∧ k₀ ≤ khi ∧
  R.arcSet k = {z : ℂ | z.re = o + (jhi + 1) * hm ∧
  z.im ∈ Icc (cy (jhi, k₀)) (o + (k₀ + 1) * hm)} ∧
  R.loop (R.φs k.castSucc) = ⟨o + (jhi + 1) * hm, cy (jhi, k₀)⟩ ∧
  R.loop (R.φs k.succ) = ⟨o + (jhi + 1) * hm, o + (k₀ + 1) * hm⟩ ∧
  (∀ t ∈ R.arcIcc k, R.r t = (Real.cos t / (o + (jhi + 1) * hm))⁻¹) ∧
  (R.arcIcc k ⊆ Ioo (-(π / 2)) (π / 2) ∨ R.arcIcc k ⊆ Ioo (3 * π / 2) (5 * π / 2)))) ∧
  (∀ j : ℤ, jlo ≤ j → j ≤ jhi → ∃ k : Fin R.N,
  R.arcSet k = {z : ℂ | z.im = o + klo * hm ∧ z.re ∈ Icc (o + j * hm) (o + (j + 1) * hm)}) ∧
  (∀ j : ℤ, jlo ≤ j → j ≤ jhi → ∃ k : Fin R.N,
  R.arcSet k = {z : ℂ | z.im = o + (khi + 1) * hm ∧ z.re ∈ Icc (o + j * hm) (o + (j + 1) * hm)}) ∧
  (∀ k₀ : ℤ, klo ≤ k₀ → k₀ ≤ khi → ∃ k : Fin R.N,
  R.arcSet k = {z : ℂ | z.re = o + jlo * hm ∧ z.im ∈ Icc (cy (jlo, k₀)) (o + (k₀ + 1) * hm)}) ∧
  (∀ k₀ : ℤ, klo ≤ k₀ → k₀ ≤ khi → ∃ k : Fin R.N,
  R.arcSet k = {z : ℂ | z.re = o + jlo * hm ∧ z.im ∈ Icc (o + k₀ * hm) (cy (jlo, k₀))}) ∧
  (∀ k₀ : ℤ, klo ≤ k₀ → k₀ ≤ khi → ∃ k : Fin R.N,
  R.arcSet k = {z : ℂ | z.re = o + (jhi + 1) * hm ∧ z.im ∈ Icc (o + k₀ * hm) (cy (jhi, k₀))}) ∧
  (∀ k₀ : ℤ, klo ≤ k₀ → k₀ ≤ khi → ∃ k : Fin R.N,
  R.arcSet k = {z : ℂ | z.re = o + (jhi + 1) * hm ∧
  z.im ∈ Icc (cy (jhi, k₀)) (o + (k₀ + 1) * hm)})

abbrev RecipClauses (R : RadialRegion) (_hq : R.q = 0) (R' : RadialRegion) : Prop :=
  R'.q = 0 ∧ R'.N = R.N ∧ (0 : ℂ) ∈ R'.Kint ∧
  (∀ w : ℂ, w ≠ 0 → (w ∈ R'.K ↔ w⁻¹ ∉ R.Kint)) ∧
  (∀ w : ℂ, w ≠ 0 → (w ∈ R'.Kint ↔ w⁻¹ ∉ R.K)) ∧
  (∀ θ : ℝ, R'.loop θ = (R.loop (2 * π - θ))⁻¹)

abbrev RecipIdxClauses (R : RadialRegion) (_hq : R.q = 0) (R' : RadialRegion) (σ : Fin R.N ≃ Fin R'.N) : Prop :=
  (∀ k : Fin R.N, R'.arcIcc (σ k) = (fun t : ℝ => 2 * π - t) '' R.arcIcc k) ∧
  (∀ k : Fin R.N, (fun w : ℂ => w⁻¹) '' R'.arcSet (σ k) = R.arcSet k)

abbrev EfoldClauses (R : RadialRegion) (_hN : 2 ≤ R.N) (e : ℕ) (_he : e ≠ 0) (R' : RadialRegion) : Prop :=
  R'.q = 0 ∧ R'.N = e * R.N ∧
  (∀ u : ℂ, u ∈ R'.K ↔ R.q + u ^ e ∈ R.K) ∧
  (∀ u : ℂ, u ∈ R'.Kint ↔ R.q + u ^ e ∈ R.Kint) ∧
  (∀ ψ : ℝ, R.q + R'.loop ψ ^ e = R.loop ((e : ℝ) * ψ))

abbrev LapClauses (R : RadialRegion) (_hN : 2 ≤ R.N) (e : ℕ) (_he : e ≠ 0) (R' : RadialRegion) (lap : Fin e → Fin R.N → Fin R'.N) : Prop :=
  Function.Bijective (fun jk : Fin e × Fin R.N => lap jk.1 jk.2) ∧
  (∀ (j : Fin e) (k : Fin R.N),
  R'.arcIcc (lap j k) = (fun t : ℝ => (2 * π * ((j : ℕ) : ℝ) + t) / (e : ℝ)) '' R.arcIcc k) ∧
  (∀ (j : Fin e) (k : Fin R.N),
  (fun u : ℂ => R.q + u ^ e) '' R'.arcSet (lap j k) = R.arcSet k) ∧
  (∀ (j : Fin e) (k : Fin R.N), Set.InjOn (fun u : ℂ => R.q + u ^ e) (R'.arcSet (lap j k))) ∧
  (∀ k : Fin R.N, ∃ U : Fin e → Set ℂ, (∀ j, IsOpen (U j)) ∧
  Pairwise (fun j j' => Disjoint (U j) (U j')) ∧ ∀ j, R'.arcSet (lap j k) ⊆ U j)

class Planar where

  rect : ∀ (x₀ x₁ y₀ y₁ : ℝ) (p : ℂ) (yL : ℝ) (_hx₀ : x₀ < p.re) (_hx₁ : p.re < x₁) (_hy₀ : y₀ < p.im) (_hy₁ : p.im < y₁) (_hL₀ : y₀ < yL) (_hL₁ : yL < y₁), RadialRegion
  rect_spec : ∀ (x₀ x₁ y₀ y₁ : ℝ) (p : ℂ) (yL : ℝ) (hx₀ : x₀ < p.re) (hx₁ : p.re < x₁) (hy₀ : y₀ < p.im) (hy₁ : p.im < y₁) (hL₀ : y₀ < yL) (hL₁ : yL < y₁), RectClauses x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁ (rect x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁)

  window : ∀ (o hm : ℝ) (_hhm : 0 < hm) (jlo jhi klo khi : ℤ) (_hj : jlo ≤ jhi) (_hk : klo ≤ khi) (cy : ℤ × ℤ → ℝ) (_hcy : ∀ p : ℤ × ℤ, o + p.2 * hm < cy p ∧ cy p < o + (p.2 + 1) * hm) (_hx₀ : o + jlo * hm < 0) (_hx₁ : 0 < o + (jhi + 1) * hm) (_hy₀ : o + klo * hm < 0) (_hy₁ : 0 < o + (khi + 1) * hm) (_hcy0 : ∀ k : ℤ, o + k * hm < 0 → 0 < o + (k + 1) * hm → cy (jhi, k) = 0), RadialRegion
  window_spec : ∀ (o hm : ℝ) (hhm : 0 < hm) (jlo jhi klo khi : ℤ) (hj : jlo ≤ jhi) (hk : klo ≤ khi) (cy : ℤ × ℤ → ℝ) (hcy : ∀ p : ℤ × ℤ, o + p.2 * hm < cy p ∧ cy p < o + (p.2 + 1) * hm) (hx₀ : o + jlo * hm < 0) (hx₁ : 0 < o + (jhi + 1) * hm) (hy₀ : o + klo * hm < 0) (hy₁ : 0 < o + (khi + 1) * hm) (hcy0 : ∀ k : ℤ, o + k * hm < 0 → 0 < o + (k + 1) * hm → cy (jhi, k) = 0), WindowClauses o hm hhm jlo jhi klo khi hj hk cy hcy hx₀ hx₁ hy₀ hy₁ hcy0 (window o hm hhm jlo jhi klo khi hj hk cy hcy hx₀ hx₁ hy₀ hy₁ hcy0)

  recip : ∀ (R : RadialRegion) (_hq : R.q = 0), RadialRegion
  recip_spec : ∀ (R : RadialRegion) (hq : R.q = 0), RecipClauses R hq (recip R hq)

  recipIdx : ∀ (R : RadialRegion) (hq : R.q = 0), Fin R.N ≃ Fin (recip R hq).N
  recipIdx_spec : ∀ (R : RadialRegion) (hq : R.q = 0), RecipIdxClauses R hq (recip R hq) (recipIdx R hq)

  efold : ∀ (R : RadialRegion) (_hN : 2 ≤ R.N) (e : ℕ) (_he : e ≠ 0), RadialRegion
  efold_spec : ∀ (R : RadialRegion) (hN : 2 ≤ R.N) (e : ℕ) (he : e ≠ 0), EfoldClauses R hN e he (efold R hN e he)

  lap : ∀ (R : RadialRegion) (hN : 2 ≤ R.N) (e : ℕ) (he : e ≠ 0), Fin e → Fin R.N → Fin (efold R hN e he).N
  lap_spec : ∀ (R : RadialRegion) (hN : 2 ≤ R.N) (e : ℕ) (he : e ≠ 0), LapClauses R hN e he (efold R hN e he) (lap R hN e he)

  across :
    (∀ (R R' : RadialRegion) (k : Fin R.N) (k' : Fin R'.N) (a b : ℝ), 0 < a → 0 < b →
    R.q.re + a = R'.q.re - b →
    (∀ t ∈ R.arcIcc k, R.r t = (Real.cos t / a)⁻¹) →
    (R.arcIcc k ⊆ Ioo (-(π / 2)) (π / 2) ∨ R.arcIcc k ⊆ Ioo (3 * π / 2) (5 * π / 2)) →
    (∀ t ∈ R'.arcIcc k', R'.r t = (-Real.cos t / b)⁻¹) →
    R'.arcIcc k' ⊆ Ioo (π / 2) (3 * π / 2) →
    R.loop (R.φs k.castSucc) = R'.loop (R'.φs k'.succ) →
    R.loop (R.φs k.succ) = R'.loop (R'.φs k'.castSucc) →
    ∃ ψ : ℝ → ℝ, StrictAntiOn ψ (R'.arcIcc k') ∧ ContDiffOn ℝ 1 ψ (R'.arcIcc k') ∧
    ψ (R'.φs k'.castSucc) = R.φs k.succ ∧ ψ (R'.φs k'.succ) = R.φs k.castSucc ∧
    ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t)) ∧
    (∀ (R R' : RadialRegion) (k : Fin R.N) (k' : Fin R'.N) (c d : ℝ), 0 < c → 0 < d →
    R.q.im + c = R'.q.im - d →
    (∀ t ∈ R.arcIcc k, R.r t = (Real.sin t / c)⁻¹) → R.arcIcc k ⊆ Ioo 0 π →
    (∀ t ∈ R'.arcIcc k', R'.r t = (-Real.sin t / d)⁻¹) → R'.arcIcc k' ⊆ Ioo π (2 * π) →
    R.loop (R.φs k.castSucc) = R'.loop (R'.φs k'.succ) →
    R.loop (R.φs k.succ) = R'.loop (R'.φs k'.castSucc) →
    ∃ ψ : ℝ → ℝ, StrictAntiOn ψ (R'.arcIcc k') ∧ ContDiffOn ℝ 1 ψ (R'.arcIcc k') ∧
    ψ (R'.φs k'.castSucc) = R.φs k.succ ∧ ψ (R'.φs k'.succ) = R.φs k.castSucc ∧
    ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t))

  same :
    (∀ (R R' : RadialRegion) (k : Fin R.N) (k' : Fin R'.N) (a a' : ℝ), 0 < a → 0 < a' →
    R.q.re + a = R'.q.re + a' →
    (∀ t ∈ R.arcIcc k, R.r t = (Real.cos t / a)⁻¹) →
    (R.arcIcc k ⊆ Ioo (-(π / 2)) (π / 2) ∨ R.arcIcc k ⊆ Ioo (3 * π / 2) (5 * π / 2)) →
    (∀ t ∈ R'.arcIcc k', R'.r t = (Real.cos t / a')⁻¹) →
    (R'.arcIcc k' ⊆ Ioo (-(π / 2)) (π / 2) ∨ R'.arcIcc k' ⊆ Ioo (3 * π / 2) (5 * π / 2)) →
    R.loop (R.φs k.castSucc) = R'.loop (R'.φs k'.castSucc) →
    R.loop (R.φs k.succ) = R'.loop (R'.φs k'.succ) →
    ∃ ψ : ℝ → ℝ, StrictMonoOn ψ (R'.arcIcc k') ∧ ContDiffOn ℝ 1 ψ (R'.arcIcc k') ∧
    ψ (R'.φs k'.castSucc) = R.φs k.castSucc ∧ ψ (R'.φs k'.succ) = R.φs k.succ ∧
    ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t)) ∧
    (∀ (R R' : RadialRegion) (k : Fin R.N) (k' : Fin R'.N) (b b' : ℝ), 0 < b → 0 < b' →
    R.q.re - b = R'.q.re - b' →
    (∀ t ∈ R.arcIcc k, R.r t = (-Real.cos t / b)⁻¹) → R.arcIcc k ⊆ Ioo (π / 2) (3 * π / 2) →
    (∀ t ∈ R'.arcIcc k', R'.r t = (-Real.cos t / b')⁻¹) → R'.arcIcc k' ⊆ Ioo (π / 2) (3 * π / 2) →
    R.loop (R.φs k.castSucc) = R'.loop (R'.φs k'.castSucc) →
    R.loop (R.φs k.succ) = R'.loop (R'.φs k'.succ) →
    ∃ ψ : ℝ → ℝ, StrictMonoOn ψ (R'.arcIcc k') ∧ ContDiffOn ℝ 1 ψ (R'.arcIcc k') ∧
    ψ (R'.φs k'.castSucc) = R.φs k.castSucc ∧ ψ (R'.φs k'.succ) = R.φs k.succ ∧
    ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t)) ∧
    (∀ (R R' : RadialRegion) (k : Fin R.N) (k' : Fin R'.N) (c c' : ℝ), 0 < c → 0 < c' →
    R.q.im + c = R'.q.im + c' →
    (∀ t ∈ R.arcIcc k, R.r t = (Real.sin t / c)⁻¹) → R.arcIcc k ⊆ Ioo 0 π →
    (∀ t ∈ R'.arcIcc k', R'.r t = (Real.sin t / c')⁻¹) → R'.arcIcc k' ⊆ Ioo 0 π →
    R.loop (R.φs k.castSucc) = R'.loop (R'.φs k'.castSucc) →
    R.loop (R.φs k.succ) = R'.loop (R'.φs k'.succ) →
    ∃ ψ : ℝ → ℝ, StrictMonoOn ψ (R'.arcIcc k') ∧ ContDiffOn ℝ 1 ψ (R'.arcIcc k') ∧
    ψ (R'.φs k'.castSucc) = R.φs k.castSucc ∧ ψ (R'.φs k'.succ) = R.φs k.succ ∧
    ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t)) ∧
    (∀ (R R' : RadialRegion) (k : Fin R.N) (k' : Fin R'.N) (d d' : ℝ), 0 < d → 0 < d' →
    R.q.im - d = R'.q.im - d' →
    (∀ t ∈ R.arcIcc k, R.r t = (-Real.sin t / d)⁻¹) → R.arcIcc k ⊆ Ioo π (2 * π) →
    (∀ t ∈ R'.arcIcc k', R'.r t = (-Real.sin t / d')⁻¹) → R'.arcIcc k' ⊆ Ioo π (2 * π) →
    R.loop (R.φs k.castSucc) = R'.loop (R'.φs k'.castSucc) →
    R.loop (R.φs k.succ) = R'.loop (R'.φs k'.succ) →
    ∃ ψ : ℝ → ℝ, StrictMonoOn ψ (R'.arcIcc k') ∧ ContDiffOn ℝ 1 ψ (R'.arcIcc k') ∧
    ψ (R'.φs k'.castSucc) = R.φs k.castSucc ∧ ψ (R'.φs k'.succ) = R.φs k.succ ∧
    ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t))

end PlanarRegions
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.AssemblyData P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily"

open PlanarRegions

namespace DissectionMaterials
namespace Materials

abbrev OrdPack (F : Type*) [Field F] [Algebra ℂ F] [TopologicalSpace (Place ℂ F)]
    [ChartedSpace ℂ (Place ℂ F)] : Prop :=
  ∀ g : F, g ≠ 0 → ∀ v : Place ℂ F,
    MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) g)
        (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) g)
        (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord g : WithTop ℤ)

variable {F : Type*} [Field F] [Algebra ℂ F] [TopologicalSpace (Place ℂ F)]
variable [ChartedSpace ℂ (Place ℂ F)]
variable {S : Finset (Place ℂ F)} {P₀ : Place ℂ F}
variable (M : Materials F S P₀)

def sx (p : ℤ × ℤ) : ℝ := M.o + p.1 * M.hm
def sx' (p : ℤ × ℤ) : ℝ := M.o + (p.1 + 1) * M.hm
def sy (p : ℤ × ℤ) : ℝ := M.o + p.2 * M.hm
def sy' (p : ℤ × ℤ) : ℝ := M.o + (p.2 + 1) * M.hm

theorem gridSquare_eq (p : ℤ × ℤ) :
    PlaneGrid.gridSquare M.o M.hm p.1 p.2 =
      {z : ℂ | z.re ∈ Icc (M.sx p) (M.sx' p) ∧ z.im ∈ Icc (M.sy p) (M.sy' p)} := rfl

def ctr (p : ℤ × ℤ) : ℂ := (M.capAt p).getD (M.centre p)

theorem bad_mem_of_capAt {p : ℤ × ℤ} {b : ℂ} (h : M.capAt p = some b) :
    (M.sx p < b.re ∧ b.re < M.sx' p) ∧ (M.sy p < b.im ∧ b.im < M.sy' p) := by
  obtain ⟨hb, hre, him⟩ := (M.hcap p b).mp h
  have hoff := M.hbad_off b hb
  have hhm := M.hhm
  have hre' := Int.floor_eq_iff.mp hre
  have him' := Int.floor_eq_iff.mp him
  rw [le_div_iff₀ hhm] at hre' him'
  rw [div_lt_iff₀ hhm] at hre' him'
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · exact lt_of_le_of_ne (by unfold sx; linarith [hre'.1]) fun heq => (hoff p.1).1 (by unfold sx at heq; linarith)
  · unfold sx'; linarith [hre'.2]
  · exact lt_of_le_of_ne (by unfold sy; linarith [him'.1]) fun heq => (hoff p.2).2 (by unfold sy at heq; linarith)
  · unfold sy'; linarith [him'.2]

theorem ctr_mem (p : ℤ × ℤ) :
    (M.sx p < (M.ctr p).re ∧ (M.ctr p).re < M.sx' p) ∧
      (M.sy p < (M.ctr p).im ∧ (M.ctr p).im < M.sy' p) := by
  unfold ctr
  cases h : M.capAt p with
  | none =>
      simp only [Option.getD_none]
      exact M.hcentre p
  | some b =>
      simp only [Option.getD_some]
      exact M.bad_mem_of_capAt h

def yL (p : ℤ × ℤ) : ℝ := if p.1 = M.jlo then (M.ctr p).im else (M.ctr (p.1 - 1, p.2)).im

theorem yL_mem (p : ℤ × ℤ) : M.sy p < M.yL p ∧ M.yL p < M.sy' p := by
  unfold yL
  split_ifs
  · exact (M.ctr_mem p).2
  · have h := (M.ctr_mem (p.1 - 1, p.2)).2
    exact h

variable [Planar]

noncomputable def base (p : ℤ × ℤ) : RadialRegion :=
  Planar.rect (M.sx p) (M.sx' p) (M.sy p) (M.sy' p) (M.ctr p) (M.yL p)
    (M.ctr_mem p).1.1 (M.ctr_mem p).1.2 (M.ctr_mem p).2.1 (M.ctr_mem p).2.2
    (M.yL_mem p).1 (M.yL_mem p).2

theorem base_spec (p : ℤ × ℤ) :
    RectClauses (M.sx p) (M.sx' p) (M.sy p) (M.sy' p) (M.ctr p) (M.yL p)
      (M.ctr_mem p).1.1 (M.ctr_mem p).1.2 (M.ctr_mem p).2.1 (M.ctr_mem p).2.2
      (M.yL_mem p).1 (M.yL_mem p).2 (M.base p) :=
  Planar.rect_spec ..

theorem base_q (p : ℤ × ℤ) : (M.base p).q = M.ctr p := (M.base_spec p).1
theorem base_N (p : ℤ × ℤ) : (M.base p).N = 6 := (M.base_spec p).2.1
theorem base_K (p : ℤ × ℤ) : (M.base p).K = PlaneGrid.gridSquare M.o M.hm p.1 p.2 :=
  (M.base_spec p).2.2.1
theorem base_Kint (p : ℤ × ℤ) :
    (M.base p).Kint = {z : ℂ | z.re ∈ Ioo (M.sx p) (M.sx' p) ∧ z.im ∈ Ioo (M.sy p) (M.sy' p)} :=
  (M.base_spec p).2.2.2.1
theorem two_le_base_N (p : ℤ × ℤ) : 2 ≤ (M.base p).N := by rw [base_N]; norm_num

omit [Planar] in

theorem norm_sub_le_of_mem_gridSquare {p : ℤ × ℤ} {z w : ℂ}
    (hz : z ∈ PlaneGrid.gridSquare M.o M.hm p.1 p.2) (hw : w ∈ PlaneGrid.gridSquare M.o M.hm p.1 p.2) :
    ‖z - w‖ ≤ 2 * M.hm := by
  rw [gridSquare_eq] at hz hw
  have h1 : |z.re - w.re| ≤ M.hm := by
    rw [abs_le]
    unfold sx sx' at hz hw
    constructor <;> linarith [hz.1.1, hz.1.2, hw.1.1, hw.1.2]
  have h2 : |z.im - w.im| ≤ M.hm := by
    rw [abs_le]
    unfold sy sy' at hz hw
    constructor <;> linarith [hz.2.1, hz.2.2, hw.2.1, hw.2.2]
  calc ‖z - w‖ ≤ |(z - w).re| + |(z - w).im| := Complex.norm_le_abs_re_add_abs_im _
    _ = |z.re - w.re| + |z.im - w.im| := by simp [Complex.sub_re, Complex.sub_im]
    _ ≤ 2 * M.hm := by linarith

omit [Planar] in
theorem zero_mem_window :
    (M.sx (M.jlo, M.klo) < 0 ∧ 0 < M.sx' (M.jhi, M.khi)) ∧
      (M.sy (M.jlo, M.klo) < 0 ∧ 0 < M.sy' (M.jhi, M.khi)) := by
  have h := M.hwin 0 (by rw [norm_zero]; linarith [M.hRw])
  simp only [Complex.zero_re, Complex.zero_im] at h
  exact ⟨⟨h.1.1, h.1.2⟩, h.2.1, h.2.2⟩

def cy (p : ℤ × ℤ) : ℝ := (M.ctr p).im

omit [Planar] in
theorem cy_mem (p : ℤ × ℤ) : M.o + p.2 * M.hm < M.cy p ∧ M.cy p < M.o + (p.2 + 1) * M.hm :=
  (M.ctr_mem p).2

omit [Planar] in

theorem ctr_of_perim {p : ℤ × ℤ} (hp : p.1 = M.jlo ∨ p.1 = M.jhi ∨ p.2 = M.klo ∨ p.2 = M.khi) :
    M.ctr p = M.centre p := by
  simp [ctr, M.hperim_plain p hp]

omit [Planar] in
theorem cy_zero : ∀ k : ℤ, M.o + k * M.hm < 0 → 0 < M.o + (k + 1) * M.hm → M.cy (M.jhi, k) = 0 := by
  intro k h1 h2
  unfold cy
  rw [M.ctr_of_perim (p := (M.jhi, k)) (Or.inr (Or.inl rfl))]
  exact M.hcentre0 (M.jhi, k) rfl h1 h2

omit [Planar] in
theorem jlo_le_jhi : M.jlo ≤ M.jhi := by have := M.hjlt; omega
omit [Planar] in
theorem klo_le_khi : M.klo ≤ M.khi := by have := M.hklt; omega

noncomputable def winReg : RadialRegion :=
  Planar.window M.o M.hm M.hhm M.jlo M.jhi M.klo M.khi M.jlo_le_jhi M.klo_le_khi M.cy M.cy_mem
    M.zero_mem_window.1.1 M.zero_mem_window.1.2 M.zero_mem_window.2.1 M.zero_mem_window.2.2
    M.cy_zero

theorem winReg_spec :
    WindowClauses M.o M.hm M.hhm M.jlo M.jhi M.klo M.khi M.jlo_le_jhi M.klo_le_khi M.cy M.cy_mem
      M.zero_mem_window.1.1 M.zero_mem_window.1.2 M.zero_mem_window.2.1 M.zero_mem_window.2.2
      M.cy_zero M.winReg :=
  Planar.window_spec ..

theorem winReg_q : M.winReg.q = 0 := M.winReg_spec.1
theorem winReg_K : M.winReg.K =
    {z : ℂ | z.re ∈ Icc (M.sx (M.jlo, M.klo)) (M.sx' (M.jhi, M.khi)) ∧
      z.im ∈ Icc (M.sy (M.jlo, M.klo)) (M.sy' (M.jhi, M.khi))} := M.winReg_spec.2.1
theorem winReg_Kint : M.winReg.Kint =
    {z : ℂ | z.re ∈ Ioo (M.sx (M.jlo, M.klo)) (M.sx' (M.jhi, M.khi)) ∧
      z.im ∈ Ioo (M.sy (M.jlo, M.klo)) (M.sy' (M.jhi, M.khi))} := M.winReg_spec.2.2.1
theorem winReg_N :
    M.winReg.N = 2 * (M.jhi - M.jlo + 1).toNat + 4 * (M.khi - M.klo + 1).toNat :=
  M.winReg_spec.2.2.2.1
theorem two_le_winReg_N : 2 ≤ M.winReg.N := by
  rw [winReg_N]
  have := M.hjlt
  omega

theorem mem_winReg_Kint_of_norm_le {z : ℂ} (hz : ‖z‖ ≤ M.Rw) : z ∈ M.winReg.Kint := by
  rw [winReg_Kint]
  have h := M.hwin z hz
  exact ⟨⟨h.1.1, h.1.2⟩, h.2.1, h.2.2⟩

theorem hinner_Kint {z : ℂ} (hz : ‖z‖ < M.Rw) : z ∈ M.winReg.Kint :=
  M.mem_winReg_Kint_of_norm_le hz.le

theorem mem_winReg_K_of_norm_le {z : ℂ} (hz : ‖z‖ ≤ M.Rw) : z ∈ M.winReg.K := by
  rw [winReg_K]
  have h := M.hwin z hz
  exact ⟨⟨h.1.1.le, h.1.2.le⟩, h.2.1.le, h.2.2.le⟩

noncomputable def infBase : RadialRegion := Planar.recip M.winReg M.winReg_q

theorem infBase_spec : RecipClauses M.winReg M.winReg_q M.infBase := Planar.recip_spec ..

theorem infBase_q : M.infBase.q = 0 := M.infBase_spec.1
theorem infBase_N : M.infBase.N = M.winReg.N := M.infBase_spec.2.1
theorem zero_mem_infBase_Kint : (0 : ℂ) ∈ M.infBase.Kint := M.infBase_spec.2.2.1
theorem mem_infBase_K_iff {w : ℂ} (hw : w ≠ 0) : w ∈ M.infBase.K ↔ w⁻¹ ∉ M.winReg.Kint :=
  M.infBase_spec.2.2.2.1 w hw
theorem mem_infBase_Kint_iff {w : ℂ} (hw : w ≠ 0) : w ∈ M.infBase.Kint ↔ w⁻¹ ∉ M.winReg.K :=
  M.infBase_spec.2.2.2.2.1 w hw
theorem two_le_infBase_N : 2 ≤ M.infBase.N := by rw [infBase_N]; exact M.two_le_winReg_N

theorem efold_q (R : RadialRegion) (hN : 2 ≤ R.N) (e : ℕ) (he : e ≠ 0) :
    (Planar.efold R hN e he).q = 0 := (Planar.efold_spec R hN e he).1
theorem efold_N (R : RadialRegion) (hN : 2 ≤ R.N) (e : ℕ) (he : e ≠ 0) :
    (Planar.efold R hN e he).N = e * R.N := (Planar.efold_spec R hN e he).2.1
theorem efold_mem_K_iff (R : RadialRegion) (hN : 2 ≤ R.N) (e : ℕ) (he : e ≠ 0) (u : ℂ) :
    u ∈ (Planar.efold R hN e he).K ↔ R.q + u ^ e ∈ R.K := (Planar.efold_spec R hN e he).2.2.1 u
theorem efold_mem_Kint_iff (R : RadialRegion) (hN : 2 ≤ R.N) (e : ℕ) (he : e ≠ 0) (u : ℂ) :
    u ∈ (Planar.efold R hN e he).Kint ↔ R.q + u ^ e ∈ R.Kint :=
  (Planar.efold_spec R hN e he).2.2.2.1 u

noncomputable def capRegion (p : ℤ × ℤ) (b : ℂ) (w : Place ℂ F) : RadialRegion :=
  if h : M.cape b w ≠ 0 then Planar.efold (M.base p) (M.two_le_base_N p) (M.cape b w) h else M.base p

noncomputable def infRegion (w : Place ℂ F) : RadialRegion :=
  if h : M.infe w ≠ 0 then Planar.efold M.infBase M.two_le_infBase_N (M.infe w) h else M.infBase

theorem capRegion_eq {p : ℤ × ℤ} {b : ℂ} {w : Place ℂ F} (h : M.cape b w ≠ 0) :
    M.capRegion p b w = Planar.efold (M.base p) (M.two_le_base_N p) (M.cape b w) h := dif_pos h

theorem infRegion_eq {w : Place ℂ F} (h : M.infe w ≠ 0) :
    M.infRegion w = Planar.efold M.infBase M.two_le_infBase_N (M.infe w) h := dif_pos h

theorem capRegion_K_subset {p : ℤ × ℤ} {b : ℂ} (hb : b ∈ M.Bad) (hp : M.capAt p = some b)
    {w : Place ℂ F} (hw : M.x ∈ w.toValuationSubring) (hwb : Place.evalAt w M.x = b) :
    (M.capRegion p b w).K ⊆ (M.capζ b w).target := by
  have hchart := M.hcapchart b hb w hw hwb
  have he : M.cape b w ≠ 0 := hchart.e_pos.ne'
  rw [M.capRegion_eq he, hchart.target]
  intro u hu
  rw [efold_mem_K_iff, base_q, base_K] at hu
  have hctr : M.ctr p = b := by simp [ctr, hp]
  have hb_mem : b ∈ PlaneGrid.gridSquare M.o M.hm p.1 p.2 := by
    rw [gridSquare_eq]
    have h := M.bad_mem_of_capAt hp
    exact ⟨⟨h.1.1.le, h.1.2.le⟩, h.2.1.le, h.2.2.le⟩
  have hdist : ‖u ^ M.cape b w‖ ≤ 2 * M.hm := by
    have := M.norm_sub_le_of_mem_gridSquare hu hb_mem
    rwa [hctr, add_sub_cancel_left] at this
  have hbig := M.hcapbig b hb w hw hwb
  have hcs := M.hcs b hb
  rw [Metric.mem_ball, dist_zero_right]
  by_contra hcon
  push Not at hcon
  have : M.capρ b w ^ M.cape b w ≤ ‖u‖ ^ M.cape b w :=
    pow_le_pow_left₀ hchart.ρ_pos.le hcon _
  rw [← norm_pow] at this
  linarith [hdist, hbig, hcs, M.hhm]

theorem infRegion_K_subset {w : Place ℂ F} (hw : M.x ∉ w.toValuationSubring) :
    (M.infRegion w).K ⊆ (M.infζ w).target := by
  have hchart := M.hinfchart w hw
  have he : M.infe w ≠ 0 := hchart.e_pos.ne'
  rw [M.infRegion_eq he, hchart.target]
  intro u hu
  rw [efold_mem_K_iff, infBase_q, zero_add] at hu
  have hbig := M.hinfbig w hw
  have hRw : 0 < M.Rw := by linarith [M.hRw]
  rw [Metric.mem_ball, dist_zero_right]

  have hnorm : ‖u ^ M.infe w‖ ≤ 1 / M.Rw := by
    by_cases h0 : u ^ M.infe w = 0
    · rw [h0, norm_zero]
      positivity
    · have hout := (M.mem_infBase_K_iff h0).mp hu
      by_contra hcon
      push Not at hcon
      apply hout

      have hinv : ‖(u ^ M.infe w)⁻¹‖ < M.Rw := by
        rw [norm_inv]
        have hpos : 0 < ‖u ^ M.infe w‖ := norm_pos_iff.mpr h0
        rw [inv_lt_comm₀ hpos hRw]
        rwa [one_div] at hcon
      have hin := M.hinner_Kint hinv
      exact hin
  by_contra hcon
  push Not at hcon
  have : M.infρ w ^ M.infe w ≤ ‖u‖ ^ M.infe w := pow_le_pow_left₀ hchart.ρ_pos.le hcon _
  rw [← norm_pow] at this
  linarith

section FibreBridge

variable [IsCurveOver ℂ F]

omit [Planar] in

theorem ord_eq_one_of_card_fiber {t : ℂ} (ht : t ∉ M.Bad) {P : Place ℂ F}
    (hxP : M.x ∈ P.toValuationSubring) (hPt : Place.evalAt P M.x = t) :
    P.ord (M.x - algebraMap ℂ F t) = 1 := by
  haveI := M.hfd
  have hw : P ∈ FibreDegree.fib M.x t := ⟨hxP, hPt⟩
  have hs : ∀ w, w ∈ (M.hfib t).toFinset ↔ w ∈ FibreDegree.fib M.x t :=
    fun w => (M.hfib t).mem_toFinset
  have hcard : (M.hfib t).toFinset.card = FibreDegree.deg M.x := by
    rw [M.hcard t ht, M.hdeg]
  have h1 := FibreDegree.eFin_eq_one_of_card M.x M.hx _ hs hcard hw
  unfold FibreDegree.eFin at h1
  omega

omit [Planar] [IsCurveOver ℂ F] in

theorem evalAt_inv_of_pole {w : Place ℂ F} (hw : M.x ∉ w.toValuationSubring) :
    Place.evalAt w M.x⁻¹ = 0 :=
  FibreDegree.evalAt_inv_of_mem_poles M.x hw

end FibreBridge
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.AssemblyData P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily"

section Analytic

variable [IsCurveOver ℂ F] [T2Space (Place ℂ F)] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]
omit [T2Space (Place ℂ F)] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [Planar] in

theorem ord_eq_one_of_mem_sheet {p : ℤ × ℤ} (hw : p ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi)
    (hp : M.capAt p = none) (i : Fin M.n) {P : Place ℂ F} (hP : P ∈ (M.sheet p i).source) :
    P.ord (M.x - algebraMap ℂ F (P.evalAt M.x)) = 1 := by
  have hfam := M.hsheet p hw hp
  obtain ⟨hxP, hζP⟩ := hfam.forward i P hP
  set t : ℂ := Place.evalAt P M.x with ht
  have htV : t ∈ M.margin p := by
    have h := (M.sheet p i).map_source hP
    rwa [hfam.target i, hζP] at h
  have htBad : t ∉ M.Bad := fun hb => M.hmargin_bad p hw hp t hb htV
  exact M.ord_eq_one_of_card_fiber htBad hxP ht.symm

omit [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [Planar] in
theorem sheet_fields (hF : OrdPack F) (hrat : ∀ P : Place ℂ F, P.IsRational)
    {p : ℤ × ℤ} (hw : p ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi)
    (hp : M.capAt p = none) (i : Fin M.n) {P : Place ℂ F} (hP : P ∈ (M.sheet p i).source) :
    AnalyticAt ℂ (M.sheet p i ∘ (extChartAt 𝓘(ℂ, ℂ) P).symm) (extChartAt 𝓘(ℂ, ℂ) P P) ∧
      deriv (M.sheet p i ∘ (extChartAt 𝓘(ℂ, ℂ) P).symm) (extChartAt 𝓘(ℂ, ℂ) P P) ≠ 0 := by
  have hfam := M.hsheet p hw hp
  exact PlaceCoordinate.analyticCoord_fields_of_agree hF hrat M.hx (M.sheet p i)
    (fun Q hQ => (hfam.forward i Q hQ).2) P hP (hfam.forward i P hP).1
    (M.ord_eq_one_of_mem_sheet hw hp i hP)

omit [Planar] [IsCurveOver ℂ F] [T2Space (Place ℂ F)] in
theorem normalChart_fields {g : F} {w : Place ℂ F} {ζ : OpenPartialHomeomorph (Place ℂ F) ℂ}
    {ρ : ℝ} {e : ℕ} (h : IsNormalChart g w ζ ρ e) {P : Place ℂ F} (hP : P ∈ ζ.source) :
    AnalyticAt ℂ (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) P).symm) (extChartAt 𝓘(ℂ, ℂ) P P) ∧
      deriv (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) P).symm) (extChartAt 𝓘(ℂ, ℂ) P P) ≠ 0 :=
  CentreChart.analyticCoord_fields_of_center ζ h.sub_chart h.analytic h.deriv_ne P hP

omit [Planar] [IsCurveOver ℂ F] [T2Space (Place ℂ F)] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem exists_capAt_eq {p : ℤ × ℤ} (hp : M.capAt p ≠ none) :
    ∃ b ∈ M.Bad, M.capAt p = some b ∧ (M.capAt p).getD 0 = b := by
  obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hp
  exact ⟨b, ((M.hcap p b).mp hb).1, hb, by simp [hb]⟩

noncomputable def toAssembly (hF : OrdPack F) (hrat : ∀ P : Place ℂ F, P.IsRational) :
    AssemblyData F where
  x := M.x
  n := M.n
  hn := M.hn
  jlo := M.jlo
  jhi := M.jhi
  klo := M.klo
  khi := M.khi
  o := M.o
  hm := M.hm
  hhm := M.hhm
  capAt := M.capAt
  hfib := M.hfib
  margin := M.margin
  sheetζ := M.sheet
  hmargin := M.hmargin_sq
  hζtarget := fun p hw hp i => (M.hsheet p hw hp).target i
  hζanalytic := fun p hw hp i P hP => (M.sheet_fields hF hrat hw hp i hP).1
  hζderiv := fun p hw hp i P hP => (M.sheet_fields hF hrat hw hp i hP).2
  rad := fun p _ => M.base p
  hradK := fun p _ _ _ => M.base_K p
  capζ := fun p w => M.capζ ((M.capAt p).getD 0) w
  capRad := fun p w => M.capRegion p ((M.capAt p).getD 0) w
  hcapanalytic := by
    intro p hp w hxw hwb P hP
    obtain ⟨b, hb, -, hbd⟩ := M.exists_capAt_eq hp
    rw [hbd] at hwb hP ⊢
    exact (normalChart_fields (M.hcapchart b hb w hxw hwb) hP).1
  hcapderiv := by
    intro p hp w hxw hwb P hP
    obtain ⟨b, hb, -, hbd⟩ := M.exists_capAt_eq hp
    rw [hbd] at hwb hP ⊢
    exact (normalChart_fields (M.hcapchart b hb w hxw hwb) hP).2
  hcapKt := by
    intro p hp w hxw hwb
    obtain ⟨b, hb, hsome, hbd⟩ := M.exists_capAt_eq hp
    simp only [hbd] at hwb ⊢
    exact M.capRegion_K_subset hb hsome hxw hwb
  hpoles := M.hpoles
  infζ := M.infζ
  infRad := M.infRegion
  hinfanalytic := fun w hw P hP => (normalChart_fields (M.hinfchart w hw) hP).1
  hinfderiv := fun w hw P hP => (normalChart_fields (M.hinfchart w hw) hP).2
  hinfKt := fun w hw => M.infRegion_K_subset hw

end Analytic
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.AssemblyData P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily"

section Carriers

omit [Planar] in
theorem Kint_subset_K (R : RadialRegion) : R.Kint ⊆ R.K := fun z hz =>
  show ‖z - R.q‖ ≤ R.r (Complex.arg (z - R.q)) from
    le_of_lt (show ‖z - R.q‖ < R.r (Complex.arg (z - R.q)) from hz)

variable [IsCurveOver ℂ F] [T2Space (Place ℂ F)] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]
variable (hF : OrdPack F) (hrat : ∀ P : Place ℂ F, P.IsRational)

omit [ChartedSpace ℂ (Place ℂ F)] [Planar] [IsCurveOver ℂ F] [T2Space (Place ℂ F)] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem symm_image_eq {ζ : OpenPartialHomeomorph (Place ℂ F) ℂ} {K : Set ℂ} (hK : K ⊆ ζ.target) :
    ζ.symm '' K = {P | P ∈ ζ.source ∧ ζ P ∈ K} := by
  ext P
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨ζ.map_target (hK hz), by rwa [ζ.right_inv (hK hz)]⟩
  · rintro ⟨hP, hz⟩
    exact ⟨ζ P, hz, ζ.left_inv hP⟩

theorem carrier_inl (Q : (M.toAssembly hF hrat).plain_finite.toFinset) (i : Fin M.n) :
    ((M.toAssembly hF hrat).cellOf (Sum.inl ⟨Q, i⟩)).carrier =
      {P | P ∈ (M.sheet Q.1 i).source ∧
        Place.evalAt P M.x ∈ PlaneGrid.gridSquare M.o M.hm Q.1.1 Q.1.2} := by
  have hQ := (M.toAssembly hF hrat).mem_plain_iff.mp
    ((M.toAssembly hF hrat).plain_finite.mem_toFinset.mp Q.2)
  have hfam := M.hsheet Q.1 hQ.1 hQ.2
  show (M.sheet Q.1 i).symm '' (M.base Q.1).K = _
  rw [base_K, symm_image_eq (ζ := M.sheet Q.1 i)]
  · ext P
    simp only [mem_setOf_eq]
    constructor
    · rintro ⟨hP, hz⟩
      exact ⟨hP, by rwa [← (hfam.forward i P hP).2]⟩
    · rintro ⟨hP, hz⟩
      exact ⟨hP, by rwa [(hfam.forward i P hP).2]⟩
  · rw [hfam.target i]
    exact M.hmargin_sq Q.1 hQ.1 hQ.2

theorem interior_inl (Q : (M.toAssembly hF hrat).plain_finite.toFinset) (i : Fin M.n) :
    ((M.toAssembly hF hrat).cellOf (Sum.inl ⟨Q, i⟩)).interior' =
      {P | P ∈ (M.sheet Q.1 i).source ∧
        (Place.evalAt P M.x).re ∈ Ioo (M.sx Q.1) (M.sx' Q.1) ∧
        (Place.evalAt P M.x).im ∈ Ioo (M.sy Q.1) (M.sy' Q.1)} := by
  have hQ := (M.toAssembly hF hrat).mem_plain_iff.mp
    ((M.toAssembly hF hrat).plain_finite.mem_toFinset.mp Q.2)
  have hfam := M.hsheet Q.1 hQ.1 hQ.2
  show (M.sheet Q.1 i).symm '' (M.base Q.1).Kint = _
  rw [base_Kint, symm_image_eq (ζ := M.sheet Q.1 i)]
  · ext P
    simp only [mem_setOf_eq]
    constructor
    · rintro ⟨hP, hz⟩
      rw [(hfam.forward i P hP).2] at hz
      exact ⟨hP, hz⟩
    · rintro ⟨hP, hz⟩
      exact ⟨hP, by rw [(hfam.forward i P hP).2]; exact hz⟩
  · rw [hfam.target i]
    intro z hz
    apply M.hmargin_sq Q.1 hQ.1 hQ.2
    rw [gridSquare_eq]
    exact ⟨Ioo_subset_Icc_self hz.1, Ioo_subset_Icc_self hz.2⟩

omit [Planar] [IsCurveOver ℂ F] [T2Space (Place ℂ F)] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem evalAt_eq_of_mem_capζ (hrat : ∀ P : Place ℂ F, P.IsRational) {b : ℂ} (hb : b ∈ M.Bad)
    {w : Place ℂ F}
    (hxw : M.x ∈ w.toValuationSubring) (hwb : Place.evalAt w M.x = b) {P : Place ℂ F}
    (hP : P ∈ (M.capζ b w).source) :
    M.x ∈ P.toValuationSubring ∧ Place.evalAt P M.x = b + (M.capζ b w P) ^ M.cape b w := by
  have hchart := M.hcapchart b hb w hxw hwb
  obtain ⟨hmem, hform⟩ := hchart.form P hP
  have hxP : M.x ∈ P.toValuationSubring := by
    have := add_mem hmem (P.algebraMap_mem' b)
    simpa using this
  refine ⟨hxP, ?_⟩
  rw [PlaceCoordinate.evalAt_sub_algebraMap P (hrat P) hxP b] at hform
  linear_combination hform

theorem carrier_cap (Q : (M.toAssembly hF hrat).caps_finite.toFinset)
    (w : (M.toAssembly hF hrat).Fib ((M.toAssembly hF hrat).capVal Q)) :
    ((M.toAssembly hF hrat).cellOf (Sum.inr (Sum.inl ⟨Q, w⟩))).carrier =
      {P | P ∈ (M.capζ ((M.capAt Q.1).getD 0) w.1).source ∧
        Place.evalAt P M.x ∈ PlaneGrid.gridSquare M.o M.hm Q.1.1 Q.1.2} := by
  have hQ := (M.toAssembly hF hrat).mem_caps_iff.mp
    ((M.toAssembly hF hrat).caps_finite.mem_toFinset.mp Q.2)
  obtain ⟨b, hb, hsome, hbd⟩ := M.exists_capAt_eq hQ.2
  have hw := w.2
  change M.x ∈ w.1.toValuationSubring ∧ Place.evalAt w.1 M.x = (M.capAt Q.1).getD 0 at hw
  rw [hbd] at hw
  have hchart := M.hcapchart b hb w.1 hw.1 hw.2
  have he : M.cape b w.1 ≠ 0 := hchart.e_pos.ne'
  show (M.capζ ((M.capAt Q.1).getD 0) w.1).symm '' (M.capRegion Q.1 ((M.capAt Q.1).getD 0) w.1).K = _
  simp only [hbd]
  rw [symm_image_eq (M.capRegion_K_subset hb hsome hw.1 hw.2), M.capRegion_eq he]
  ext P
  simp only [mem_setOf_eq, efold_mem_K_iff, base_q, base_K]
  have hctr : M.ctr Q.1 = b := by simp [ctr, hsome]
  rw [hctr]
  constructor
  · rintro ⟨hP, hz⟩
    exact ⟨hP, by rw [(M.evalAt_eq_of_mem_capζ hrat hb hw.1 hw.2 hP).2]; exact hz⟩
  · rintro ⟨hP, hz⟩
    exact ⟨hP, by rw [← (M.evalAt_eq_of_mem_capζ hrat hb hw.1 hw.2 hP).2]; exact hz⟩

omit [Planar] [IsCurveOver ℂ F] [T2Space (Place ℂ F)] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem evalAt_of_mem_infζ (hrat : ∀ P : Place ℂ F, P.IsRational) {w : Place ℂ F}
    (hw : M.x ∉ w.toValuationSubring) {P : Place ℂ F}
    (hP : P ∈ (M.infζ w).source) (hxP : M.x ∈ P.toValuationSubring) :
    Place.evalAt P M.x ≠ 0 ∧ (Place.evalAt P M.x)⁻¹ = (M.infζ w P) ^ M.infe w := by
  have hchart := M.hinfchart w hw
  obtain ⟨hmem, hform⟩ := hchart.form P hP
  have hx0 : M.x ≠ 0 := fun h => hw (h ▸ zero_mem _)
  have h1 : Place.evalAt P (1 : F) = 1 := P.evalAt_one
  have hmul : Place.evalAt P M.x * Place.evalAt P M.x⁻¹ = 1 := by
    rw [← Place.evalAt_mul_of_mem P (hrat P) hxP hmem, mul_inv_cancel₀ hx0]
    exact h1
  have hne : Place.evalAt P M.x ≠ 0 := fun h => by rw [h, zero_mul] at hmul; exact zero_ne_one hmul
  refine ⟨hne, ?_⟩
  rw [← hform]
  exact (eq_inv_of_mul_eq_one_right hmul).symm

theorem carrier_inf (w : (M.toAssembly hF hrat).FibInf) :
    ((M.toAssembly hF hrat).cellOf (Sum.inr (Sum.inr w))).carrier =
      {P | P ∈ (M.infζ w.1).source ∧
        (M.x ∉ P.toValuationSubring ∨ Place.evalAt P M.x ∉ M.winReg.Kint)} := by
  have hw : M.x ∉ w.1.toValuationSubring := w.2
  have hchart := M.hinfchart w.1 hw
  have he : M.infe w.1 ≠ 0 := hchart.e_pos.ne'
  show (M.infζ w.1).symm '' (M.infRegion w.1).K = _
  rw [symm_image_eq (M.infRegion_K_subset hw), M.infRegion_eq he]
  ext P
  simp only [mem_setOf_eq, efold_mem_K_iff, infBase_q, zero_add]
  constructor
  · rintro ⟨hP, hz⟩
    refine ⟨hP, ?_⟩
    by_cases hxP : M.x ∈ P.toValuationSubring
    · right
      obtain ⟨hne, hinv⟩ := M.evalAt_of_mem_infζ hrat hw hP hxP
      rw [← hinv] at hz
      have hinv_ne : (Place.evalAt P M.x)⁻¹ ≠ 0 := inv_ne_zero hne
      have := (M.mem_infBase_K_iff hinv_ne).mp hz
      rwa [inv_inv] at this
    · exact Or.inl hxP
  · rintro ⟨hP, hout⟩
    refine ⟨hP, ?_⟩
    by_cases hxP : M.x ∈ P.toValuationSubring
    · have hout' : Place.evalAt P M.x ∉ M.winReg.Kint := hout.resolve_left fun h => h hxP
      obtain ⟨hne, hinv⟩ := M.evalAt_of_mem_infζ hrat hw hP hxP
      rw [← hinv]
      exact (M.mem_infBase_K_iff (inv_ne_zero hne)).mpr (by rwa [inv_inv])
    ·
      have hform := (hchart.form P hP).2
      rw [M.evalAt_inv_of_pole hxP] at hform
      rw [← hform]
      exact Kint_subset_K _ M.zero_mem_infBase_Kint

end Carriers
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.AssemblyData P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily"

section Cover

variable [IsCurveOver ℂ F] [T2Space (Place ℂ F)] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]
variable (hF : OrdPack F) (hrat : ∀ P : Place ℂ F, P.IsRational)

omit [Planar] [IsCurveOver ℂ F] [T2Space (Place ℂ F)] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem exists_idx_of_mem_Icc {lo hi : ℤ} (hlohi : lo ≤ hi) {c : ℝ}
    (hc : M.o + lo * M.hm ≤ c ∧ c ≤ M.o + (hi + 1) * M.hm) :
    ∃ j : ℤ, lo ≤ j ∧ j ≤ hi ∧ M.o + j * M.hm ≤ c ∧ c ≤ M.o + (j + 1) * M.hm := by
  have hhm := M.hhm
  set u : ℝ := (c - M.o) / M.hm with hu
  have hu_lo : (lo : ℝ) ≤ u := by
    rw [hu, le_div_iff₀ hhm]; linarith [hc.1]
  have hu_hi : u ≤ hi + 1 := by
    rw [hu, div_le_iff₀ hhm]; linarith [hc.2]
  by_cases hfl : ⌊u⌋ ≤ hi
  · refine ⟨⌊u⌋, ?_, hfl, ?_, ?_⟩
    · exact_mod_cast Int.le_floor.mpr hu_lo
    · have h := Int.floor_le u
      rw [hu, le_div_iff₀ hhm] at h; linarith
    · have h := (Int.lt_floor_add_one u).le
      rw [hu, div_le_iff₀ hhm] at h; linarith
  · push Not at hfl

    have h1 : (hi : ℝ) + 1 ≤ ⌊u⌋ := by exact_mod_cast hfl
    have h2 : (⌊u⌋ : ℝ) ≤ u := Int.floor_le u
    refine ⟨hi, hlohi, le_rfl, ?_, ?_⟩
    · have : (hi : ℝ) ≤ u := by linarith
      rw [hu, le_div_iff₀ hhm] at this; linarith
    · rw [hu] at hu_hi; rw [div_le_iff₀ hhm] at hu_hi; linarith

omit [IsCurveOver ℂ F] [T2Space (Place ℂ F)] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem exists_square_of_mem_winReg_K {v : ℂ} (hv : v ∈ M.winReg.K) :
    ∃ p : ℤ × ℤ, p ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi ∧
      v ∈ PlaneGrid.gridSquare M.o M.hm p.1 p.2 := by
  rw [winReg_K] at hv
  obtain ⟨⟨hre₁, hre₂⟩, him₁, him₂⟩ := hv
  have hj : M.jlo ≤ M.jhi := by have := M.hjlt; omega
  have hk : M.klo ≤ M.khi := by have := M.hklt; omega
  obtain ⟨j, hj₁, hj₂, hj₃, hj₄⟩ := M.exists_idx_of_mem_Icc hj (c := v.re) ⟨hre₁, hre₂⟩
  obtain ⟨k, hk₁, hk₂, hk₃, hk₄⟩ := M.exists_idx_of_mem_Icc hk (c := v.im) ⟨him₁, him₂⟩
  exact ⟨(j, k), ⟨⟨hj₁, hj₂⟩, hk₁, hk₂⟩, ⟨hj₃, hj₄⟩, hk₃, hk₄⟩

theorem cover (P : Place ℂ F) :
    ∃ C : (M.toAssembly hF hrat).IdxC, P ∈ ((M.toAssembly hF hrat).cellOf C).carrier := by
  by_cases hxP : M.x ∈ P.toValuationSubring
  · by_cases hv : Place.evalAt P M.x ∈ M.winReg.K
    · obtain ⟨p, hp, hvp⟩ := M.exists_square_of_mem_winReg_K hv
      by_cases hcap : M.capAt p = none
      ·
        have hpl : p ∈ (M.toAssembly hF hrat).Plain := (M.toAssembly hF hrat).mem_plain_iff.mpr ⟨hp, hcap⟩
        have hvV : Place.evalAt P M.x ∈ M.margin p := M.hmargin_sq p hp hcap hvp
        obtain ⟨i, hi⟩ := (M.hsheet p hp hcap).exhaust P hxP hvV
        refine ⟨Sum.inl ⟨⟨p, (M.toAssembly hF hrat).plain_finite.mem_toFinset.mpr hpl⟩, i⟩, ?_⟩
        rw [carrier_inl]
        exact ⟨hi, hvp⟩
      ·
        obtain ⟨b, hb, hsome, hbd⟩ := M.exists_capAt_eq hcap
        have hcp : p ∈ (M.toAssembly hF hrat).Caps := (M.toAssembly hF hrat).mem_caps_iff.mpr ⟨hp, hcap⟩
        have hb_sq : b ∈ PlaneGrid.gridSquare M.o M.hm p.1 p.2 := by
          rw [gridSquare_eq]
          have h := M.bad_mem_of_capAt hsome
          exact ⟨⟨h.1.1.le, h.1.2.le⟩, h.2.1.le, h.2.2.le⟩
        have hclose : ‖Place.evalAt P M.x - b‖ < 2 * M.cs b := by
          have h1 := M.norm_sub_le_of_mem_gridSquare hvp hb_sq
          have h2 := M.hcs b hb
          linarith [M.hhm]
        obtain ⟨w, hxw, hwb, hPw⟩ := M.hcapexhaust b hb P hxP hclose
        let Q : (M.toAssembly hF hrat).caps_finite.toFinset :=
          ⟨p, (M.toAssembly hF hrat).caps_finite.mem_toFinset.mpr hcp⟩
        have hwfib : M.x ∈ w.toValuationSubring ∧
            Place.evalAt w M.x = (M.toAssembly hF hrat).capVal Q := by
          refine ⟨hxw, ?_⟩
          show Place.evalAt w M.x = (M.capAt p).getD 0
          rw [hbd]; exact hwb
        refine ⟨Sum.inr (Sum.inl ⟨Q, ⟨w, hwfib⟩⟩), ?_⟩
        rw [carrier_cap]
        refine ⟨?_, hvp⟩
        show P ∈ (M.capζ ((M.capAt p).getD 0) w).source
        rw [hbd]; exact hPw
    ·
      have hbig : M.Rw ≤ ‖Place.evalAt P M.x‖ := by
        by_contra h
        push Not at h
        exact hv (M.mem_winReg_K_of_norm_le h.le)
      obtain ⟨w, hw, hPw⟩ := M.hinfexhaust P hxP hbig
      refine ⟨Sum.inr (Sum.inr ⟨w, hw⟩), ?_⟩
      rw [carrier_inf]
      exact ⟨hPw, Or.inr fun hint => hv (Kint_subset_K _ hint)⟩
  ·
    refine ⟨Sum.inr (Sum.inr ⟨P, hxP⟩), ?_⟩
    rw [carrier_inf]
    exact ⟨(M.hinfchart P hxP).mem, Or.inl hxP⟩

end Cover
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.AssemblyData P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily"

section Marked

variable [IsCurveOver ℂ F] [T2Space (Place ℂ F)] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]
variable (hF : OrdPack F) (hrat : ∀ P : Place ℂ F, P.IsRational)

noncomputable def sq (z : ℂ) : ℤ × ℤ := (⌊(z.re - M.o) / M.hm⌋, ⌊(z.im - M.o) / M.hm⌋)

omit [Planar] [IsCurveOver ℂ F] [T2Space (Place ℂ F)] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem mem_gridSquare_sq (z : ℂ) : z ∈ PlaneGrid.gridSquare M.o M.hm (M.sq z).1 (M.sq z).2 := by
  have hhm := M.hhm
  rw [gridSquare_eq]
  simp only [sq, sx, sx', sy, sy']
  have h1 := Int.floor_le ((z.re - M.o) / M.hm)
  have h2 := (Int.lt_floor_add_one ((z.re - M.o) / M.hm)).le
  have h3 := Int.floor_le ((z.im - M.o) / M.hm)
  have h4 := (Int.lt_floor_add_one ((z.im - M.o) / M.hm)).le
  rw [le_div_iff₀ hhm] at h1 h3
  rw [div_le_iff₀ hhm] at h2 h4
  exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

omit [Planar] [IsCurveOver ℂ F] [T2Space (Place ℂ F)] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem mem_open_sq_of_off {z : ℂ} (hoff : ∀ j : ℤ, z.re - M.o ≠ j * M.hm ∧ z.im - M.o ≠ j * M.hm) :
    (z.re ∈ Ioo (M.sx (M.sq z)) (M.sx' (M.sq z))) ∧ (z.im ∈ Ioo (M.sy (M.sq z)) (M.sy' (M.sq z))) := by
  have h := M.mem_gridSquare_sq z
  rw [gridSquare_eq] at h
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
  refine ⟨⟨lt_of_le_of_ne h1 ?_, lt_of_le_of_ne h2 ?_⟩, lt_of_le_of_ne h3 ?_, lt_of_le_of_ne h4 ?_⟩
  · intro heq; exact (hoff (M.sq z).1).1 (by simp only [sx] at heq; linarith)
  · intro heq; exact (hoff ((M.sq z).1 + 1)).1 (by simp only [sx'] at heq; push_cast; linarith)
  · intro heq; exact (hoff (M.sq z).2).2 (by simp only [sy] at heq; linarith)
  · intro heq; exact (hoff ((M.sq z).2 + 1)).2 (by simp only [sy'] at heq; push_cast; linarith)

omit [Planar] [IsCurveOver ℂ F] [T2Space (Place ℂ F)] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem sq_eq_of_mem_open {z : ℂ} {p : ℤ × ℤ}
    (hre : z.re ∈ Ioo (M.sx p) (M.sx' p)) (him : z.im ∈ Ioo (M.sy p) (M.sy' p)) : M.sq z = p := by
  have hhm := M.hhm
  simp only [sx, sx', sy, sy'] at hre him
  refine Prod.ext ?_ ?_
  · show ⌊(z.re - M.o) / M.hm⌋ = p.1
    rw [Int.floor_eq_iff]
    constructor
    · rw [le_div_iff₀ hhm]; linarith [hre.1]
    · rw [div_lt_iff₀ hhm]; linarith [hre.2]
  · show ⌊(z.im - M.o) / M.hm⌋ = p.2
    rw [Int.floor_eq_iff]
    constructor
    · rw [le_div_iff₀ hhm]; linarith [him.1]
    · rw [div_lt_iff₀ hhm]; linarith [him.2]

omit [Planar] [IsCurveOver ℂ F] [T2Space (Place ℂ F)] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem sq_eq_of_mem_gridSquare_of_off {z : ℂ} {p : ℤ × ℤ}
    (hz : z ∈ PlaneGrid.gridSquare M.o M.hm p.1 p.2)
    (hoff : ∀ j : ℤ, z.re - M.o ≠ j * M.hm ∧ z.im - M.o ≠ j * M.hm) : M.sq z = p := by
  rw [gridSquare_eq] at hz
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz
  apply M.sq_eq_of_mem_open
  · refine ⟨lt_of_le_of_ne h1 ?_, lt_of_le_of_ne h2 ?_⟩
    · intro heq; exact (hoff p.1).1 (by simp only [sx] at heq; linarith)
    · intro heq; exact (hoff (p.1 + 1)).1 (by simp only [sx'] at heq; push_cast; linarith)
  · refine ⟨lt_of_le_of_ne h3 ?_, lt_of_le_of_ne h4 ?_⟩
    · intro heq; exact (hoff p.2).2 (by simp only [sy] at heq; linarith)
    · intro heq; exact (hoff (p.2 + 1)).2 (by simp only [sy'] at heq; push_cast; linarith)

omit [Planar] [IsCurveOver ℂ F] [T2Space (Place ℂ F)] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem sq_mem_win_of_norm_lt {z : ℂ} (hz : ‖z‖ < M.Rw - 1) :
    M.sq z ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi := by
  have hhm := M.hhm
  have h := M.hinner z hz
  have hsq := M.mem_gridSquare_sq z
  rw [gridSquare_eq] at hsq
  simp only [sx, sx', sy, sy'] at hsq

  have hj1 : ((M.sq z).1 : ℝ) * M.hm < M.jhi * M.hm := by linarith [hsq.1.1, h.1.2]
  have hj2 : ((M.jlo : ℝ) + 1) * M.hm < ((M.sq z).1 + 1) * M.hm := by linarith [hsq.1.2, h.1.1]
  have hk1 : ((M.sq z).2 : ℝ) * M.hm < M.khi * M.hm := by linarith [hsq.2.1, h.2.2]
  have hk2 : ((M.klo : ℝ) + 1) * M.hm < ((M.sq z).2 + 1) * M.hm := by linarith [hsq.2.2, h.2.1]
  have hj1' : ((M.sq z).1 : ℝ) < M.jhi := lt_of_mul_lt_mul_right hj1 hhm.le
  have hj2' : ((M.jlo : ℝ) + 1) < (M.sq z).1 + 1 := lt_of_mul_lt_mul_right hj2 hhm.le
  have hk1' : ((M.sq z).2 : ℝ) < M.khi := lt_of_mul_lt_mul_right hk1 hhm.le
  have hk2' : ((M.klo : ℝ) + 1) < (M.sq z).2 + 1 := lt_of_mul_lt_mul_right hk2 hhm.le
  have a1 : (M.sq z).1 < M.jhi := by exact_mod_cast hj1'
  have a2 : M.jlo < (M.sq z).1 := by
    have : (M.jlo : ℝ) < (M.sq z).1 := by linarith
    exact_mod_cast this
  have a3 : (M.sq z).2 < M.khi := by exact_mod_cast hk1'
  have a4 : M.klo < (M.sq z).2 := by
    have : (M.klo : ℝ) < (M.sq z).2 := by linarith
    exact_mod_cast this
  exact ⟨⟨a2.le, a1.le⟩, a4.le, a3.le⟩

omit [Planar] [IsCurveOver ℂ F] [T2Space (Place ℂ F)] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem capAt_sq {b : ℂ} (hb : b ∈ M.Bad) : M.capAt (M.sq b) = some b :=
  (M.hcap (M.sq b) b).mpr ⟨hb, rfl, rfl⟩

omit [Planar] [IsCurveOver ℂ F] [T2Space (Place ℂ F)] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem eq_of_mem_capζ_source {b : ℂ} (hb : b ∈ M.Bad) {w v : Place ℂ F}
    (hxw : M.x ∈ w.toValuationSubring) (hwb : Place.evalAt w M.x = b)
    (hxv : M.x ∈ v.toValuationSubring) (hvb : Place.evalAt v M.x = b)
    (hv : v ∈ (M.capζ b w).source) : v = w := by
  by_contra hne
  have hdisj := M.hcapdisj b hb v w hxv hvb hxw hwb hne
  have hvv : v ∈ (M.capζ b v).source := (M.hcapchart b hb v hxv hvb).mem
  exact Set.disjoint_left.mp hdisj hvv hv

omit [Planar] [IsCurveOver ℂ F] [T2Space (Place ℂ F)] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem eq_of_mem_infζ_source {w v : Place ℂ F} (hw : M.x ∉ w.toValuationSubring)
    (hv' : M.x ∉ v.toValuationSubring) (hv : v ∈ (M.infζ w).source) : v = w := by
  by_contra hne
  have hdisj := M.hinfdisj v w hv' hw hne
  exact Set.disjoint_left.mp hdisj (M.hinfchart v hv').mem hv

theorem interior_cap (Q : (M.toAssembly hF hrat).caps_finite.toFinset)
    (w : (M.toAssembly hF hrat).Fib ((M.toAssembly hF hrat).capVal Q)) :
    ((M.toAssembly hF hrat).cellOf (Sum.inr (Sum.inl ⟨Q, w⟩))).interior' =
      {P | P ∈ (M.capζ ((M.capAt Q.1).getD 0) w.1).source ∧
        (Place.evalAt P M.x).re ∈ Ioo (M.sx Q.1) (M.sx' Q.1) ∧
        (Place.evalAt P M.x).im ∈ Ioo (M.sy Q.1) (M.sy' Q.1)} := by
  have hQ := (M.toAssembly hF hrat).mem_caps_iff.mp
    ((M.toAssembly hF hrat).caps_finite.mem_toFinset.mp Q.2)
  obtain ⟨b, hb, hsome, hbd⟩ := M.exists_capAt_eq hQ.2
  have hw := w.2
  change M.x ∈ w.1.toValuationSubring ∧ Place.evalAt w.1 M.x = (M.capAt Q.1).getD 0 at hw
  rw [hbd] at hw
  have hchart := M.hcapchart b hb w.1 hw.1 hw.2
  have he : M.cape b w.1 ≠ 0 := hchart.e_pos.ne'
  show (M.capζ ((M.capAt Q.1).getD 0) w.1).symm '' (M.capRegion Q.1 ((M.capAt Q.1).getD 0) w.1).Kint = _
  simp only [hbd]
  rw [symm_image_eq ((Kint_subset_K _).trans (M.capRegion_K_subset hb hsome hw.1 hw.2)),
    M.capRegion_eq he]
  ext P
  simp only [mem_setOf_eq, efold_mem_Kint_iff, base_q, base_Kint]
  have hctr : M.ctr Q.1 = b := by simp [ctr, hsome]
  rw [hctr]
  constructor
  · rintro ⟨hP, hz⟩
    exact ⟨hP, by rw [(M.evalAt_eq_of_mem_capζ hrat hb hw.1 hw.2 hP).2]; exact hz⟩
  · rintro ⟨hP, hz⟩
    exact ⟨hP, by rw [← (M.evalAt_eq_of_mem_capζ hrat hb hw.1 hw.2 hP).2]; exact hz⟩

theorem interior_inf (w : (M.toAssembly hF hrat).FibInf) :
    ((M.toAssembly hF hrat).cellOf (Sum.inr (Sum.inr w))).interior' =
      {P | P ∈ (M.infζ w.1).source ∧
        (M.x ∉ P.toValuationSubring ∨ Place.evalAt P M.x ∉ M.winReg.K)} := by
  have hw : M.x ∉ w.1.toValuationSubring := w.2
  have hchart := M.hinfchart w.1 hw
  have he : M.infe w.1 ≠ 0 := hchart.e_pos.ne'
  show (M.infζ w.1).symm '' (M.infRegion w.1).Kint = _
  rw [symm_image_eq ((Kint_subset_K _).trans (M.infRegion_K_subset hw)), M.infRegion_eq he]
  ext P
  simp only [mem_setOf_eq, efold_mem_Kint_iff, infBase_q, zero_add]
  constructor
  · rintro ⟨hP, hz⟩
    refine ⟨hP, ?_⟩
    by_cases hxP : M.x ∈ P.toValuationSubring
    · right
      obtain ⟨hne, hinv⟩ := M.evalAt_of_mem_infζ hrat hw hP hxP
      rw [← hinv] at hz
      have := (M.mem_infBase_Kint_iff (inv_ne_zero hne)).mp hz
      rwa [inv_inv] at this
    · exact Or.inl hxP
  · rintro ⟨hP, hout⟩
    refine ⟨hP, ?_⟩
    by_cases hxP : M.x ∈ P.toValuationSubring
    · have hout' : Place.evalAt P M.x ∉ M.winReg.K := hout.resolve_left fun h => h hxP
      obtain ⟨hne, hinv⟩ := M.evalAt_of_mem_infζ hrat hw hP hxP
      rw [← hinv]
      exact (M.mem_infBase_Kint_iff (inv_ne_zero hne)).mpr (by rwa [inv_inv])
    · have hform := (hchart.form P hP).2
      rw [M.evalAt_inv_of_pole hxP] at hform
      rw [← hform]
      exact M.zero_mem_infBase_Kint

theorem marked_centred (v : Place ℂ F) (hv : v ∈ insert P₀ (S : Set (Place ℂ F))) :
    ∃ C : (M.toAssembly hF hrat).IdxC,
      v ∈ ((M.toAssembly hF hrat).cellOf C).interior' ∧
        ((M.toAssembly hF hrat).cellOf C).ζ v = ((M.toAssembly hF hrat).cellOf C).R.q := by
  by_cases hxv : M.x ∈ v.toValuationSubring
  · set t : ℂ := Place.evalAt v M.x with ht
    by_cases htb : t ∈ M.Bad
    ·
      have hwin : M.sq t ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi :=
        M.sq_mem_win_of_norm_lt (M.hbadR t htb)
      have hsome : M.capAt (M.sq t) = some t := M.capAt_sq htb
      have hcp : M.sq t ∈ (M.toAssembly hF hrat).Caps :=
        (M.toAssembly hF hrat).mem_caps_iff.mpr
          ⟨hwin, by show M.capAt (M.sq t) ≠ none; rw [hsome]; exact Option.some_ne_none t⟩
      let Q : (M.toAssembly hF hrat).caps_finite.toFinset :=
        ⟨M.sq t, (M.toAssembly hF hrat).caps_finite.mem_toFinset.mpr hcp⟩
      have hvfib : M.x ∈ v.toValuationSubring ∧
          Place.evalAt v M.x = (M.toAssembly hF hrat).capVal Q := by
        refine ⟨hxv, ?_⟩
        show Place.evalAt v M.x = (M.capAt (M.sq t)).getD 0
        rw [hsome]; rfl
      have hchart := M.hcapchart t htb v hxv rfl
      have he : M.cape t v ≠ 0 := hchart.e_pos.ne'
      refine ⟨Sum.inr (Sum.inl ⟨Q, ⟨v, hvfib⟩⟩), ?_, ?_⟩
      · rw [interior_cap]
        have hopen := M.bad_mem_of_capAt hsome
        refine ⟨?_, ⟨hopen.1.1, hopen.1.2⟩, hopen.2.1, hopen.2.2⟩
        show v ∈ (M.capζ ((M.capAt (M.sq t)).getD 0) v).source
        rw [hsome]
        exact hchart.mem
      · show M.capζ ((M.capAt (M.sq t)).getD 0) v v = (M.capRegion (M.sq t) ((M.capAt (M.sq t)).getD 0) v).q
        simp only [hsome, Option.getD_some]
        rw [M.capRegion_eq he, efold_q]
        exact hchart.centre
    ·
      obtain ⟨hR, hoff, hnone, hcen⟩ := M.hmarked v hv hxv htb
      have hwin : M.sq t ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi := M.sq_mem_win_of_norm_lt hR
      have hnone' : M.capAt (M.sq t) = none := hnone
      have hpl : M.sq t ∈ (M.toAssembly hF hrat).Plain :=
        (M.toAssembly hF hrat).mem_plain_iff.mpr ⟨hwin, hnone'⟩
      have hfam := M.hsheet (M.sq t) hwin hnone'
      have htV : t ∈ M.margin (M.sq t) := M.hmargin_sq _ hwin hnone' (M.mem_gridSquare_sq t)
      obtain ⟨i, hi⟩ := hfam.exhaust v hxv htV
      refine ⟨Sum.inl ⟨⟨M.sq t, (M.toAssembly hF hrat).plain_finite.mem_toFinset.mpr hpl⟩, i⟩, ?_, ?_⟩
      · rw [interior_inl]
        exact ⟨hi, M.mem_open_sq_of_off hoff⟩
      · show M.sheet (M.sq t) i v = (M.base (M.sq t)).q
        rw [base_q, (hfam.forward i v hi).2]
        show t = M.ctr (M.sq t)
        simp only [ctr, hnone', Option.getD_none]
        exact hcen.symm
  ·
    have hchart := M.hinfchart v hxv
    have he : M.infe v ≠ 0 := hchart.e_pos.ne'
    refine ⟨Sum.inr (Sum.inr ⟨v, hxv⟩), ?_, ?_⟩
    · rw [interior_inf]
      exact ⟨hchart.mem, Or.inl hxv⟩
    · show M.infζ v v = (M.infRegion v).q
      rw [M.infRegion_eq he, efold_q]
      exact hchart.centre

theorem carrier_inter_marked_subsingleton (C : (M.toAssembly hF hrat).IdxC) :
    (((M.toAssembly hF hrat).cellOf C).carrier ∩ (S : Set (Place ℂ F))).Subsingleton := by

  have hS : ∀ v ∈ S, v ∈ insert P₀ (S : Set (Place ℂ F)) := fun v hv =>
    Set.mem_insert_of_mem P₀ (Finset.mem_coe.mpr hv)
  rcases C with ⟨Q, i⟩ | ⟨Q, w⟩ | w
  ·

    have hQ := (M.toAssembly hF hrat).mem_plain_iff.mp
      ((M.toAssembly hF hrat).plain_finite.mem_toFinset.mp Q.2)
    have hfam := M.hsheet Q.1 hQ.1 hQ.2
    intro v ⟨hvC, hvS⟩ v' ⟨hv'C, hv'S⟩
    rw [carrier_inl] at hvC hv'C
    obtain ⟨hvsrc, hvsq⟩ := hvC
    obtain ⟨hv'src, hv'sq⟩ := hv'C
    have hxv := (hfam.forward i v hvsrc).1
    have hxv' := (hfam.forward i v' hv'src).1
    have hvBad : Place.evalAt v M.x ∉ M.Bad := fun hb =>
      M.hmargin_bad Q.1 hQ.1 hQ.2 _ hb (M.hmargin_sq Q.1 hQ.1 hQ.2 hvsq)
    have hv'Bad : Place.evalAt v' M.x ∉ M.Bad := fun hb =>
      M.hmargin_bad Q.1 hQ.1 hQ.2 _ hb (M.hmargin_sq Q.1 hQ.1 hQ.2 hv'sq)
    obtain ⟨-, hoff, -, -⟩ := M.hmarked v (hS v hvS) hxv hvBad
    obtain ⟨-, hoff', -, -⟩ := M.hmarked v' (hS v' hv'S) hxv' hv'Bad
    have hval : Place.evalAt v M.x = Place.evalAt v' M.x := by
      by_contra hne
      apply M.hmarked_sep v (hS v hvS) v' (hS v' hv'S) hxv hxv' hvBad hv'Bad hne
      show M.sq _ = M.sq _
      rw [M.sq_eq_of_mem_gridSquare_of_off hvsq hoff, M.sq_eq_of_mem_gridSquare_of_off hv'sq hoff']
    apply (M.sheet Q.1 i).injOn hvsrc hv'src
    rw [(hfam.forward i v hvsrc).2, (hfam.forward i v' hv'src).2, hval]
  ·
    have hQ := (M.toAssembly hF hrat).mem_caps_iff.mp
      ((M.toAssembly hF hrat).caps_finite.mem_toFinset.mp Q.2)
    obtain ⟨b, hb, hsome, hbd⟩ := M.exists_capAt_eq hQ.2
    have hw := w.2
    change M.x ∈ w.1.toValuationSubring ∧ Place.evalAt w.1 M.x = (M.capAt Q.1).getD 0 at hw
    rw [hbd] at hw
    have key : ∀ v ∈ S, v ∈ ((M.toAssembly hF hrat).cellOf (Sum.inr (Sum.inl ⟨Q, w⟩))).carrier →
        v = w.1 := by
      intro v hvS hvC
      rw [carrier_cap] at hvC
      obtain ⟨hvsrc, hvsq⟩ := hvC
      rw [hbd] at hvsrc
      have hxv := (M.evalAt_eq_of_mem_capζ hrat hb hw.1 hw.2 hvsrc).1
      by_cases hvb : Place.evalAt v M.x ∈ M.Bad
      ·
        have hsq : M.sq (Place.evalAt v M.x) = Q.1 :=
          M.sq_eq_of_mem_gridSquare_of_off hvsq (M.hbad_off _ hvb)
        have h1 : M.capAt Q.1 = some (Place.evalAt v M.x) := by rw [← hsq]; exact M.capAt_sq hvb
        have hvb' : Place.evalAt v M.x = b := by
          rw [h1] at hsome; exact Option.some_injective _ hsome
        exact M.eq_of_mem_capζ_source hb hw.1 hw.2 hxv hvb' hvsrc
      ·
        exfalso
        obtain ⟨-, hoff, hnone, -⟩ := M.hmarked v (hS v hvS) hxv hvb
        have hsq : M.sq (Place.evalAt v M.x) = Q.1 := M.sq_eq_of_mem_gridSquare_of_off hvsq hoff
        have : M.capAt Q.1 = none := by rw [← hsq]; exact hnone
        rw [this] at hsome
        exact absurd hsome (by simp)
    intro v ⟨hvC, hvS⟩ v' ⟨hv'C, hv'S⟩
    rw [key v hvS hvC, key v' hv'S hv'C]
  ·
    have hw : M.x ∉ w.1.toValuationSubring := w.2
    have key : ∀ v ∈ S, v ∈ ((M.toAssembly hF hrat).cellOf (Sum.inr (Sum.inr w))).carrier →
        v = w.1 := by
      intro v hvS hvC
      rw [carrier_inf] at hvC
      obtain ⟨hvsrc, hout⟩ := hvC
      by_cases hxv : M.x ∈ v.toValuationSubring
      · exfalso
        have hout' := hout.resolve_left fun h => h hxv
        have hsmall := M.hmarked_R v (hS v hvS) hxv
        exact hout' (M.hinner_Kint (by linarith))
      · exact M.eq_of_mem_infζ_source hw hxv hvsrc
    intro v ⟨hvC, hvS⟩ v' ⟨hv'C, hv'S⟩
    rw [key v hvS hvC, key v' hv'S hv'C]

end Marked
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.AssemblyData P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily"

end DissectionMaterials.Materials
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.AssemblyData P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily"
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.AssemblyData P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily"

end Part_l3_cells
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.AssemblyData P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily"

section Part_D1EdgeData

set_option autoImplicit false

p2m_open "AlgebraicCurve~H1 Set"

namespace CurveCellFamily

variable {F : Type*} [Field F] [Algebra ℂ F] [TopologicalSpace (Place ℂ F)]
variable [ChartedSpace ℂ (Place ℂ F)]

namespace AssemblyData

variable (A : AssemblyData F)

def ArcIdx : Type _ := Σ C : A.IdxC, Fin (A.cellOf C).R.N

noncomputable scoped instance : Fintype A.ArcIdx := by
  unfold ArcIdx
  infer_instance

noncomputable scoped instance : DecidableEq A.ArcIdx := Classical.decEq _

noncomputable def endPt (a : A.ArcIdx) (b : Bool) : Place ℂ F :=
  (A.cellOf a.1).bdry ((A.cellOf a.1).R.φs (if b then a.2.succ else a.2.castSucc))

theorem endPt_false (a : A.ArcIdx) :
    A.endPt a false = (A.cellOf a.1).bdry ((A.cellOf a.1).R.φs a.2.castSucc) := rfl

theorem endPt_true (a : A.ArcIdx) :
    A.endPt a true = (A.cellOf a.1).bdry ((A.cellOf a.1).R.φs a.2.succ) := rfl

def VertSet : Set (Place ℂ F) :=
  Set.range fun ab : A.ArcIdx × Bool => A.endPt ab.1 ab.2

theorem endPt_mem_vertSet (a : A.ArcIdx) (b : Bool) : A.endPt a b ∈ A.VertSet :=
  ⟨(a, b), rfl⟩

theorem vertSet_finite : A.VertSet.Finite := Set.finite_range _

def IdxV : Type _ := {v : Place ℂ F // v ∈ A.VertSet}

noncomputable scoped instance : Fintype A.IdxV := A.vertSet_finite.fintype

noncomputable scoped instance : DecidableEq A.IdxV := Classical.decEq _

def vert : A.IdxV → Place ℂ F := Subtype.val

end AssemblyData
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.AssemblyData P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily"

structure EdgeData (A : AssemblyData F) where
  pair : A.ArcIdx → A.ArcIdx
  hpair : ∀ a, pair (pair a) = a
  orient : A.ArcIdx → Bool
  horient : ∀ a, orient (pair a) = !orient a
  hrev : ∀ (C : A.IdxC) (k : Fin (A.cellOf C).R.N) (C' : A.IdxC)
    (k' : Fin (A.cellOf C').R.N),
    pair ⟨C, k⟩ = ⟨C', k'⟩ → orient ⟨C, k⟩ = true →
    ∃ ψ : ℝ → ℝ,
      StrictAntiOn ψ ((A.cellOf C').R.arcIcc k') ∧
      ContDiffOn ℝ 1 ψ ((A.cellOf C').R.arcIcc k') ∧
      ψ ((A.cellOf C').R.φs k'.castSucc) = (A.cellOf C).R.φs k.succ ∧
      ψ ((A.cellOf C').R.φs k'.succ) = (A.cellOf C).R.φs k.castSucc ∧
      ∀ t ∈ (A.cellOf C').R.arcIcc k', (A.cellOf C').bdry t = (A.cellOf C).bdry (ψ t)

namespace EdgeData

variable {A : AssemblyData F} (E : EdgeData A)

theorem orient_pair_of_not {a : A.ArcIdx} (h : ¬E.orient a = true) :
    E.orient (E.pair a) = true := by
  have h' : E.orient a = false := by
    revert h
    cases E.orient a <;> simp
  rw [E.horient, h']
  rfl

def IdxE : Type _ := {a : A.ArcIdx // E.orient a = true}

noncomputable scoped instance : Fintype E.IdxE := by
  unfold IdxE
  infer_instance

noncomputable scoped instance : DecidableEq E.IdxE := Classical.decEq _

noncomputable def sideOf (C : A.IdxC) (k : Fin (A.cellOf C).R.N) : E.IdxE × Bool :=
  if h : E.orient ⟨C, k⟩ = true then (⟨⟨C, k⟩, h⟩, true)
  else (⟨E.pair ⟨C, k⟩, E.orient_pair_of_not h⟩, false)

theorem sideOf_bij :
    Function.Bijective fun a : A.ArcIdx => E.sideOf a.1 a.2 := by
  constructor
  · rintro ⟨C, k⟩ ⟨C', k'⟩ h
    simp only [sideOf] at h
    by_cases ha : E.orient ⟨C, k⟩ = true <;> by_cases ha' : E.orient ⟨C', k'⟩ = true
    · rw [dif_pos ha, dif_pos ha'] at h
      exact Subtype.ext_iff.mp (congrArg Prod.fst h)
    · rw [dif_pos ha, dif_neg ha'] at h
      exact Bool.noConfusion (congrArg Prod.snd h)
    · rw [dif_neg ha, dif_pos ha'] at h
      exact Bool.noConfusion (congrArg Prod.snd h)
    · rw [dif_neg ha, dif_neg ha'] at h
      have hval : E.pair ⟨C, k⟩ = E.pair ⟨C', k'⟩ :=
        Subtype.ext_iff.mp (congrArg Prod.fst h)
      have h2 := congrArg E.pair hval
      rwa [E.hpair, E.hpair] at h2
  · rintro ⟨e, b⟩
    cases b
    · rcases hpe : E.pair e.1 with ⟨C, k⟩
      refine ⟨⟨C, k⟩, ?_⟩
      show E.sideOf C k = (e, false)
      have ha : ¬E.orient ⟨C, k⟩ = true := by
        rw [← hpe, E.horient, e.2]
        simp
      unfold sideOf
      rw [dif_neg ha]
      refine Prod.ext ?_ rfl
      apply Subtype.ext
      show E.pair ⟨C, k⟩ = e.1
      rw [← hpe, E.hpair]
    · rcases he1 : e.1 with ⟨C, k⟩
      refine ⟨⟨C, k⟩, ?_⟩
      show E.sideOf C k = (e, true)
      have ha : E.orient ⟨C, k⟩ = true := he1 ▸ e.2
      unfold sideOf
      rw [dif_pos ha]
      refine Prod.ext ?_ rfl
      apply Subtype.ext
      show (⟨C, k⟩ : A.ArcIdx) = e.1
      exact he1.symm

end EdgeData
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.AssemblyData P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.EdgeData"

end CurveCellFamily
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.AssemblyData P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.EdgeData"

end Part_D1EdgeData
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.AssemblyData P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.EdgeData"

section Part_d1_count_g2

set_option autoImplicit false

noncomputable section

namespace CellCount
p2m_open "AlgebraicCurve~H1 P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily"

variable {F : Type*} [Field F] [Algebra ℂ F] [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

def J (A : AssemblyData F) : ℕ := (A.jhi - A.jlo + 1).toNat
private def _root_.CellCount.K (A : AssemblyData F) : ℕ := (A.khi - A.klo + 1).toNat
p2m_export "CellCount" "K"

def V₀ (A : AssemblyData F) : ℕ := (J A + 1) * (K A + 1) + J A * K A + K A

def Nperim (A : AssemblyData F) : ℕ := 2 * J A + 4 * K A

theorem card_Icc_J (A : AssemblyData F) : (Finset.Icc A.jlo A.jhi).card = J A := by
  exact (Int.card_Icc _ _).trans (congrArg Int.toNat (by ring))

theorem card_Icc_K (A : AssemblyData F) : (Finset.Icc A.klo A.khi).card = K A := by
  exact (Int.card_Icc _ _).trans (congrArg Int.toNat (by ring))

theorem win_toFinset (A : AssemblyData F) :
    A.win_finite.toFinset = Finset.Icc A.jlo A.jhi ×ˢ Finset.Icc A.klo A.khi := by
  ext p
  simp only [Set.Finite.mem_toFinset, AssemblyData.Win, Set.mem_prod, Set.mem_Icc,
      Finset.mem_product, Finset.mem_Icc]

theorem card_win (A : AssemblyData F) : A.win_finite.toFinset.card = J A * K A := by
  rw [win_toFinset A, Finset.card_product, card_Icc_J A, card_Icc_K A]

theorem plain_toFinset (A : AssemblyData F) :
    A.plain_finite.toFinset = A.win_finite.toFinset.filter (fun p => A.capAt p = none) := by
  ext p
  simp [A.mem_plain_iff]

theorem caps_toFinset (A : AssemblyData F) :
    A.caps_finite.toFinset = A.win_finite.toFinset.filter (fun p => ¬ A.capAt p = none) := by
  ext p
  simp [A.mem_caps_iff]

theorem card_plain_add_card_caps (A : AssemblyData F) :
    A.plain_finite.toFinset.card + A.caps_finite.toFinset.card = J A * K A := by
  rw [← card_win A, plain_toFinset A, caps_toFinset A]; exact Finset.card_filter_add_card_filter_not _

theorem card_arcIdx (A : AssemblyData F) (E : EdgeData A) :
    Fintype.card A.ArcIdx = 2 * Fintype.card E.IdxE := by
  have h := Fintype.card_of_bijective E.sideOf_bij
  rw [Fintype.card_prod, Fintype.card_bool] at h; omega

def idxCEquiv (A : AssemblyData F) :
    A.IdxC ≃ ((Σ _Q : A.plain_finite.toFinset, Fin A.n) ⊕
      ((Σ Q : A.caps_finite.toFinset, A.Fib (A.capVal Q)) ⊕ A.FibInf)) :=
  Equiv.refl _

def arcEquiv (A : AssemblyData F) : A.ArcIdx ≃ (Σ C : A.IdxC, Fin (A.cellOf C).R.N) :=
  Equiv.refl _

theorem sum_idxC {M : Type*} [AddCommMonoid M] (A : AssemblyData F) (f : A.IdxC → M) :
    ∑ C : A.IdxC, f C =
      (∑ Q : A.plain_finite.toFinset, ∑ i : Fin A.n, f (Sum.inl ⟨Q, i⟩)) +
        ((∑ Q : A.caps_finite.toFinset, ∑ w : A.Fib (A.capVal Q), f (Sum.inr (Sum.inl ⟨Q, w⟩))) +
          ∑ w : A.FibInf, f (Sum.inr (Sum.inr w))) := by
  refine (Fintype.sum_equiv (idxCEquiv A) f f (fun _ => rfl)).trans ?_; simp only [Fintype.sum_sum_type, Fintype.sum_sigma]

theorem card_arcIdx_eq_sum (A : AssemblyData F) :
    Fintype.card A.ArcIdx = ∑ C : A.IdxC, (A.cellOf C).R.N := by
  have h := Fintype.card_congr (arcEquiv A)
  simpa using h

theorem card_idxC (A : AssemblyData F) :
    Fintype.card A.IdxC =
      A.plain_finite.toFinset.card * A.n +
        ((∑ Q : A.caps_finite.toFinset, Fintype.card (A.Fib (A.capVal Q))) +
          Fintype.card A.FibInf) := by
  have h := Fintype.card_congr (idxCEquiv A); simpa using h

theorem euler (A : AssemblyData F) (E : EdgeData A) (g : ℤ)

    (ecap : ∀ Q : A.caps_finite.toFinset, A.Fib (A.capVal Q) → ℕ) (einf : A.FibInf → ℕ)

    (hN_plain : ∀ (Q : A.plain_finite.toFinset) (i : Fin A.n), (A.cellOf (Sum.inl ⟨Q, i⟩)).R.N = 6)
    (hN_cap : ∀ (Q : A.caps_finite.toFinset) (w : A.Fib (A.capVal Q)),
      (A.cellOf (Sum.inr (Sum.inl ⟨Q, w⟩))).R.N = 6 * ecap Q w)
    (hN_inf : ∀ w : A.FibInf, (A.cellOf (Sum.inr (Sum.inr w))).R.N = einf w * Nperim A)

    (hsum_cap : ∀ Q : A.caps_finite.toFinset, ∑ w : A.Fib (A.capVal Q), ecap Q w = A.n)
    (hsum_inf : ∑ w : A.FibInf, einf w = A.n)

    (hV : Fintype.card A.IdxV = A.n * V₀ A)

    (hRH : (∑ Q : A.caps_finite.toFinset, ∑ w : A.Fib (A.capVal Q), ((ecap Q w : ℤ) - 1))
        + ∑ w : A.FibInf, ((einf w : ℤ) - 1) = 2 * g - 2 + 2 * (A.n : ℤ)) :
    (Fintype.card A.IdxV : ℤ) - (Fintype.card E.IdxE : ℤ) + (Fintype.card A.IdxC : ℤ) = 2 - 2 * g := by

  have hW : A.plain_finite.toFinset.card + A.caps_finite.toFinset.card = J A * K A :=
    card_plain_add_card_caps A

  have hcount := AlgebraicCurve.CellDissection.euler_count_grid A.n (J A) (K A)
    A.plain_finite.toFinset.card A.caps_finite.toFinset.card g hW
    A.caps_finite.toFinset (Fintype.card_coe _) (fun Q => A.Fib (A.capVal Q)) ecap hsum_cap
    A.FibInf einf hsum_inf hRH

  have hV' : (Fintype.card A.IdxV : ℤ) = A.n * ((J A + 1) * (K A + 1) + J A * K A + K A) := by
    unfold V₀ at hV; exact_mod_cast hV

  have hX : (Fintype.card A.ArcIdx : ℤ) = 2 * (Fintype.card E.IdxE : ℤ) := by
    exact_mod_cast card_arcIdx A E

  have hAn : Fintype.card A.ArcIdx =
      6 * A.n * A.plain_finite.toFinset.card +
        (∑ Q : A.caps_finite.toFinset, ∑ w : A.Fib (A.capVal Q), 6 * ecap Q w) +
        ∑ w : A.FibInf, einf w * (2 * J A + 4 * K A) := by
    rw [card_arcIdx_eq_sum A, sum_idxC]
    simp only [hN_plain, hN_cap, hN_inf, Nperim, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Fintype.card_coe, smul_eq_mul]; ring1
  have hA : (Fintype.card A.ArcIdx : ℤ) =
      (6 * A.n * A.plain_finite.toFinset.card : ℤ) +
        (∑ Q : A.caps_finite.toFinset, ∑ w : A.Fib (A.capVal Q), (6 * ecap Q w : ℤ)) +
        ∑ w : A.FibInf, ((einf w : ℤ) * (2 * J A + 4 * K A)) := by
    exact_mod_cast hAn

  have hCn : Fintype.card A.IdxC =
      A.n * A.plain_finite.toFinset.card +
        (∑ Q : A.caps_finite.toFinset, Fintype.card (A.Fib (A.capVal Q))) + Fintype.card A.FibInf := by
    rw [card_idxC]; ring1
  have hC' : (Fintype.card A.IdxC : ℤ) =
      (A.n * A.plain_finite.toFinset.card : ℤ) +
        (∑ Q : A.caps_finite.toFinset, (Fintype.card (A.Fib (A.capVal Q)) : ℤ)) + Fintype.card A.FibInf := by
    exact_mod_cast hCn

  linarith

end CellCount
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.AssemblyData P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.EdgeData"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.AssemblyData P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.EdgeData"

end Part_d1_count_g2
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.AssemblyData P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.EdgeData"

section Part_D1Pair

set_option autoImplicit false

p2m_open "AlgebraicCurve~H1 Set P2MW.S_AlgebraicCurve_exists_pairedCellFamily.PlanarRegions P2MW.S_AlgebraicCurve_exists_pairedCellFamily.DissectionMaterials P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily P2MW.S_AlgebraicCurve_exists_pairedCellFamily.ArcPairing P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CellFacts"
open scoped Manifold ContDiff Topology Real

namespace CellPairing

p2m_open "AlgebraicCurve~H1 Set"

theorem exists_lap_of_pow_mem {R R' : RadialRegion} {e : ℕ} (he : e ≠ 0)
    {lap : Fin e → Fin R.N → Fin R'.N}
    (himg : ∀ (j : Fin e) (k : Fin R.N),
      (fun u : ℂ => R.q + u ^ e) '' R'.arcSet (lap j k) = R.arcSet k)
    (hsep : ∀ k : Fin R.N, ∃ U : Fin e → Set ℂ, (∀ j, IsOpen (U j)) ∧
      Pairwise (fun j j' => Disjoint (U j) (U j')) ∧ ∀ j, R'.arcSet (lap j k) ⊆ U j)
    {k : Fin R.N} {u : ℂ} (hu : R.q + u ^ e ∈ R.arcSet k) :
    ∃ j : Fin e, u ∈ R'.arcSet (lap j k) := by
  classical
  obtain ⟨U, -, hdisj, hUsub⟩ := hsep k
  have hroot : ∀ j : Fin e, ∃ v ∈ R'.arcSet (lap j k), R.q + v ^ e = R.q + u ^ e := by
    intro j
    have hu' : R.q + u ^ e ∈ (fun v : ℂ => R.q + v ^ e) '' R'.arcSet (lap j k) := by
      rw [himg j k]
      exact hu
    obtain ⟨v, hv, hveq⟩ := hu'
    exact ⟨v, hv, hveq⟩
  choose v hv hveq using hroot
  have hvinj : Function.Injective v := by
    intro j j' hjj'
    by_contra hne
    exact Set.disjoint_left.mp (hdisj hne) (hUsub j (hv j)) (hjj' ▸ hUsub j' (hv j'))
  have hpow : ∀ j, v j ^ e = u ^ e := fun j => add_left_cancel (hveq j)
  have hepos : 0 < e := Nat.pos_of_ne_zero he
  have himage : Finset.univ.image v ⊆ (Polynomial.nthRoots e (u ^ e)).toFinset := by
    intro z hz
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hz
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_nthRoots hepos).mpr (hpow j))
  have hcard : (Polynomial.nthRoots e (u ^ e)).toFinset.card ≤ (Finset.univ.image v).card := by
    rw [Finset.card_image_of_injective _ hvinj, Finset.card_univ, Fintype.card_fin]
    exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots e (u ^ e))
  have humem : u ∈ (Polynomial.nthRoots e (u ^ e)).toFinset :=
    Multiset.mem_toFinset.mpr ((Polynomial.mem_nthRoots hepos).mpr rfl)
  rw [← Finset.eq_of_subset_of_card_le himage hcard] at humem
  obtain ⟨j, -, hj⟩ := Finset.mem_image.mp humem
  exact ⟨j, hj ▸ hv j⟩

theorem loop_not_mem_Kint (R : RadialRegion) (φ : ℝ) : R.loop φ ∉ R.Kint := by
  intro h
  change ‖R.loop φ - R.q‖ < R.r (Complex.arg (R.loop φ - R.q)) at h
  have hφ : R.loop φ - R.q = ((R.r φ : ℝ) : ℂ) * Complex.exp (φ * Complex.I) := by
    unfold RadialRegion.loop
    ring
  rw [hφ, CellFacts.periodic_apply_arg R.hper (R.hpos φ), norm_mul, Complex.norm_exp_ofReal_mul_I,
    mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (R.hpos φ)] at h
  exact lt_irrefl _ h

theorem arcSet_not_mem_Kint (R : RadialRegion) (k : Fin R.N) {z : ℂ} (hz : z ∈ R.arcSet k) :
    z ∉ R.Kint := by
  obtain ⟨φ, -, rfl⟩ := hz
  exact loop_not_mem_Kint R φ

theorem efold_arcSet_injective {R R' : RadialRegion} {e : ℕ} {lap : Fin e → Fin R.N → Fin R'.N}
    (hbij : Function.Bijective (fun jk : Fin e × Fin R.N => lap jk.1 jk.2))
    (himg : ∀ (j : Fin e) (k : Fin R.N),
      (fun u : ℂ => R.q + u ^ e) '' R'.arcSet (lap j k) = R.arcSet k)
    (hsep : ∀ k : Fin R.N, ∃ U : Fin e → Set ℂ, (∀ j, IsOpen (U j)) ∧
      Pairwise (fun j j' => Disjoint (U j) (U j')) ∧ ∀ j, R'.arcSet (lap j k) ⊆ U j)
    (hbase : ∀ k k' : Fin R.N, R.arcSet k = R.arcSet k' → k = k') :
    ∀ a a' : Fin R'.N, R'.arcSet a = R'.arcSet a' → a = a' := by
  intro a a' haa'
  obtain ⟨⟨j, k⟩, rfl⟩ := hbij.2 a
  obtain ⟨⟨j', k'⟩, rfl⟩ := hbij.2 a'
  simp only at haa' ⊢

  have hk : k = k' := by
    apply hbase
    rw [← himg j k, ← himg j' k', haa']
  subst hk

  have hj : j = j' := by
    obtain ⟨U, -, hUd, hUsub⟩ := hsep k
    obtain ⟨u, hu⟩ := CellFacts.arcSet_nonempty R' (lap j k)
    by_contra hne
    exact Set.disjoint_left.mp (hUd hne) (hUsub j hu) (hUsub j' (haa' ▸ hu))
  subst hj
  rfl

theorem loop_add_int_mul (R : RadialRegion) (φ : ℝ) (j : ℤ) :
    R.loop (φ + j * (2 * π)) = R.loop φ := by
  unfold RadialRegion.loop
  rw [R.hper.int_mul j φ]
  congr 2
  push_cast
  rw [add_mul, Complex.exp_add]
  have h : Complex.exp ((j : ℂ) * (2 * (π : ℂ)) * Complex.I) = 1 := by
    rw [show (j : ℂ) * (2 * (π : ℂ)) * Complex.I = (j : ℂ) * (2 * (π : ℂ) * Complex.I) by ring]
    exact Complex.exp_int_mul_two_pi_mul_I j
  rw [h, mul_one]

theorem endpoints_of_image_mono {m c a b x y : ℝ} (hm : 0 < m) (hxy : x ≤ y)
    (h : Icc a b = (fun t : ℝ => m * t + c) '' Icc x y) : a = m * x + c ∧ b = m * y + c := by
  have himg : (fun t : ℝ => m * t + c) '' Icc x y = Icc (m * x + c) (m * y + c) := by
    ext s
    simp only [mem_image, mem_Icc]
    constructor
    · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
      exact ⟨by nlinarith, by nlinarith⟩
    · rintro ⟨h1, h2⟩
      refine ⟨(s - c) / m, ⟨?_, ?_⟩, ?_⟩
      · rw [le_div_iff₀ hm]; linarith
      · rw [div_le_iff₀ hm]; linarith
      · show m * ((s - c) / m) + c = s
        field_simp
        ring
  rw [himg] at h
  have hne : m * x + c ≤ m * y + c := by nlinarith
  have hab : a ≤ b := by
    have hne' : (Icc a b).Nonempty := by rw [h]; exact nonempty_Icc.mpr hne
    exact nonempty_Icc.mp hne'
  exact (Icc_eq_Icc_iff hab).mp h

theorem endpoints_of_image_anti {m c a b x y : ℝ} (hm : m < 0) (hxy : x ≤ y)
    (h : Icc a b = (fun t : ℝ => m * t + c) '' Icc x y) : a = m * y + c ∧ b = m * x + c := by
  have himg : (fun t : ℝ => m * t + c) '' Icc x y = Icc (m * y + c) (m * x + c) := by
    ext s
    simp only [mem_image, mem_Icc]
    constructor
    · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
      exact ⟨by nlinarith, by nlinarith⟩
    · rintro ⟨h1, h2⟩
      refine ⟨(s - c) / m, ⟨?_, ?_⟩, ?_⟩
      · rw [le_div_iff_of_neg hm]; linarith
      · rw [div_le_iff_of_neg hm]; linarith
      · show m * ((s - c) / m) + c = s
        have hm0 : m ≠ 0 := hm.ne
        field_simp
        ring
  rw [himg] at h
  have hne : m * y + c ≤ m * x + c := by nlinarith
  have hab : a ≤ b := by
    have hne' : (Icc a b).Nonempty := by rw [h]; exact nonempty_Icc.mpr hne
    exact nonempty_Icc.mp hne'
  exact (Icc_eq_Icc_iff hab).mp h

theorem affine_inv_apply {m c : ℝ} (hm : m ≠ 0) (t : ℝ) : (m * t + c - c) / m = t := by
  field_simp
  ring

theorem affine_apply_inv {m c : ℝ} (hm : m ≠ 0) (u : ℝ) : m * ((u - c) / m) + c = u := by
  field_simp
  ring

theorem contDiffOn_affine_inv (m c : ℝ) (s : Set ℝ) : ContDiffOn ℝ 1 (fun u : ℝ => (u - c) / m) s :=
  ((contDiff_id.sub contDiff_const).div_const m).contDiffOn

theorem strictMono_affine_inv {m c : ℝ} (hm : 0 < m) : StrictMono fun u : ℝ => (u - c) / m :=
  fun _ _ h => by
    show _ / m < _ / m
    exact div_lt_div_of_pos_right (by linarith) hm

theorem strictAnti_affine_inv {m c : ℝ} (hm : m < 0) : StrictAnti fun u : ℝ => (u - c) / m :=
  fun _ _ h => by
    show _ / m < _ / m
    exact div_lt_div_of_neg_of_lt hm (by linarith)

theorem affine_mapsTo_pos {m c u₀ u₁ : ℝ} (hm : 0 < m) :
    MapsTo (fun t : ℝ => m * t + c) (Icc u₀ u₁) (Icc (m * u₀ + c) (m * u₁ + c)) := by
  intro t ht
  exact ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩

theorem affine_mapsTo_neg {m c u₀ u₁ : ℝ} (hm : m < 0) :
    MapsTo (fun t : ℝ => m * t + c) (Icc u₀ u₁) (Icc (m * u₁ + c) (m * u₀ + c)) := by
  intro t ht
  exact ⟨by nlinarith [ht.2], by nlinarith [ht.1]⟩

theorem affine_inv_mapsTo_pos {m c u₀ u₁ : ℝ} (hm : 0 < m) :
    MapsTo (fun u : ℝ => (u - c) / m) (Icc (m * u₀ + c) (m * u₁ + c)) (Icc u₀ u₁) := by
  intro u hu
  constructor
  · rw [le_div_iff₀ hm]; linarith [hu.1]
  · rw [div_le_iff₀ hm]; linarith [hu.2]

theorem affine_inv_mapsTo_neg {m c u₀ u₁ : ℝ} (hm : m < 0) :
    MapsTo (fun u : ℝ => (u - c) / m) (Icc (m * u₁ + c) (m * u₀ + c)) (Icc u₀ u₁) := by
  intro u hu
  constructor
  · rw [le_div_iff_of_neg hm]; linarith [hu.2]
  · rw [div_le_iff_of_neg hm]; linarith [hu.1]

theorem mapsTo_Icc_of_strictAntiOn {ψ : ℝ → ℝ} {x y : ℝ} (hxy : x ≤ y) (h : StrictAntiOn ψ (Icc x y)) :
    MapsTo ψ (Icc x y) (Icc (ψ y) (ψ x)) := by
  intro t ht
  have hx : x ∈ Icc x y := ⟨le_rfl, hxy⟩
  have hy : y ∈ Icc x y := ⟨hxy, le_rfl⟩
  exact ⟨h.antitoneOn ht hy ht.2, h.antitoneOn hx ht ht.1⟩

theorem mapsTo_Icc_of_strictMonoOn {ψ : ℝ → ℝ} {x y : ℝ} (hxy : x ≤ y) (h : StrictMonoOn ψ (Icc x y)) :
    MapsTo ψ (Icc x y) (Icc (ψ x) (ψ y)) := by
  intro t ht
  have hx : x ∈ Icc x y := ⟨le_rfl, hxy⟩
  have hy : y ∈ Icc x y := ⟨hxy, le_rfl⟩
  exact ⟨h.monotoneOn hx ht ht.1, h.monotoneOn ht hy ht.2⟩

theorem strictAntiOn_comp_mono {f g : ℝ → ℝ} {s t : Set ℝ} (hf : StrictMonoOn f s) (hfs : MapsTo f s t)
    (hg : StrictAntiOn g t) : StrictAntiOn (fun x => g (f x)) s :=
  fun _ ha _ hb hab => hg (hfs ha) (hfs hb) (hf ha hb hab)

theorem strictAntiOn_comp_anti {f g : ℝ → ℝ} {s t : Set ℝ} (hf : StrictAntiOn f s) (hfs : MapsTo f s t)
    (hg : StrictMonoOn g t) : StrictAntiOn (fun x => g (f x)) s :=
  fun _ ha _ hb hab => hg (hfs hb) (hfs ha) (hf ha hb hab)

theorem strictMonoOn_comp_mono {f g : ℝ → ℝ} {s t : Set ℝ} (hf : StrictMonoOn f s) (hfs : MapsTo f s t)
    (hg : StrictMonoOn g t) : StrictMonoOn (fun x => g (f x)) s :=
  fun _ ha _ hb hab => hg (hfs ha) (hfs hb) (hf ha hb hab)

theorem strictMonoOn_affine_pos {m c : ℝ} (hm : 0 < m) (s : Set ℝ) :
    StrictMonoOn (fun t : ℝ => m * t + c) s :=
  fun _ _ _ _ hab => by
    show m * _ + c < m * _ + c
    nlinarith

theorem strictAntiOn_affine_neg {m c : ℝ} (hm : m < 0) (s : Set ℝ) :
    StrictAntiOn (fun t : ℝ => m * t + c) s :=
  fun _ _ _ _ hab => by
    show m * _ + c < m * _ + c
    nlinarith

theorem contDiffOn_affine (m c : ℝ) (s : Set ℝ) : ContDiffOn ℝ 1 (fun t : ℝ => m * t + c) s :=
  ((contDiff_const.mul contDiff_id).add contDiff_const).contDiffOn

theorem contDiffOn_comp₃ {α' ψ₀ β : ℝ → ℝ} {s t : Set ℝ} (hα' : ContDiffOn ℝ 1 α' s) (hmaps : MapsTo α' s t)
    (hψ₀ : ContDiffOn ℝ 1 ψ₀ t) (hβ : ContDiffOn ℝ 1 β univ) :
    ContDiffOn ℝ 1 (fun x => β (ψ₀ (α' x))) s :=
  (hβ.comp (hψ₀.comp hα' hmaps) (mapsTo_univ _ _))

theorem arcIcc_eq (R : RadialRegion) (k : Fin R.N) : R.arcIcc k = Icc (R.φs k.castSucc) (R.φs k.succ) := rfl

end CellPairing
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.AssemblyData P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.EdgeData"

namespace DissectionMaterials
namespace Materials

variable {F : Type*} [Field F] [Algebra ℂ F] [TopologicalSpace (Place ℂ F)]
variable [ChartedSpace ℂ (Place ℂ F)]
variable {S : Finset (Place ℂ F)} {P₀ : Place ℂ F}
variable (M : Materials F S P₀) [Planar] [IsCurveOver ℂ F] [T2Space (Place ℂ F)]
variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]
variable (hF : OrdPack F) (hrat : ∀ P : Place ℂ F, P.IsRational)

theorem arc_inl (Q : (M.toAssembly hF hrat).plain_finite.toFinset) (i : Fin M.n)
    (k : Fin (M.base Q.1).N) :
    ((M.toAssembly hF hrat).cellOf (Sum.inl ⟨Q, i⟩)).arc k =
      {P | P ∈ (M.sheet Q.1 i).source ∧ Place.evalAt P M.x ∈ (M.base Q.1).arcSet k} := by
  have hQ := (M.toAssembly hF hrat).mem_plain_iff.mp
    ((M.toAssembly hF hrat).plain_finite.mem_toFinset.mp Q.2)
  have hfam := M.hsheet Q.1 hQ.1 hQ.2
  rw [arc_eq]
  ext P
  simp only [mem_setOf_eq]
  show P ∈ (M.sheet Q.1 i).source ∧ M.sheet Q.1 i P ∈ (M.base Q.1).arcSet k ↔ _
  constructor
  · rintro ⟨hP, hz⟩
    exact ⟨hP, by rwa [← (hfam.forward i P hP).2]⟩
  · rintro ⟨hP, hz⟩
    exact ⟨hP, by rwa [(hfam.forward i P hP).2]⟩

theorem existsUnique_sheet_arc (Q : (M.toAssembly hF hrat).plain_finite.toFinset)
    (k : Fin (M.base Q.1).N) {A : Set (Place ℂ F)} (hA : IsPreconnected A) (hne : A.Nonempty)
    (hover : ∀ P ∈ A, M.x ∈ P.toValuationSubring ∧ Place.evalAt P M.x ∈ (M.base Q.1).arcSet k)
    (honto : (M.base Q.1).arcSet k ⊆ (fun P => Place.evalAt P M.x) '' A) :
    ∃! i : Fin M.n, A = ((M.toAssembly hF hrat).cellOf (Sum.inl ⟨Q, i⟩)).arc k := by
  have hQ := (M.toAssembly hF hrat).mem_plain_iff.mp
    ((M.toAssembly hF hrat).plain_finite.mem_toFinset.mp Q.2)
  have hfam := M.hsheet Q.1 hQ.1 hQ.2

  have hseg : ∀ z ∈ (M.base Q.1).arcSet k, z ∈ M.margin Q.1 := by
    intro z hz
    have hzK : z ∈ (M.base Q.1).K := arcSet_subset_K _ k hz
    rw [base_K] at hzK
    exact M.hmargin_sq Q.1 hQ.1 hQ.2 hzK

  have hcov : A ⊆ ⋃ i, (M.sheet Q.1 i).source := by
    intro P hP
    obtain ⟨hxP, hz⟩ := hover P hP
    obtain ⟨i, hi⟩ := hfam.exhaust P hxP (hseg _ hz)
    exact mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨i, hAi⟩ := exists_subset_of_isPreconnected hA hne (fun i => (M.sheet Q.1 i).open_source)
    hfam.disjoint hcov
  have hsub : A ⊆ ((M.toAssembly hF hrat).cellOf (Sum.inl ⟨Q, i⟩)).arc k := by
    intro P hP
    rw [arc_inl]
    exact ⟨hAi hP, (hover P hP).2⟩
  have hinj : InjOn (fun P => Place.evalAt P M.x)
      (((M.toAssembly hF hrat).cellOf (Sum.inl ⟨Q, i⟩)).arc k) := by
    intro P hP P' hP' hPP'
    rw [arc_inl] at hP hP'
    apply (M.sheet Q.1 i).injOn hP.1 hP'.1
    rw [(hfam.forward i P hP.1).2, (hfam.forward i P' hP'.1).2]
    exact hPP'
  have himg : (fun P => Place.evalAt P M.x) '' ((M.toAssembly hF hrat).cellOf (Sum.inl ⟨Q, i⟩)).arc k
      ⊆ (fun P => Place.evalAt P M.x) '' A := by
    rintro _ ⟨P, hP, rfl⟩
    rw [arc_inl] at hP
    exact honto hP.2
  refine ⟨i, eq_of_image_subset_of_injOn hsub himg hinj, ?_⟩
  intro j hj
  obtain ⟨P, hP⟩ := hne
  have hPj : P ∈ (M.sheet Q.1 j).source := by
    have h := hj ▸ hP
    rw [arc_inl] at h
    exact h.1
  by_contra hji
  exact Set.disjoint_left.mp (hfam.disjoint hji) hPj (hAi hP)

omit [Planar] [IsCurveOver ℂ F] [T2Space (Place ℂ F)] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem cape_ne_zero {b : ℂ} (hb : b ∈ M.Bad) {w : Place ℂ F} (hxw : M.x ∈ w.toValuationSubring)
    (hwb : Place.evalAt w M.x = b) : M.cape b w ≠ 0 :=
  (M.hcapchart b hb w hxw hwb).e_pos.ne'

omit [Planar] [IsCurveOver ℂ F] [T2Space (Place ℂ F)] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem infe_ne_zero {w : Place ℂ F} (hw : M.x ∉ w.toValuationSubring) : M.infe w ≠ 0 :=
  (M.hinfchart w hw).e_pos.ne'

omit [IsCurveOver ℂ F] [T2Space (Place ℂ F)] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem capRegion_laps (p : ℤ × ℤ) {b : ℂ} {w : Place ℂ F} (h : M.cape b w ≠ 0) :
    EfoldClauses (M.base p) (M.two_le_base_N p) (M.cape b w) h (M.capRegion p b w) ∧
      ∃ lap : Fin (M.cape b w) → Fin (M.base p).N → Fin (M.capRegion p b w).N,
        LapClauses (M.base p) (M.two_le_base_N p) (M.cape b w) h (M.capRegion p b w) lap := by
  have key : ∀ R' : RadialRegion,
      R' = Planar.efold (M.base p) (M.two_le_base_N p) (M.cape b w) h →
      EfoldClauses (M.base p) (M.two_le_base_N p) (M.cape b w) h R' ∧
        ∃ lap : Fin (M.cape b w) → Fin (M.base p).N → Fin R'.N,
          LapClauses (M.base p) (M.two_le_base_N p) (M.cape b w) h R' lap := by
    rintro _ rfl
    exact ⟨Planar.efold_spec _ _ _ _, Planar.lap _ _ _ _, Planar.lap_spec _ _ _ _⟩
  exact key _ (M.capRegion_eq h)

omit [IsCurveOver ℂ F] [T2Space (Place ℂ F)] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem infRegion_laps {w : Place ℂ F} (h : M.infe w ≠ 0) :
    EfoldClauses M.infBase M.two_le_infBase_N (M.infe w) h (M.infRegion w) ∧
      ∃ lap : Fin (M.infe w) → Fin M.infBase.N → Fin (M.infRegion w).N,
        LapClauses M.infBase M.two_le_infBase_N (M.infe w) h (M.infRegion w) lap := by
  have key : ∀ R' : RadialRegion, R' = Planar.efold M.infBase M.two_le_infBase_N (M.infe w) h →
      EfoldClauses M.infBase M.two_le_infBase_N (M.infe w) h R' ∧
        ∃ lap : Fin (M.infe w) → Fin M.infBase.N → Fin R'.N,
          LapClauses M.infBase M.two_le_infBase_N (M.infe w) h R' lap := by
    rintro _ rfl
    exact ⟨Planar.efold_spec _ _ _ _, Planar.lap _ _ _ _, Planar.lap_spec _ _ _ _⟩
  exact key _ (M.infRegion_eq h)

theorem arc_cap (Q : (M.toAssembly hF hrat).caps_finite.toFinset)
    (w : (M.toAssembly hF hrat).Fib ((M.toAssembly hF hrat).capVal Q))
    (k : Fin ((M.toAssembly hF hrat).cellOf (Sum.inr (Sum.inl ⟨Q, w⟩))).R.N) :
    ((M.toAssembly hF hrat).cellOf (Sum.inr (Sum.inl ⟨Q, w⟩))).arc k =
      {P | P ∈ (M.capζ ((M.toAssembly hF hrat).capVal Q) w.1).source ∧
        M.capζ ((M.toAssembly hF hrat).capVal Q) w.1 P ∈
          (M.capRegion Q.1 ((M.toAssembly hF hrat).capVal Q) w.1).arcSet k} :=
  arc_eq ((M.toAssembly hF hrat).cellOf (Sum.inr (Sum.inl ⟨Q, w⟩))) k

theorem arc_inf (w : (M.toAssembly hF hrat).FibInf)
    (k : Fin ((M.toAssembly hF hrat).cellOf (Sum.inr (Sum.inr w))).R.N) :
    ((M.toAssembly hF hrat).cellOf (Sum.inr (Sum.inr w))).arc k =
      {P | P ∈ (M.infζ w.1).source ∧ M.infζ w.1 P ∈ (M.infRegion w.1).arcSet k} :=
  arc_eq ((M.toAssembly hF hrat).cellOf (Sum.inr (Sum.inr w))) k

theorem capVal_facts (Q : (M.toAssembly hF hrat).caps_finite.toFinset) :
    (M.toAssembly hF hrat).capVal Q ∈ M.Bad ∧
      M.capAt Q.1 = some ((M.toAssembly hF hrat).capVal Q) ∧
      M.ctr Q.1 = (M.toAssembly hF hrat).capVal Q ∧
      (M.toAssembly hF hrat).capVal Q ∈ PlaneGrid.gridSquare M.o M.hm Q.1.1 Q.1.2 := by
  have hQ := ((M.toAssembly hF hrat).mem_caps_iff.mp
    ((M.toAssembly hF hrat).caps_finite.mem_toFinset.mp Q.2)).2
  obtain ⟨b', hb', hQb', hgetD⟩ := M.exists_capAt_eq hQ
  have hval : (M.toAssembly hF hrat).capVal Q = b' := hgetD
  rw [hval]
  refine ⟨hb', hQb', by simp [ctr, hQb'], ?_⟩
  rw [gridSquare_eq]
  have h := M.bad_mem_of_capAt hQb'
  exact ⟨⟨h.1.1.le, h.1.2.le⟩, h.2.1.le, h.2.2.le⟩

theorem exists_cap_arc (Q : (M.toAssembly hF hrat).caps_finite.toFinset) (k : Fin (M.base Q.1).N)
    {A : Set (Place ℂ F)} (hA : IsPreconnected A) (hne : A.Nonempty)
    (hover : ∀ P ∈ A, M.x ∈ P.toValuationSubring ∧ Place.evalAt P M.x ∈ (M.base Q.1).arcSet k)
    (honto : (M.base Q.1).arcSet k ⊆ (fun P => Place.evalAt P M.x) '' A) :
    ∃ (w : (M.toAssembly hF hrat).Fib ((M.toAssembly hF hrat).capVal Q))
      (k' : Fin ((M.toAssembly hF hrat).cellOf (Sum.inr (Sum.inl ⟨Q, w⟩))).R.N),
      A = ((M.toAssembly hF hrat).cellOf (Sum.inr (Sum.inl ⟨Q, w⟩))).arc k' := by
  obtain ⟨hb, hQb, hctr, hbsq⟩ := M.capVal_facts hF hrat Q

  have hclose : ∀ P ∈ A, ‖Place.evalAt P M.x - ((M.toAssembly hF hrat).capVal Q)‖ < 2 * M.cs ((M.toAssembly hF hrat).capVal Q) := by
    intro P hP
    have hz : Place.evalAt P M.x ∈ PlaneGrid.gridSquare M.o M.hm Q.1.1 Q.1.2 := by
      have h := arcSet_subset_K _ k (hover P hP).2
      rwa [base_K] at h
    have h1 := M.norm_sub_le_of_mem_gridSquare hz hbsq
    have h2 := M.hcs ((M.toAssembly hF hrat).capVal Q) hb
    have h3 := M.hhm
    linarith

  have hcov : A ⊆ ⋃ w : (M.toAssembly hF hrat).Fib ((M.toAssembly hF hrat).capVal Q), (M.capζ ((M.toAssembly hF hrat).capVal Q) w.1).source := by
    intro P hP
    obtain ⟨w, hxw, hwb, hPw⟩ := M.hcapexhaust ((M.toAssembly hF hrat).capVal Q) hb P (hover P hP).1 (hclose P hP)
    exact mem_iUnion.mpr ⟨⟨w, hxw, hwb⟩, hPw⟩
  have hdisj : Pairwise fun w w' : (M.toAssembly hF hrat).Fib ((M.toAssembly hF hrat).capVal Q) =>
      Disjoint (M.capζ ((M.toAssembly hF hrat).capVal Q) w.1).source (M.capζ ((M.toAssembly hF hrat).capVal Q) w'.1).source := by
    intro w w' hww'
    exact M.hcapdisj ((M.toAssembly hF hrat).capVal Q) hb w.1 w'.1 w.2.1 w.2.2 w'.2.1 w'.2.2 fun h => hww' (Subtype.ext h)
  obtain ⟨w, hAw⟩ := exists_subset_of_isPreconnected hA hne
    (fun w : (M.toAssembly hF hrat).Fib ((M.toAssembly hF hrat).capVal Q) => (M.capζ ((M.toAssembly hF hrat).capVal Q) w.1).open_source) hdisj hcov

  have he : M.cape ((M.toAssembly hF hrat).capVal Q) w.1 ≠ 0 := M.cape_ne_zero hb w.2.1 w.2.2
  obtain ⟨-, lap, hlap⟩ := M.capRegion_laps Q.1 he
  obtain ⟨-, -, himg, hinjlap, hsep⟩ := hlap
  have hq : (M.base Q.1).q = ((M.toAssembly hF hrat).capVal Q) := by rw [base_q, hctr]

  have hlapmem : ∀ P ∈ A, ∃ j : Fin (M.cape ((M.toAssembly hF hrat).capVal Q) w.1),
      M.capζ ((M.toAssembly hF hrat).capVal Q) w.1 P ∈ (M.capRegion Q.1 ((M.toAssembly hF hrat).capVal Q) w.1).arcSet (lap j k) := by
    intro P hP
    have hx := (M.evalAt_eq_of_mem_capζ hrat hb w.2.1 w.2.2 (hAw hP)).2
    have hmem : (M.base Q.1).q + (M.capζ ((M.toAssembly hF hrat).capVal Q) w.1 P) ^ M.cape ((M.toAssembly hF hrat).capVal Q) w.1 ∈ (M.base Q.1).arcSet k := by
      rw [hq, ← hx]
      exact (hover P hP).2
    exact CellPairing.exists_lap_of_pow_mem he himg hsep hmem

  obtain ⟨U, hUo, hUd, hUsub⟩ := hsep k
  have himA : IsPreconnected (M.capζ ((M.toAssembly hF hrat).capVal Q) w.1 '' A) :=
    hA.image _ ((M.capζ ((M.toAssembly hF hrat).capVal Q) w.1).continuousOn.mono hAw)
  have himA_ne : (M.capζ ((M.toAssembly hF hrat).capVal Q) w.1 '' A).Nonempty := hne.image _
  have himA_cov : M.capζ ((M.toAssembly hF hrat).capVal Q) w.1 '' A ⊆ ⋃ j, U j := by
    rintro _ ⟨P, hP, rfl⟩
    obtain ⟨j, hj⟩ := hlapmem P hP
    exact mem_iUnion.mpr ⟨j, hUsub j hj⟩
  obtain ⟨j₀, hj₀⟩ := exists_subset_of_isPreconnected himA himA_ne hUo hUd himA_cov
  have hsub : A ⊆ ((M.toAssembly hF hrat).cellOf (Sum.inr (Sum.inl ⟨Q, w⟩))).arc (lap j₀ k) := by
    intro P hP
    rw [arc_cap]
    refine ⟨hAw hP, ?_⟩
    obtain ⟨j, hj⟩ := hlapmem P hP
    have hjj₀ : j = j₀ := by
      by_contra hjne
      exact Set.disjoint_left.mp (hUd hjne) (hUsub j hj) (hj₀ ⟨P, hP, rfl⟩)
    rw [hjj₀] at hj
    exact hj

  have hread : ∀ P ∈ ((M.toAssembly hF hrat).cellOf (Sum.inr (Sum.inl ⟨Q, w⟩))).arc (lap j₀ k),
      Place.evalAt P M.x = (M.base Q.1).q + (M.capζ ((M.toAssembly hF hrat).capVal Q) w.1 P) ^ M.cape ((M.toAssembly hF hrat).capVal Q) w.1 := by
    intro P hP
    rw [arc_cap] at hP
    rw [hq]
    exact (M.evalAt_eq_of_mem_capζ hrat hb w.2.1 w.2.2 hP.1).2
  have himg' : (fun P => Place.evalAt P M.x) ''
      ((M.toAssembly hF hrat).cellOf (Sum.inr (Sum.inl ⟨Q, w⟩))).arc (lap j₀ k) ⊆
        (fun P => Place.evalAt P M.x) '' A := by
    rintro _ ⟨P, hP, rfl⟩
    apply honto
    have hP' := hP
    rw [arc_cap] at hP'
    rw [← himg j₀ k]
    exact ⟨_, hP'.2, (hread P hP).symm⟩
  have hinj : InjOn (fun P => Place.evalAt P M.x)
      (((M.toAssembly hF hrat).cellOf (Sum.inr (Sum.inl ⟨Q, w⟩))).arc (lap j₀ k)) := by
    intro P hP P' hP' hPP'
    have h1 := hread P hP
    have h2 := hread P' hP'
    rw [arc_cap] at hP hP'
    apply (M.capζ ((M.toAssembly hF hrat).capVal Q) w.1).injOn hP.1 hP'.1
    apply hinjlap j₀ k hP.2 hP'.2
    show (M.base Q.1).q + (M.capζ ((M.toAssembly hF hrat).capVal Q) w.1 P) ^ M.cape ((M.toAssembly hF hrat).capVal Q) w.1 =
      (M.base Q.1).q + (M.capζ ((M.toAssembly hF hrat).capVal Q) w.1 P') ^ M.cape ((M.toAssembly hF hrat).capVal Q) w.1
    rw [← h1, ← h2]
    exact hPP'
  exact ⟨w, lap j₀ k, eq_of_image_subset_of_injOn hsub himg' hinj⟩

noncomputable def infIdx : Fin M.winReg.N ≃ Fin M.infBase.N := Planar.recipIdx M.winReg M.winReg_q

omit [IsCurveOver ℂ F] [T2Space (Place ℂ F)] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem infIdx_spec : RecipIdxClauses M.winReg M.winReg_q M.infBase (M.infIdx) :=
  Planar.recipIdx_spec M.winReg M.winReg_q

omit [IsCurveOver ℂ F] [T2Space (Place ℂ F)] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem Rw_lt_norm_of_mem_perimeter {k₀ : Fin M.winReg.N} {z : ℂ} (hz : z ∈ M.winReg.arcSet k₀) :
    M.Rw < ‖z‖ := by
  by_contra h
  push Not at h
  apply CellPairing.arcSet_not_mem_Kint M.winReg k₀ hz
  rw [winReg_Kint]
  exact M.hwin z h

omit [IsCurveOver ℂ F] [T2Space (Place ℂ F)] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem x_mem_of_mem_inf_arc {w : Place ℂ F} (hw : M.x ∉ w.toValuationSubring)
    {k : Fin (M.infRegion w).N} {P : Place ℂ F} (hP : P ∈ (M.infζ w).source)
    (hPk : M.infζ w P ∈ (M.infRegion w).arcSet k) : M.x ∈ P.toValuationSubring := by
  by_contra hxP
  have he : M.infe w ≠ 0 := M.infe_ne_zero hw
  have hPw : P = w := M.eq_of_mem_infζ_source hw hxP hP
  have hcentre : M.infζ w P = 0 := by rw [hPw]; exact (M.hinfchart w hw).centre
  have h0 : (0 : ℂ) ∈ (M.infRegion w).arcSet k := hcentre ▸ hPk
  apply CellPairing.arcSet_not_mem_Kint _ k h0
  obtain ⟨-, -, -, hKint, -⟩ := (M.infRegion_laps he).1
  rw [hKint, M.infBase_q, zero_add, zero_pow he]
  exact M.infBase_spec.2.2.1

theorem exists_pole_arc (k₀ : Fin M.winReg.N) {A : Set (Place ℂ F)} (hA : IsPreconnected A)
    (hne : A.Nonempty)
    (hover : ∀ P ∈ A, M.x ∈ P.toValuationSubring ∧ Place.evalAt P M.x ∈ M.winReg.arcSet k₀)
    (honto : M.winReg.arcSet k₀ ⊆ (fun P => Place.evalAt P M.x) '' A) :
    ∃ (w : (M.toAssembly hF hrat).FibInf)
      (k' : Fin ((M.toAssembly hF hrat).cellOf (Sum.inr (Sum.inr w))).R.N),
      A = ((M.toAssembly hF hrat).cellOf (Sum.inr (Sum.inr w))).arc k' := by

  have hcov : A ⊆ ⋃ w : (M.toAssembly hF hrat).FibInf, (M.infζ w.1).source := by
    intro P hP
    obtain ⟨w, hw, hPw⟩ :=
      M.hinfexhaust P (hover P hP).1 (M.Rw_lt_norm_of_mem_perimeter (hover P hP).2).le
    exact mem_iUnion.mpr ⟨⟨w, hw⟩, hPw⟩
  have hdisj : Pairwise fun w w' : (M.toAssembly hF hrat).FibInf =>
      Disjoint (M.infζ w.1).source (M.infζ w'.1).source := by
    intro w w' hww'
    exact M.hinfdisj w.1 w'.1 w.2 w'.2 fun h => hww' (Subtype.ext h)
  obtain ⟨w, hAw⟩ := exists_subset_of_isPreconnected hA hne
    (fun w : (M.toAssembly hF hrat).FibInf => (M.infζ w.1).open_source) hdisj hcov

  have he : M.infe w.1 ≠ 0 := M.infe_ne_zero w.2
  obtain ⟨-, lap, hlap⟩ := M.infRegion_laps he
  obtain ⟨-, -, himg, hinjlap, hsep⟩ := hlap
  have hq : M.infBase.q = 0 := M.infBase_q
  have hrecip := M.infIdx_spec.2 k₀

  have hval : ∀ P ∈ (M.infζ w.1).source, M.x ∈ P.toValuationSubring →
      Place.evalAt P M.x ≠ 0 ∧
        M.infBase.q + (M.infζ w.1 P) ^ M.infe w.1 = (Place.evalAt P M.x)⁻¹ := by
    intro P hP hxP
    obtain ⟨hne0, hinv⟩ := M.evalAt_of_mem_infζ hrat w.2 hP hxP
    exact ⟨hne0, by rw [hq, zero_add, hinv]⟩
  have hlapmem : ∀ P ∈ A, ∃ j : Fin (M.infe w.1),
      M.infζ w.1 P ∈ (M.infRegion w.1).arcSet (lap j (M.infIdx k₀)) := by
    intro P hP
    obtain ⟨hxP, hz⟩ := hover P hP
    obtain ⟨-, hread⟩ := hval P (hAw hP) hxP
    have hmem : M.infBase.q + (M.infζ w.1 P) ^ M.infe w.1 ∈ M.infBase.arcSet (M.infIdx k₀) := by
      rw [hread]
      rw [← hrecip] at hz
      obtain ⟨v, hv, hvz⟩ := hz
      have hvz' : v⁻¹ = Place.evalAt P M.x := hvz
      rw [← hvz', inv_inv]
      exact hv
    exact CellPairing.exists_lap_of_pow_mem he himg hsep hmem
  obtain ⟨U, hUo, hUd, hUsub⟩ := hsep (M.infIdx k₀)
  have himA : IsPreconnected (M.infζ w.1 '' A) :=
    hA.image _ ((M.infζ w.1).continuousOn.mono hAw)
  have himA_cov : M.infζ w.1 '' A ⊆ ⋃ j, U j := by
    rintro _ ⟨P, hP, rfl⟩
    obtain ⟨j, hj⟩ := hlapmem P hP
    exact mem_iUnion.mpr ⟨j, hUsub j hj⟩
  obtain ⟨j₀, hj₀⟩ := exists_subset_of_isPreconnected himA (hne.image _) hUo hUd himA_cov
  set k' := lap j₀ (M.infIdx k₀)
  have hsub : A ⊆ ((M.toAssembly hF hrat).cellOf (Sum.inr (Sum.inr w))).arc k' := by
    intro P hP
    rw [arc_inf]
    refine ⟨hAw hP, ?_⟩
    obtain ⟨j, hj⟩ := hlapmem P hP
    have hjj₀ : j = j₀ := by
      by_contra hjne
      exact Set.disjoint_left.mp (hUd hjne) (hUsub j hj) (hj₀ ⟨P, hP, rfl⟩)
    rw [hjj₀] at hj
    exact hj

  have harc_x : ∀ P ∈ ((M.toAssembly hF hrat).cellOf (Sum.inr (Sum.inr w))).arc k',
      M.x ∈ P.toValuationSubring := by
    intro P hP
    rw [arc_inf] at hP
    exact M.x_mem_of_mem_inf_arc w.2 hP.1 hP.2
  have hread : ∀ P ∈ ((M.toAssembly hF hrat).cellOf (Sum.inr (Sum.inr w))).arc k',
      Place.evalAt P M.x = (M.infBase.q + (M.infζ w.1 P) ^ M.infe w.1)⁻¹ := by
    intro P hP
    have hxP := harc_x P hP
    rw [arc_inf] at hP
    obtain ⟨-, h⟩ := hval P hP.1 hxP
    rw [h, inv_inv]
  have himg' : (fun P => Place.evalAt P M.x) ''
      ((M.toAssembly hF hrat).cellOf (Sum.inr (Sum.inr w))).arc k' ⊆
        (fun P => Place.evalAt P M.x) '' A := by
    rintro _ ⟨P, hP, rfl⟩
    apply honto
    have hP' := hP
    rw [arc_inf] at hP'
    rw [← hrecip, ← himg j₀ (M.infIdx k₀)]
    exact ⟨_, ⟨_, hP'.2, rfl⟩, (hread P hP).symm⟩
  have hinj : InjOn (fun P => Place.evalAt P M.x)
      (((M.toAssembly hF hrat).cellOf (Sum.inr (Sum.inr w))).arc k') := by
    intro P hP P' hP' hPP'
    have h1 := hread P hP
    have h2 := hread P' hP'
    rw [arc_inf] at hP hP'
    apply (M.infζ w.1).injOn hP.1 hP'.1
    apply hinjlap j₀ (M.infIdx k₀) hP.2 hP'.2
    show M.infBase.q + (M.infζ w.1 P) ^ M.infe w.1 = M.infBase.q + (M.infζ w.1 P') ^ M.infe w.1
    have h : (M.infBase.q + (M.infζ w.1 P) ^ M.infe w.1)⁻¹ =
        (M.infBase.q + (M.infζ w.1 P') ^ M.infe w.1)⁻¹ := by
      rw [← h1, ← h2]
      exact hPP'
    exact inv_injective h
  exact ⟨w, k', eq_of_image_subset_of_injOn hsub himg' hinj⟩

def regionOf : (M.toAssembly hF hrat).IdxC → Option (ℤ × ℤ)
  | .inl ⟨Q, _⟩ => some Q.1
  | .inr (.inl ⟨Q, _⟩) => some Q.1
  | .inr (.inr _) => none

abbrev ArcOf : Type _ :=
  Σ C : (M.toAssembly hF hrat).IdxC, Fin ((M.toAssembly hF hrat).cellOf C).R.N

def arcPlaces (a : M.ArcOf hF hrat) : Set (Place ℂ F) :=
  ((M.toAssembly hF hrat).cellOf a.1).arc a.2

omit [Planar] [IsCurveOver ℂ F] [T2Space (Place ℂ F)] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem arc_index_eq {C : Cell F} (hinj : ∀ k k' : Fin C.R.N, C.R.arcSet k = C.R.arcSet k' → k = k')
    {k k' : Fin C.R.N} (h : C.arc k = C.arc k') : k = k' := by
  apply hinj
  rw [← image_arc C k, ← image_arc C k', h]

omit [IsCurveOver ℂ F] [T2Space (Place ℂ F)] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem capRegion_arcSet_injective {p : ℤ × ℤ} {b : ℂ} {w : Place ℂ F} (h : M.cape b w ≠ 0)
    (hbase : ∀ k k' : Fin (M.base p).N, (M.base p).arcSet k = (M.base p).arcSet k' → k = k') :
    ∀ a a' : Fin (M.capRegion p b w).N,
      (M.capRegion p b w).arcSet a = (M.capRegion p b w).arcSet a' → a = a' := by
  obtain ⟨-, lap, hbij, -, himg, -, hsep⟩ := M.capRegion_laps p h
  exact CellPairing.efold_arcSet_injective hbij himg hsep hbase

omit [IsCurveOver ℂ F] [T2Space (Place ℂ F)] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem infBase_arcSet_injective :
    ∀ a a' : Fin M.infBase.N, M.infBase.arcSet a = M.infBase.arcSet a' → a = a' := by
  intro a a' h
  have hwin := M.winReg_spec.2.2.2.2.1
  have hrec := M.infIdx_spec.2
  have h1 : M.infIdx.symm a = M.infIdx.symm a' := by
    apply hwin
    rw [← hrec, ← hrec, Equiv.apply_symm_apply, Equiv.apply_symm_apply, h]
  exact M.infIdx.symm.injective h1

omit [IsCurveOver ℂ F] [T2Space (Place ℂ F)] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem infRegion_arcSet_injective {w : Place ℂ F} (h : M.infe w ≠ 0) :
    ∀ a a' : Fin (M.infRegion w).N, (M.infRegion w).arcSet a = (M.infRegion w).arcSet a' → a = a' := by
  obtain ⟨-, lap, hbij, -, himg, -, hsep⟩ := M.infRegion_laps h
  exact CellPairing.efold_arcSet_injective hbij himg hsep M.infBase_arcSet_injective

theorem existsUnique_arc_over_square {p : ℤ × ℤ} (hp : p ∈ (M.toAssembly hF hrat).Win)
    (hbase : ∀ k k' : Fin (M.base p).N, (M.base p).arcSet k = (M.base p).arcSet k' → k = k')
    (k : Fin (M.base p).N) {A : Set (Place ℂ F)} (hA : IsPreconnected A) (hne : A.Nonempty)
    (hover : ∀ P ∈ A, M.x ∈ P.toValuationSubring ∧ Place.evalAt P M.x ∈ (M.base p).arcSet k)
    (honto : (M.base p).arcSet k ⊆ (fun P => Place.evalAt P M.x) '' A) :
    ∃! a : M.ArcOf hF hrat, M.regionOf hF hrat a.1 = some p ∧ M.arcPlaces hF hrat a = A := by
  obtain ⟨P₁, hP₁⟩ := hne
  by_cases hcap : M.capAt p = none
  ·
    have hQmem : p ∈ (M.toAssembly hF hrat).plain_finite.toFinset :=
      (M.toAssembly hF hrat).plain_finite.mem_toFinset.mpr
        ((M.toAssembly hF hrat).mem_plain_iff.mpr ⟨hp, hcap⟩)
    set Q : (M.toAssembly hF hrat).plain_finite.toFinset := ⟨p, hQmem⟩ with hQdef
    obtain ⟨i, hi, -⟩ := M.existsUnique_sheet_arc hF hrat Q k hA ⟨P₁, hP₁⟩ hover honto
    refine ⟨⟨Sum.inl ⟨Q, i⟩, k⟩, ⟨rfl, hi.symm⟩, ?_⟩
    rintro ⟨C, k''⟩ ⟨hreg, hplaces⟩
    rcases C with ⟨Q', i'⟩ | ⟨Q', w'⟩ | w'
    · have hfam := M.hsheet p hp hcap
      have hQ' : Q' = Q := Subtype.ext (Option.some.inj hreg)
      subst hQ'

      have hmemi : P₁ ∈ (M.sheet p i).source := by
        have h := hi ▸ hP₁
        rw [arc_inl] at h
        exact h.1
      have hmemi' : P₁ ∈ (M.sheet p i').source := by
        have h := hplaces ▸ hP₁
        unfold arcPlaces at h
        rw [arc_inl] at h
        exact h.1
      have hii : i' = i := by
        by_contra hne'
        exact Set.disjoint_left.mp (hfam.disjoint hne') hmemi' hmemi
      subst hii

      have hk : k'' = k := arc_index_eq hbase (hplaces.trans hi)
      subst hk
      rfl
    ·
      exfalso
      have hQ' : Q'.1 = p := Option.some.inj hreg
      have hQ'cap := ((M.toAssembly hF hrat).mem_caps_iff.mp
        ((M.toAssembly hF hrat).caps_finite.mem_toFinset.mp Q'.2)).2
      exact hQ'cap (hQ' ▸ hcap)
    · exact absurd hreg (by simp [regionOf])
  ·
    have hQmem : p ∈ (M.toAssembly hF hrat).caps_finite.toFinset :=
      (M.toAssembly hF hrat).caps_finite.mem_toFinset.mpr
        ((M.toAssembly hF hrat).mem_caps_iff.mpr ⟨hp, hcap⟩)
    set Q : (M.toAssembly hF hrat).caps_finite.toFinset := ⟨p, hQmem⟩ with hQdef
    obtain ⟨w, k', hwk⟩ := M.exists_cap_arc hF hrat Q k hA ⟨P₁, hP₁⟩ hover honto
    refine ⟨⟨Sum.inr (Sum.inl ⟨Q, w⟩), k'⟩, ⟨rfl, hwk.symm⟩, ?_⟩
    rintro ⟨C, k''⟩ ⟨hreg, hplaces⟩
    rcases C with ⟨Q', i'⟩ | ⟨Q', w'⟩ | w'
    · exfalso
      have hQ' : Q'.1 = p := Option.some.inj hreg
      have hQ'plain := ((M.toAssembly hF hrat).mem_plain_iff.mp
        ((M.toAssembly hF hrat).plain_finite.mem_toFinset.mp Q'.2)).2
      exact hcap (hQ' ▸ hQ'plain)
    · obtain ⟨hb, -, -, -⟩ := M.capVal_facts hF hrat Q
      have hinj := M.capRegion_arcSet_injective (p := p) (M.cape_ne_zero hb w.2.1 w.2.2) hbase
      have hQ' : Q' = Q := Subtype.ext (Option.some.inj hreg)
      subst hQ'

      have hmemw := hwk ▸ hP₁
      rw [arc_cap] at hmemw
      have hmemw' := hplaces ▸ hP₁
      unfold arcPlaces at hmemw'
      rw [arc_cap] at hmemw'
      have hww : w' = w := by
        apply Subtype.ext
        by_contra hne'
        exact Set.disjoint_left.mp
          (M.hcapdisj _ hb w'.1 w.1 w'.2.1 w'.2.2 w.2.1 w.2.2 hne') hmemw'.1 hmemw.1
      subst hww
      have hk : k'' = k' := arc_index_eq hinj (hplaces.trans hwk)
      subst hk
      rfl
    · exact absurd hreg (by simp [regionOf])

theorem existsUnique_arc_outside (k₀ : Fin M.winReg.N) {A : Set (Place ℂ F)}
    (hA : IsPreconnected A) (hne : A.Nonempty)
    (hover : ∀ P ∈ A, M.x ∈ P.toValuationSubring ∧ Place.evalAt P M.x ∈ M.winReg.arcSet k₀)
    (honto : M.winReg.arcSet k₀ ⊆ (fun P => Place.evalAt P M.x) '' A) :
    ∃! a : M.ArcOf hF hrat, M.regionOf hF hrat a.1 = none ∧ M.arcPlaces hF hrat a = A := by
  obtain ⟨P₁, hP₁⟩ := hne
  obtain ⟨w, k', hwk⟩ := M.exists_pole_arc hF hrat k₀ hA ⟨P₁, hP₁⟩ hover honto
  refine ⟨⟨Sum.inr (Sum.inr w), k'⟩, ⟨rfl, hwk.symm⟩, ?_⟩
  rintro ⟨C, k''⟩ ⟨hreg, hplaces⟩
  rcases C with ⟨Q', i'⟩ | ⟨Q', w'⟩ | w'
  · exact absurd hreg (by simp [regionOf])
  · exact absurd hreg (by simp [regionOf])
  · have hinj := M.infRegion_arcSet_injective (M.infe_ne_zero w.2)
    have hmemw := hwk ▸ hP₁
    rw [arc_inf] at hmemw
    have hmemw' := hplaces ▸ hP₁
    unfold arcPlaces at hmemw'
    rw [arc_inf] at hmemw'
    have hww : w' = w := by
      apply Subtype.ext
      by_contra hne'
      exact Set.disjoint_left.mp (M.hinfdisj w'.1 w.1 w'.2 w.2 hne') hmemw'.1 hmemw.1
    subst hww
    have hk : k'' = k' := arc_index_eq hinj (hplaces.trans hwk)
    subst hk
    rfl

abbrev LiesOver (A : Set (Place ℂ F)) (Z : Set ℂ) : Prop :=
  (∀ P ∈ A, M.x ∈ P.toValuationSubring ∧ Place.evalAt P M.x ∈ Z) ∧
    Z ⊆ (fun P => Place.evalAt P M.x) '' A

structure IsSqPres (a : M.ArcOf hF hrat) (p : ℤ × ℤ) (k : Fin (M.base p).N) (α : ℝ → ℝ) : Prop where
  region : M.regionOf hF hrat a.1 = some p
  affine : ∃ m c : ℝ, 0 < m ∧ ∀ t, α t = m * t + c
  start : α (((M.toAssembly hF hrat).cellOf a.1).R.φs a.2.castSucc) = (M.base p).φs k.castSucc
  stop : α (((M.toAssembly hF hrat).cellOf a.1).R.φs a.2.succ) = (M.base p).φs k.succ
  read : ∀ t ∈ ((M.toAssembly hF hrat).cellOf a.1).R.arcIcc a.2,
    Place.evalAt (((M.toAssembly hF hrat).cellOf a.1).bdry t) M.x = (M.base p).loop (α t)
  lies : M.LiesOver (M.arcPlaces hF hrat a) ((M.base p).arcSet k)

structure IsPerPres (a : M.ArcOf hF hrat) (k₀ : Fin M.winReg.N) (α : ℝ → ℝ) : Prop where
  region : M.regionOf hF hrat a.1 = none
  affine : ∃ m c : ℝ, m < 0 ∧ ∀ t, α t = m * t + c
  start : α (((M.toAssembly hF hrat).cellOf a.1).R.φs a.2.castSucc) = M.winReg.φs k₀.succ
  stop : α (((M.toAssembly hF hrat).cellOf a.1).R.φs a.2.succ) = M.winReg.φs k₀.castSucc
  read : ∀ t ∈ ((M.toAssembly hF hrat).cellOf a.1).R.arcIcc a.2,
    Place.evalAt (((M.toAssembly hF hrat).cellOf a.1).bdry t) M.x = M.winReg.loop (α t)
  lies : M.LiesOver (M.arcPlaces hF hrat a) (M.winReg.arcSet k₀)

omit [Planar] [IsCurveOver ℂ F] [T2Space (Place ℂ F)] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem bdry_mem_source_and_apply (C : Cell F) (t : ℝ) :
    C.bdry t ∈ C.ζ.source ∧ C.ζ (C.bdry t) = C.R.loop t := by
  have hK : C.R.loop t ∈ C.ζ.target := C.hKt (loop_mem_K C.R t)
  exact ⟨C.ζ.map_target hK, C.ζ.right_inv hK⟩

theorem cap_arc_liesOver (Q : (M.toAssembly hF hrat).caps_finite.toFinset)
    (w : (M.toAssembly hF hrat).Fib ((M.toAssembly hF hrat).capVal Q))
    {lap : Fin (M.cape ((M.toAssembly hF hrat).capVal Q) w.1) → Fin (M.base Q.1).N → Fin (M.capRegion Q.1 ((M.toAssembly hF hrat).capVal Q) w.1).N}
    (himg : ∀ (j : Fin (M.cape ((M.toAssembly hF hrat).capVal Q) w.1)) (k : Fin (M.base Q.1).N),
      (fun u : ℂ => (M.base Q.1).q + u ^ M.cape ((M.toAssembly hF hrat).capVal Q) w.1) '' (M.capRegion Q.1 ((M.toAssembly hF hrat).capVal Q) w.1).arcSet (lap j k) =
        (M.base Q.1).arcSet k)
    (j : Fin (M.cape ((M.toAssembly hF hrat).capVal Q) w.1)) (k : Fin (M.base Q.1).N) :
    M.LiesOver (M.arcPlaces hF hrat ⟨Sum.inr (Sum.inl ⟨Q, w⟩), lap j k⟩) ((M.base Q.1).arcSet k) := by
  obtain ⟨hb, -, hctr, -⟩ := M.capVal_facts hF hrat Q
  have hq : (M.base Q.1).q = ((M.toAssembly hF hrat).capVal Q) := by rw [base_q, hctr]
  have himg' := himg j k
  rw [hq] at himg'
  refine ⟨fun P hP => ?_, fun z hz => ?_⟩
  · have h : P ∈ M.arcPlaces hF hrat ⟨Sum.inr (Sum.inl ⟨Q, w⟩), lap j k⟩ := hP
    unfold arcPlaces at h
    rw [arc_cap] at h
    obtain ⟨hxP, hval⟩ := M.evalAt_eq_of_mem_capζ hrat hb w.2.1 w.2.2 h.1
    refine ⟨hxP, ?_⟩
    rw [hval, ← himg']
    exact ⟨_, h.2, rfl⟩
  · rw [← himg'] at hz
    obtain ⟨u, hu, huz⟩ := hz
    have hu' : u ∈ ((M.toAssembly hF hrat).cellOf (Sum.inr (Sum.inl ⟨Q, w⟩))).ζ ''
        ((M.toAssembly hF hrat).cellOf (Sum.inr (Sum.inl ⟨Q, w⟩))).arc (lap j k) := by
      rw [image_arc]
      exact hu
    obtain ⟨P, hP, hPu⟩ := hu'
    refine ⟨P, hP, ?_⟩
    have hPs : P ∈ (M.capζ ((M.toAssembly hF hrat).capVal Q) w.1).source :=
      arc_subset_source ((M.toAssembly hF hrat).cellOf (Sum.inr (Sum.inl ⟨Q, w⟩))) (lap j k) hP
    show Place.evalAt P M.x = z
    rw [(M.evalAt_eq_of_mem_capζ hrat hb w.2.1 w.2.2 hPs).2, ← huz]
    have hPu' : M.capζ ((M.toAssembly hF hrat).capVal Q) w.1 P = u := hPu
    rw [hPu']

theorem pole_arc_liesOver (w : (M.toAssembly hF hrat).FibInf)
    {lap : Fin (M.infe w.1) → Fin M.infBase.N → Fin (M.infRegion w.1).N}
    (himg : ∀ (j : Fin (M.infe w.1)) (σ : Fin M.infBase.N),
      (fun u : ℂ => M.infBase.q + u ^ M.infe w.1) '' (M.infRegion w.1).arcSet (lap j σ) = M.infBase.arcSet σ)
    (j : Fin (M.infe w.1)) (k₀ : Fin M.winReg.N) :
    M.LiesOver (M.arcPlaces hF hrat ⟨Sum.inr (Sum.inr w), lap j (M.infIdx k₀)⟩) (M.winReg.arcSet k₀) := by
  obtain ⟨-, hrecSet⟩ := M.infIdx_spec
  have hq : M.infBase.q = 0 := M.infBase_q
  refine ⟨fun P hP => ?_, fun z hz => ?_⟩
  · have h : P ∈ ((M.toAssembly hF hrat).cellOf (Sum.inr (Sum.inr w))).arc (lap j (M.infIdx k₀)) := hP
    rw [arc_inf] at h
    have hxP := M.x_mem_of_mem_inf_arc w.2 h.1 h.2
    refine ⟨hxP, ?_⟩
    obtain ⟨-, hinv⟩ := M.evalAt_of_mem_infζ hrat w.2 h.1 hxP
    rw [← hrecSet k₀]
    refine ⟨(Place.evalAt P M.x)⁻¹, ?_, inv_inv _⟩
    rw [hinv, ← himg j (M.infIdx k₀)]
    refine ⟨_, h.2, ?_⟩
    show M.infBase.q + (M.infζ w.1 P) ^ M.infe w.1 = (M.infζ w.1 P) ^ M.infe w.1
    rw [hq, zero_add]
  · rw [← hrecSet k₀] at hz
    obtain ⟨v, hv, hvz⟩ := hz
    rw [← himg j (M.infIdx k₀)] at hv
    obtain ⟨u, hu, huv⟩ := hv
    have hu' : u ∈ ((M.toAssembly hF hrat).cellOf (Sum.inr (Sum.inr w))).ζ ''
        ((M.toAssembly hF hrat).cellOf (Sum.inr (Sum.inr w))).arc (lap j (M.infIdx k₀)) := by
      rw [image_arc]
      exact hu
    obtain ⟨P, hP, hPu⟩ := hu'
    refine ⟨P, hP, ?_⟩
    have hPa := hP
    rw [arc_inf] at hPa
    have hxP := M.x_mem_of_mem_inf_arc w.2 hPa.1 hPa.2
    obtain ⟨-, hinv⟩ := M.evalAt_of_mem_infζ hrat w.2 hPa.1 hxP
    have hPu' : M.infζ w.1 P = u := hPu
    have hvz' : v⁻¹ = z := hvz
    have huv' : M.infBase.q + u ^ M.infe w.1 = v := huv
    rw [hq, zero_add] at huv'
    show Place.evalAt P M.x = z
    rw [← hvz', ← huv', ← hPu', ← hinv, inv_inv]

theorem sqPres_of_sheet (Q : (M.toAssembly hF hrat).plain_finite.toFinset) (i : Fin M.n)
    (k : Fin ((M.toAssembly hF hrat).cellOf (Sum.inl ⟨Q, i⟩)).R.N) :
    ∃ α : ℝ → ℝ, M.IsSqPres hF hrat ⟨Sum.inl ⟨Q, i⟩, k⟩ Q.1 k α := by
  have hQ := (M.toAssembly hF hrat).mem_plain_iff.mp
    ((M.toAssembly hF hrat).plain_finite.mem_toFinset.mp Q.2)
  have hfam := M.hsheet Q.1 hQ.1 hQ.2
  refine ⟨fun t => t, rfl, ⟨1, 0, one_pos, fun t => by ring⟩, rfl, rfl, ?_, ?_, ?_⟩
  · intro t _
    obtain ⟨hsrc, happ⟩ := bdry_mem_source_and_apply ((M.toAssembly hF hrat).cellOf (Sum.inl ⟨Q, i⟩)) t
    have h := (hfam.forward i _ hsrc).2
    exact h.symm.trans happ
  · intro P hP
    have h : P ∈ M.arcPlaces hF hrat ⟨Sum.inl ⟨Q, i⟩, k⟩ := hP
    unfold arcPlaces at h
    rw [arc_inl] at h
    exact ⟨(hfam.forward i P h.1).1, h.2⟩
  · intro z hz
    have hz' : z ∈ ((M.toAssembly hF hrat).cellOf (Sum.inl ⟨Q, i⟩)).ζ ''
        ((M.toAssembly hF hrat).cellOf (Sum.inl ⟨Q, i⟩)).arc k := by
      rw [image_arc]
      exact hz
    obtain ⟨P, hP, hPz⟩ := hz'
    refine ⟨P, hP, ?_⟩
    have hPs : P ∈ (M.sheet Q.1 i).source := arc_subset_source _ k hP
    show Place.evalAt P M.x = z
    rw [← (hfam.forward i P hPs).2]
    exact hPz

theorem sqPres_of_cap (Q : (M.toAssembly hF hrat).caps_finite.toFinset)
    (w : (M.toAssembly hF hrat).Fib ((M.toAssembly hF hrat).capVal Q))
    (k' : Fin ((M.toAssembly hF hrat).cellOf (Sum.inr (Sum.inl ⟨Q, w⟩))).R.N) :
    ∃ (k : Fin (M.base Q.1).N) (α : ℝ → ℝ),
      M.IsSqPres hF hrat ⟨Sum.inr (Sum.inl ⟨Q, w⟩), k'⟩ Q.1 k α := by
  obtain ⟨hb, -, hctr, -⟩ := M.capVal_facts hF hrat Q
  have he : M.cape ((M.toAssembly hF hrat).capVal Q) w.1 ≠ 0 := M.cape_ne_zero hb w.2.1 w.2.2
  obtain ⟨⟨-, -, -, -, hloop⟩, lap, hbij, harc, himg, -, -⟩ := M.capRegion_laps Q.1 he
  obtain ⟨⟨j, k⟩, hjk⟩ := hbij.2 k'
  have hjk' : lap j k = k' := hjk
  subst hjk'
  have hq : (M.base Q.1).q = ((M.toAssembly hF hrat).capVal Q) := by rw [base_q, hctr]
  have hepos : (0 : ℝ) < (M.cape ((M.toAssembly hF hrat).capVal Q) w.1 : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero he

  have hIcc := harc j k
  simp only [RadialRegion.arcIcc] at hIcc
  have hIcc' : Icc ((M.capRegion Q.1 ((M.toAssembly hF hrat).capVal Q) w.1).φs (lap j k).castSucc) ((M.capRegion Q.1 ((M.toAssembly hF hrat).capVal Q) w.1).φs (lap j k).succ) =
      (fun t : ℝ => (1 / (M.cape ((M.toAssembly hF hrat).capVal Q) w.1 : ℝ)) * t + 2 * π * (j : ℕ) / (M.cape ((M.toAssembly hF hrat).capVal Q) w.1 : ℝ)) ''
        Icc ((M.base Q.1).φs k.castSucc) ((M.base Q.1).φs k.succ) := by
    rw [hIcc]
    congr 1
    funext t
    field_simp
    ring
  obtain ⟨hstart, hstop⟩ := CellPairing.endpoints_of_image_mono (by positivity)
    ((M.base Q.1).hmono (Fin.castSucc_lt_succ : k.castSucc < k.succ)).le hIcc'
  refine ⟨k, fun θ => (M.cape ((M.toAssembly hF hrat).capVal Q) w.1 : ℝ) * θ - 2 * π * (j : ℕ), rfl,
    ⟨(M.cape ((M.toAssembly hF hrat).capVal Q) w.1 : ℝ), -(2 * π * (j : ℕ)), hepos, fun t => by ring⟩, ?_, ?_, ?_, ?_⟩
  · show (M.cape ((M.toAssembly hF hrat).capVal Q) w.1 : ℝ) * (M.capRegion Q.1 ((M.toAssembly hF hrat).capVal Q) w.1).φs (lap j k).castSucc - 2 * π * (j : ℕ) =
      (M.base Q.1).φs k.castSucc
    rw [hstart]
    field_simp
    ring
  · show (M.cape ((M.toAssembly hF hrat).capVal Q) w.1 : ℝ) * (M.capRegion Q.1 ((M.toAssembly hF hrat).capVal Q) w.1).φs (lap j k).succ - 2 * π * (j : ℕ) =
      (M.base Q.1).φs k.succ
    rw [hstop]
    field_simp
    ring
  · intro θ _
    obtain ⟨hsrc, happ⟩ := bdry_mem_source_and_apply ((M.toAssembly hF hrat).cellOf (Sum.inr (Sum.inl ⟨Q, w⟩))) θ
    have hval := (M.evalAt_eq_of_mem_capζ hrat hb w.2.1 w.2.2 hsrc).2
    rw [hval]
    have happ' : M.capζ ((M.toAssembly hF hrat).capVal Q) w.1 (((M.toAssembly hF hrat).cellOf (Sum.inr (Sum.inl ⟨Q, w⟩))).bdry θ) =
        (M.capRegion Q.1 ((M.toAssembly hF hrat).capVal Q) w.1).loop θ := happ
    have h2 := hloop θ
    rw [hq] at h2
    rw [happ', h2]
    have harg : (M.cape ((M.toAssembly hF hrat).capVal Q) w.1 : ℝ) * θ = ((M.cape ((M.toAssembly hF hrat).capVal Q) w.1 : ℝ) * θ - 2 * π * (j : ℕ)) + ((j : ℕ) : ℤ) * (2 * π) := by
      push_cast
      ring
    conv_lhs => rw [harg]
    rw [CellPairing.loop_add_int_mul]
  · exact M.cap_arc_liesOver hF hrat Q w himg j k

theorem perPres_of_pole (w : (M.toAssembly hF hrat).FibInf)
    (k' : Fin ((M.toAssembly hF hrat).cellOf (Sum.inr (Sum.inr w))).R.N) :
    ∃ (k₀ : Fin M.winReg.N) (α : ℝ → ℝ), M.IsPerPres hF hrat ⟨Sum.inr (Sum.inr w), k'⟩ k₀ α := by
  have he : M.infe w.1 ≠ 0 := M.infe_ne_zero w.2
  obtain ⟨⟨-, -, -, -, hloop⟩, lap, hbij, harc, himg, -, -⟩ := M.infRegion_laps he
  obtain ⟨⟨j, σ⟩, hjσ⟩ := hbij.2 k'
  have hjσ' : lap j σ = k' := hjσ
  subst hjσ'
  obtain ⟨k₀, rfl⟩ := M.infIdx.surjective σ
  obtain ⟨hrecIcc, -⟩ := M.infIdx_spec
  have hq : M.infBase.q = 0 := M.infBase_q
  have hrloop := M.infBase_spec.2.2.2.2.2
  have hepos : (0 : ℝ) < (M.infe w.1 : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero he

  have hIcc := harc j (M.infIdx k₀)
  rw [hrecIcc k₀, image_image] at hIcc
  simp only [RadialRegion.arcIcc] at hIcc
  have hIcc' : Icc ((M.infRegion w.1).φs (lap j (M.infIdx k₀)).castSucc)
      ((M.infRegion w.1).φs (lap j (M.infIdx k₀)).succ) =
      (fun t : ℝ => (-(1 / (M.infe w.1 : ℝ))) * t + 2 * π * ((j : ℕ) + 1) / (M.infe w.1 : ℝ)) ''
        Icc (M.winReg.φs k₀.castSucc) (M.winReg.φs k₀.succ) := by
    rw [hIcc]
    congr 1
    funext t
    field_simp
    ring
  obtain ⟨hstart, hstop⟩ := CellPairing.endpoints_of_image_anti (by
      have : (0 : ℝ) < 1 / (M.infe w.1 : ℝ) := by positivity
      linarith) (M.winReg.hmono (Fin.castSucc_lt_succ : k₀.castSucc < k₀.succ)).le hIcc'

  have hread : ∀ θ ∈ (M.infRegion w.1).arcIcc (lap j (M.infIdx k₀)),
      Place.evalAt (((M.toAssembly hF hrat).cellOf (Sum.inr (Sum.inr w))).bdry θ) M.x =
        M.winReg.loop (2 * π - (M.infe w.1 : ℝ) * θ) := by
    intro θ hθ
    obtain ⟨hsrc, happ⟩ := bdry_mem_source_and_apply ((M.toAssembly hF hrat).cellOf (Sum.inr (Sum.inr w))) θ
    have happ' : M.infζ w.1 (((M.toAssembly hF hrat).cellOf (Sum.inr (Sum.inr w))).bdry θ) =
        (M.infRegion w.1).loop θ := happ
    have hxP : M.x ∈ (((M.toAssembly hF hrat).cellOf (Sum.inr (Sum.inr w))).bdry θ).toValuationSubring := by
      apply M.x_mem_of_mem_inf_arc w.2 hsrc
      rw [happ']
      exact ⟨θ, hθ, rfl⟩
    obtain ⟨-, hinv⟩ := M.evalAt_of_mem_infζ hrat w.2 hsrc hxP
    have h1 := hloop θ
    rw [hq, zero_add] at h1
    rw [happ', h1, hrloop] at hinv
    exact inv_injective hinv
  refine ⟨k₀, fun θ => (-(M.infe w.1 : ℝ)) * θ + 2 * π * ((j : ℕ) + 1), rfl,
    ⟨-(M.infe w.1 : ℝ), 2 * π * ((j : ℕ) + 1), by linarith, fun t => rfl⟩, ?_, ?_, ?_, ?_⟩
  · show (-(M.infe w.1 : ℝ)) * (M.infRegion w.1).φs (lap j (M.infIdx k₀)).castSucc + 2 * π * ((j : ℕ) + 1) =
      M.winReg.φs k₀.succ
    rw [hstart]
    field_simp
    ring
  · show (-(M.infe w.1 : ℝ)) * (M.infRegion w.1).φs (lap j (M.infIdx k₀)).succ + 2 * π * ((j : ℕ) + 1) =
      M.winReg.φs k₀.castSucc
    rw [hstop]
    field_simp
    ring
  · intro θ hθ
    rw [hread θ hθ]
    have harg : 2 * π - (M.infe w.1 : ℝ) * θ =
        ((-(M.infe w.1 : ℝ)) * θ + 2 * π * ((j : ℕ) + 1)) + ((-(j : ℕ) : ℤ) : ℝ) * (2 * π) := by
      push_cast
      ring
    rw [harg, CellPairing.loop_add_int_mul]
  · exact M.pole_arc_liesOver hF hrat w himg j k₀

theorem exists_pres (a : M.ArcOf hF hrat) :
    (∃ (p : ℤ × ℤ) (k : Fin (M.base p).N) (α : ℝ → ℝ), M.IsSqPres hF hrat a p k α) ∨
      (∃ (k₀ : Fin M.winReg.N) (α : ℝ → ℝ), M.IsPerPres hF hrat a k₀ α) := by
  obtain ⟨C, k'⟩ := a
  rcases C with ⟨Q, i⟩ | ⟨Q, w⟩ | w
  · obtain ⟨α, hα⟩ := M.sqPres_of_sheet hF hrat Q i k'
    exact Or.inl ⟨Q.1, k', α, hα⟩
  · obtain ⟨k, α, hα⟩ := M.sqPres_of_cap hF hrat Q w k'
    exact Or.inl ⟨Q.1, k, α, hα⟩
  · obtain ⟨k₀, α, hα⟩ := M.perPres_of_pole hF hrat w k'
    exact Or.inr ⟨k₀, α, hα⟩

theorem injOn_evalAt_arcPlaces (a : M.ArcOf hF hrat) :
    InjOn (fun P : Place ℂ F => Place.evalAt P M.x) (M.arcPlaces hF hrat a) := by
  obtain ⟨C, k'⟩ := a
  rcases C with ⟨Q, i⟩ | ⟨Q, w⟩ | w
  · have hQ := (M.toAssembly hF hrat).mem_plain_iff.mp
      ((M.toAssembly hF hrat).plain_finite.mem_toFinset.mp Q.2)
    have hfam := M.hsheet Q.1 hQ.1 hQ.2
    intro P hP P' hP' hPP'
    have h : P ∈ ((M.toAssembly hF hrat).cellOf (Sum.inl ⟨Q, i⟩)).arc k' := hP
    have h' : P' ∈ ((M.toAssembly hF hrat).cellOf (Sum.inl ⟨Q, i⟩)).arc k' := hP'
    rw [arc_inl] at h h'
    apply (M.sheet Q.1 i).injOn h.1 h'.1
    rw [(hfam.forward i P h.1).2, (hfam.forward i P' h'.1).2]
    exact hPP'
  · obtain ⟨hb, -, hctr, -⟩ := M.capVal_facts hF hrat Q
    have he := M.cape_ne_zero hb w.2.1 w.2.2
    obtain ⟨-, lap, hbij, -, -, hinj, -⟩ := M.capRegion_laps Q.1 he
    obtain ⟨⟨j, k⟩, hjk⟩ := hbij.2 k'
    have hjk' : lap j k = k' := hjk
    subst hjk'
    have hq : (M.base Q.1).q = (M.toAssembly hF hrat).capVal Q := by rw [base_q, hctr]
    intro P hP P' hP' hPP'
    have h : P ∈ ((M.toAssembly hF hrat).cellOf (Sum.inr (Sum.inl ⟨Q, w⟩))).arc (lap j k) := hP
    have h' : P' ∈ ((M.toAssembly hF hrat).cellOf (Sum.inr (Sum.inl ⟨Q, w⟩))).arc (lap j k) := hP'
    rw [arc_cap] at h h'
    apply (M.capζ _ w.1).injOn h.1 h'.1
    apply hinj j k h.2 h'.2
    have e1 := (M.evalAt_eq_of_mem_capζ hrat hb w.2.1 w.2.2 h.1).2
    have e2 := (M.evalAt_eq_of_mem_capζ hrat hb w.2.1 w.2.2 h'.1).2
    show (M.base Q.1).q + _ = (M.base Q.1).q + _
    rw [hq, ← e1, ← e2]
    exact hPP'
  · have he := M.infe_ne_zero w.2
    obtain ⟨-, lap, hbij, -, -, hinj, -⟩ := M.infRegion_laps he
    obtain ⟨⟨j, σ⟩, hjσ⟩ := hbij.2 k'
    have hjσ' : lap j σ = k' := hjσ
    subst hjσ'
    have hq : M.infBase.q = 0 := M.infBase_q
    intro P hP P' hP' hPP'
    have h : P ∈ ((M.toAssembly hF hrat).cellOf (Sum.inr (Sum.inr w))).arc (lap j σ) := hP
    have h' : P' ∈ ((M.toAssembly hF hrat).cellOf (Sum.inr (Sum.inr w))).arc (lap j σ) := hP'
    rw [arc_inf] at h h'
    have hx := M.x_mem_of_mem_inf_arc w.2 h.1 h.2
    have hx' := M.x_mem_of_mem_inf_arc w.2 h'.1 h'.2
    apply (M.infζ w.1).injOn h.1 h'.1
    apply hinj j σ h.2 h'.2
    have e1 := (M.evalAt_of_mem_infζ hrat w.2 h.1 hx).2
    have e2 := (M.evalAt_of_mem_infζ hrat w.2 h'.1 hx').2
    show M.infBase.q + _ = M.infBase.q + _
    rw [hq, zero_add, zero_add, ← e1, ← e2]
    have hPP'' : Place.evalAt P M.x = Place.evalAt P' M.x := hPP'
    rw [hPP'']

omit [IsCurveOver ℂ F] [T2Space (Place ℂ F)] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [Planar] in

theorem LiesOver.eq {A : Set (Place ℂ F)} {Z Z' : Set ℂ} (h : M.LiesOver A Z) (h' : M.LiesOver A Z') :
    Z = Z' := by
  have key : ∀ {Y Y' : Set ℂ}, M.LiesOver A Y → M.LiesOver A Y' → Y ⊆ Y' := by
    intro Y Y' hY hY' z hz
    obtain ⟨P, hP, rfl⟩ := hY.2 hz
    exact (hY'.1 P hP).2
  exact Subset.antisymm (key h h') (key h' h)

def Shares : Option (ℤ × ℤ) → Set ℂ → Prop
  | some p, Z => p ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi ∧ ∃ k : Fin (M.base p).N, (M.base p).arcSet k = Z
  | none, Z => ∃ k₀ : Fin M.winReg.N, M.winReg.arcSet k₀ = Z

structure SideFacts : Prop where
  base_inj : ∀ p ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi,
    ∀ k k' : Fin (M.base p).N, (M.base p).arcSet k = (M.base p).arcSet k' → k = k'
  two_regions : ∀ (ρ : Option (ℤ × ℤ)) (Z : Set ℂ), M.Shares ρ Z →
    ∃ ρ' : Option (ℤ × ℤ), ρ' ≠ ρ ∧ M.Shares ρ' Z ∧
      ∀ ρ'' : Option (ℤ × ℤ), M.Shares ρ'' Z → ρ'' = ρ ∨ ρ'' = ρ'

theorem arcPlaces_nonempty (a : M.ArcOf hF hrat) : (M.arcPlaces hF hrat a).Nonempty :=
  arc_nonempty _ a.2

theorem arcPlaces_isPreconnected (a : M.ArcOf hF hrat) : IsPreconnected (M.arcPlaces hF hrat a) :=
  isPreconnected_arc _ a.2

theorem regionOf_mem_win (C : (M.toAssembly hF hrat).IdxC) {p : ℤ × ℤ}
    (hreg : M.regionOf hF hrat C = some p) : p ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi := by
  revert hreg
  rcases C with ⟨Q, i⟩ | ⟨Q, w⟩ | w
  · intro hreg
    obtain rfl : Q.1 = p := Option.some.inj hreg
    exact ((M.toAssembly hF hrat).mem_plain_iff.mp
      ((M.toAssembly hF hrat).plain_finite.mem_toFinset.mp Q.2)).1
  · intro hreg
    obtain rfl : Q.1 = p := Option.some.inj hreg
    exact ((M.toAssembly hF hrat).mem_caps_iff.mp
      ((M.toAssembly hF hrat).caps_finite.mem_toFinset.mp Q.2)).1
  · intro hreg
    exact absurd (show some p = none from hreg.symm) (Option.some_ne_none p)

theorem exists_shared (a : M.ArcOf hF hrat) :
    ∃ Z : Set ℂ, M.Shares (M.regionOf hF hrat a.1) Z ∧ M.LiesOver (M.arcPlaces hF hrat a) Z := by
  rcases M.exists_pres hF hrat a with ⟨p, k, α, h⟩ | ⟨k₀, α, h⟩
  · refine ⟨_, ?_, h.lies⟩
    rw [h.region]
    exact ⟨M.regionOf_mem_win hF hrat a.1 h.region, k, rfl⟩
  · refine ⟨_, ?_, h.lies⟩
    rw [h.region]
    exact ⟨k₀, rfl⟩

theorem existsUnique_arc_in_region (SF : M.SideFacts) {ρ : Option (ℤ × ℤ)} {Z : Set ℂ}
    (hsh : M.Shares ρ Z) {A : Set (Place ℂ F)} (hA : IsPreconnected A) (hne : A.Nonempty)
    (hover : M.LiesOver A Z) :
    ∃! a : M.ArcOf hF hrat, M.regionOf hF hrat a.1 = ρ ∧ M.arcPlaces hF hrat a = A := by
  rcases ρ with _ | p
  · obtain ⟨k₀, rfl⟩ := hsh
    exact M.existsUnique_arc_outside hF hrat k₀ hA hne hover.1 hover.2
  · obtain ⟨hp, k, rfl⟩ := hsh
    exact M.existsUnique_arc_over_square hF hrat hp (SF.base_inj p hp) k hA hne hover.1 hover.2

theorem exists_partner (SF : M.SideFacts) (a : M.ArcOf hF hrat) :
    ∃ a' : M.ArcOf hF hrat,
      M.regionOf hF hrat a'.1 ≠ M.regionOf hF hrat a.1 ∧ M.arcPlaces hF hrat a' = M.arcPlaces hF hrat a := by
  obtain ⟨Z, hsh, hover⟩ := M.exists_shared hF hrat a
  obtain ⟨ρ', hne, hsh', -⟩ := SF.two_regions _ Z hsh
  obtain ⟨a', ⟨hreg', hplaces'⟩, -⟩ := M.existsUnique_arc_in_region hF hrat SF hsh'
    (M.arcPlaces_isPreconnected hF hrat a) (M.arcPlaces_nonempty hF hrat a) hover
  exact ⟨a', by rw [hreg']; exact hne, hplaces'⟩

theorem partner_unique (SF : M.SideFacts) (a : M.ArcOf hF hrat) {a₁ a₂ : M.ArcOf hF hrat}
    (h₁ : M.regionOf hF hrat a₁.1 ≠ M.regionOf hF hrat a.1)
    (hp₁ : M.arcPlaces hF hrat a₁ = M.arcPlaces hF hrat a)
    (h₂ : M.regionOf hF hrat a₂.1 ≠ M.regionOf hF hrat a.1)
    (hp₂ : M.arcPlaces hF hrat a₂ = M.arcPlaces hF hrat a) : a₁ = a₂ := by
  obtain ⟨Z, hsh, hover⟩ := M.exists_shared hF hrat a
  obtain ⟨ρ', -, hsh', huniq⟩ := SF.two_regions _ Z hsh

  have hreg : ∀ b : M.ArcOf hF hrat, M.regionOf hF hrat b.1 ≠ M.regionOf hF hrat a.1 →
      M.arcPlaces hF hrat b = M.arcPlaces hF hrat a → M.regionOf hF hrat b.1 = ρ' := by
    intro b hb hpb
    obtain ⟨Zb, hshb, hoverb⟩ := M.exists_shared hF hrat b
    rw [hpb] at hoverb
    have hZ : Zb = Z := LiesOver.eq M hoverb hover
    subst hZ
    rcases huniq _ hshb with h | h
    · exact absurd h hb
    · exact h
  obtain ⟨c, -, hc⟩ := M.existsUnique_arc_in_region hF hrat SF hsh'
    (M.arcPlaces_isPreconnected hF hrat a) (M.arcPlaces_nonempty hF hrat a) hover
  rw [hc a₁ ⟨hreg a₁ h₁ hp₁, hp₁⟩, hc a₂ ⟨hreg a₂ h₂ hp₂, hp₂⟩]

noncomputable def pairArc (SF : M.SideFacts) (a : M.ArcOf hF hrat) : M.ArcOf hF hrat :=
  Classical.choose (M.exists_partner hF hrat SF a)

theorem pairArc_region (SF : M.SideFacts) (a : M.ArcOf hF hrat) :
    M.regionOf hF hrat (M.pairArc hF hrat SF a).1 ≠ M.regionOf hF hrat a.1 :=
  (Classical.choose_spec (M.exists_partner hF hrat SF a)).1

theorem arcPlaces_pairArc (SF : M.SideFacts) (a : M.ArcOf hF hrat) :
    M.arcPlaces hF hrat (M.pairArc hF hrat SF a) = M.arcPlaces hF hrat a :=
  (Classical.choose_spec (M.exists_partner hF hrat SF a)).2

theorem pairArc_pairArc (SF : M.SideFacts) (a : M.ArcOf hF hrat) :
    M.pairArc hF hrat SF (M.pairArc hF hrat SF a) = a := by
  apply M.partner_unique hF hrat SF (M.pairArc hF hrat SF a)
    (M.pairArc_region hF hrat SF _) (M.arcPlaces_pairArc hF hrat SF _)
  · exact fun h => M.pairArc_region hF hrat SF a h.symm
  · exact (M.arcPlaces_pairArc hF hrat SF a).symm

structure SideFacts2 where
  sqbit : ∀ p : ℤ × ℤ, Fin (M.base p).N → Bool
  perbit : Fin M.winReg.N → Bool
  bit_sq_sq : ∀ p p' : ℤ × ℤ, p ≠ p' → ∀ (k : Fin (M.base p).N) (k' : Fin (M.base p').N),
    (M.base p).arcSet k = (M.base p').arcSet k' → sqbit p' k' = !sqbit p k
  bit_sq_per : ∀ (p : ℤ × ℤ) (k : Fin (M.base p).N) (k₀ : Fin M.winReg.N),
    p ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi → (M.base p).arcSet k = M.winReg.arcSet k₀ → perbit k₀ = !sqbit p k
  rev_sq_sq : ∀ p p' : ℤ × ℤ, p ≠ p' → ∀ (k : Fin (M.base p).N) (k' : Fin (M.base p').N),
    (M.base p).arcSet k = (M.base p').arcSet k' → sqbit p k = true →
    ∃ ψ : ℝ → ℝ, StrictAntiOn ψ ((M.base p').arcIcc k') ∧ ContDiffOn ℝ 1 ψ ((M.base p').arcIcc k') ∧
      ψ ((M.base p').φs k'.castSucc) = (M.base p).φs k.succ ∧
      ψ ((M.base p').φs k'.succ) = (M.base p).φs k.castSucc ∧
      ∀ t ∈ (M.base p').arcIcc k', (M.base p').loop t = (M.base p).loop (ψ t)
  rev_per_to_sq : ∀ (p : ℤ × ℤ) (k : Fin (M.base p).N) (k₀ : Fin M.winReg.N),
    p ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi → (M.base p).arcSet k = M.winReg.arcSet k₀ → sqbit p k = true →
    ∃ ψ : ℝ → ℝ, StrictMonoOn ψ (M.winReg.arcIcc k₀) ∧ ContDiffOn ℝ 1 ψ (M.winReg.arcIcc k₀) ∧
      ψ (M.winReg.φs k₀.castSucc) = (M.base p).φs k.castSucc ∧
      ψ (M.winReg.φs k₀.succ) = (M.base p).φs k.succ ∧
      ∀ t ∈ M.winReg.arcIcc k₀, M.winReg.loop t = (M.base p).loop (ψ t)
  rev_sq_to_per : ∀ (p : ℤ × ℤ) (k : Fin (M.base p).N) (k₀ : Fin M.winReg.N),
    p ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi → (M.base p).arcSet k = M.winReg.arcSet k₀ → sqbit p k = false →
    ∃ ψ : ℝ → ℝ, StrictMonoOn ψ ((M.base p).arcIcc k) ∧ ContDiffOn ℝ 1 ψ ((M.base p).arcIcc k) ∧
      ψ ((M.base p).φs k.castSucc) = M.winReg.φs k₀.castSucc ∧
      ψ ((M.base p).φs k.succ) = M.winReg.φs k₀.succ ∧
      ∀ t ∈ (M.base p).arcIcc k, (M.base p).loop t = M.winReg.loop (ψ t)

open scoped Classical in

noncomputable def orientArc (S2 : M.SideFacts2) (a : M.ArcOf hF hrat) : Bool :=
  if h : ∃ (p : ℤ × ℤ) (k : Fin (M.base p).N) (α : ℝ → ℝ), M.IsSqPres hF hrat a p k α then
    S2.sqbit h.choose h.choose_spec.choose
  else if h' : ∃ (k₀ : Fin M.winReg.N) (α : ℝ → ℝ), M.IsPerPres hF hrat a k₀ α then
    S2.perbit h'.choose
  else false

theorem sqbit_eq_of_pres (SF : M.SideFacts) (S2 : M.SideFacts2) {a : M.ArcOf hF hrat}
    {p₁ p : ℤ × ℤ} {k₁ : Fin (M.base p₁).N} {k : Fin (M.base p).N} {α₁ α : ℝ → ℝ}
    (h₁ : M.IsSqPres hF hrat a p₁ k₁ α₁) (h : M.IsSqPres hF hrat a p k α) :
    S2.sqbit p₁ k₁ = S2.sqbit p k := by
  obtain rfl : p₁ = p := Option.some.inj (h₁.region.symm.trans h.region)
  have hZ := LiesOver.eq M h₁.lies h.lies
  rw [SF.base_inj _ (M.regionOf_mem_win hF hrat a.1 h.region) k₁ k hZ]

theorem IsPerPres.index_eq {a : M.ArcOf hF hrat} {k₀ k₀' : Fin M.winReg.N} {α α' : ℝ → ℝ}
    (h : M.IsPerPres hF hrat a k₀ α) (h' : M.IsPerPres hF hrat a k₀' α') : k₀' = k₀ := by
  have hZ : M.winReg.arcSet k₀' = M.winReg.arcSet k₀ := LiesOver.eq M h'.lies h.lies
  exact M.winReg_spec.2.2.2.2.1 k₀' k₀ hZ

theorem orientArc_of_sqPres (SF : M.SideFacts) (S2 : M.SideFacts2) {a : M.ArcOf hF hrat} {p : ℤ × ℤ}
    {k : Fin (M.base p).N} {α : ℝ → ℝ} (h : M.IsSqPres hF hrat a p k α) :
    M.orientArc hF hrat S2 a = S2.sqbit p k := by
  have hex : ∃ (p : ℤ × ℤ) (k : Fin (M.base p).N) (α : ℝ → ℝ), M.IsSqPres hF hrat a p k α := ⟨p, k, α, h⟩
  rw [orientArc, dif_pos hex]
  exact M.sqbit_eq_of_pres hF hrat SF S2 hex.choose_spec.choose_spec.choose_spec h

theorem orientArc_of_perPres (S2 : M.SideFacts2) {a : M.ArcOf hF hrat} {k₀ : Fin M.winReg.N}
    {α : ℝ → ℝ} (h : M.IsPerPres hF hrat a k₀ α) : M.orientArc hF hrat S2 a = S2.perbit k₀ := by
  have hnot : ¬ ∃ (p : ℤ × ℤ) (k : Fin (M.base p).N) (α : ℝ → ℝ), M.IsSqPres hF hrat a p k α := by
    rintro ⟨p, k, α', h'⟩
    have hsome := h'.region
    rw [h.region] at hsome
    exact Option.some_ne_none p hsome.symm
  have hex : ∃ (k₀ : Fin M.winReg.N) (α : ℝ → ℝ), M.IsPerPres hF hrat a k₀ α := ⟨k₀, α, h⟩
  rw [orientArc, dif_neg hnot, dif_pos hex, IsPerPres.index_eq M hF hrat hex.choose_spec.choose_spec h]

abbrev RevClause (a a' : M.ArcOf hF hrat) (ψ : ℝ → ℝ) : Prop :=
  StrictAntiOn ψ (((M.toAssembly hF hrat).cellOf a'.1).R.arcIcc a'.2) ∧ ContDiffOn ℝ 1 ψ (((M.toAssembly hF hrat).cellOf a'.1).R.arcIcc a'.2) ∧
    ψ (((M.toAssembly hF hrat).cellOf a'.1).R.φs a'.2.castSucc) = ((M.toAssembly hF hrat).cellOf a.1).R.φs a.2.succ ∧ ψ (((M.toAssembly hF hrat).cellOf a'.1).R.φs a'.2.succ) = ((M.toAssembly hF hrat).cellOf a.1).R.φs a.2.castSucc ∧
    ∀ t ∈ ((M.toAssembly hF hrat).cellOf a'.1).R.arcIcc a'.2, ((M.toAssembly hF hrat).cellOf a'.1).bdry t = ((M.toAssembly hF hrat).cellOf a.1).bdry (ψ t)

theorem revClause_of_transport (a a' : M.ArcOf hF hrat)
    (hplaces : M.arcPlaces hF hrat a' = M.arcPlaces hF hrat a)
    {R R' : RadialRegion} {α α' : ℝ → ℝ} {m c : ℝ} (hm : m ≠ 0) (hα : ∀ t, α t = m * t + c)
    (hread : ∀ t ∈ ((M.toAssembly hF hrat).cellOf a.1).R.arcIcc a.2, Place.evalAt (((M.toAssembly hF hrat).cellOf a.1).bdry t) M.x = R.loop (α t))
    {Ik : Set ℝ} (hinv : MapsTo (fun u : ℝ => (u - c) / m) Ik (((M.toAssembly hF hrat).cellOf a.1).R.arcIcc a.2))
    (hread' : ∀ t ∈ ((M.toAssembly hF hrat).cellOf a'.1).R.arcIcc a'.2, Place.evalAt (((M.toAssembly hF hrat).cellOf a'.1).bdry t) M.x = R'.loop (α' t))
    {Ik' : Set ℝ} (hmaps' : MapsTo α' (((M.toAssembly hF hrat).cellOf a'.1).R.arcIcc a'.2) Ik') (hα'C : ContDiffOn ℝ 1 α' (((M.toAssembly hF hrat).cellOf a'.1).R.arcIcc a'.2))
    {ψ₀ : ℝ → ℝ} (hψmaps : MapsTo ψ₀ Ik' Ik) (hψC : ContDiffOn ℝ 1 ψ₀ Ik')
    (hloop : ∀ u ∈ Ik', R'.loop u = R.loop (ψ₀ u))
    (hanti : StrictAntiOn (fun t => (ψ₀ (α' t) - c) / m) (((M.toAssembly hF hrat).cellOf a'.1).R.arcIcc a'.2))
    (hstart : (ψ₀ (α' (((M.toAssembly hF hrat).cellOf a'.1).R.φs a'.2.castSucc)) - c) / m = ((M.toAssembly hF hrat).cellOf a.1).R.φs a.2.succ)
    (hstop : (ψ₀ (α' (((M.toAssembly hF hrat).cellOf a'.1).R.φs a'.2.succ)) - c) / m = ((M.toAssembly hF hrat).cellOf a.1).R.φs a.2.castSucc) :
    M.RevClause hF hrat a a' (fun t => (ψ₀ (α' t) - c) / m) := by
  refine ⟨hanti, ?_, hstart, hstop, ?_⟩
  · exact CellPairing.contDiffOn_comp₃ hα'C hmaps' hψC (CellPairing.contDiffOn_affine_inv m c univ)
  · intro t ht
    have hu : α' t ∈ Ik' := hmaps' ht
    have hv : ψ₀ (α' t) ∈ Ik := hψmaps hu
    have hs : (ψ₀ (α' t) - c) / m ∈ ((M.toAssembly hF hrat).cellOf a.1).R.arcIcc a.2 := hinv hv
    refine M.injOn_evalAt_arcPlaces hF hrat a ?_ ?_ ?_
    · rw [← hplaces]
      exact bdry_mem_arc _ ht
    · exact bdry_mem_arc _ hs
    · show Place.evalAt (((M.toAssembly hF hrat).cellOf a'.1).bdry t) M.x = Place.evalAt (((M.toAssembly hF hrat).cellOf a.1).bdry ((ψ₀ (α' t) - c) / m)) M.x
      rw [hread' t ht, hloop _ hu, hread _ hs, hα, CellPairing.affine_apply_inv hm]

theorem exists_revClause_sq_sq (S2 : M.SideFacts2) (a a' : M.ArcOf hF hrat)
    (hreg : M.regionOf hF hrat a'.1 ≠ M.regionOf hF hrat a.1)
    (hplaces : M.arcPlaces hF hrat a' = M.arcPlaces hF hrat a)
    {p : ℤ × ℤ} {k : Fin (M.base p).N} {α : ℝ → ℝ} (h : M.IsSqPres hF hrat a p k α)
    {p' : ℤ × ℤ} {k' : Fin (M.base p').N} {α' : ℝ → ℝ} (h' : M.IsSqPres hF hrat a' p' k' α')
    (hbit : S2.sqbit p k = true) : ∃ ψ : ℝ → ℝ, M.RevClause hF hrat a a' ψ := by
  have hpp : p ≠ p' := by
    rintro rfl
    exact hreg (h'.region.trans h.region.symm)
  have hZ : (M.base p).arcSet k = (M.base p').arcSet k' := by
    apply LiesOver.eq M h.lies
    rw [← hplaces]
    exact h'.lies
  obtain ⟨ψ₀, hψanti, hψC, hψ0, hψ1, hloop⟩ := S2.rev_sq_sq p p' hpp k k' hZ hbit
  obtain ⟨m, c, hm, hα⟩ := h.affine
  obtain ⟨m', c', hm', hα'⟩ := h'.affine
  have hα'f : α' = fun t => m' * t + c' := funext hα'
  have hst := h.start
  have hsp := h.stop
  have hst' := h'.start
  have hsp' := h'.stop
  rw [hα] at hst hsp
  rw [hα'] at hst' hsp'

  have hIk : (M.base p).arcIcc k = Icc (m * (((M.toAssembly hF hrat).cellOf a.1).R.φs a.2.castSucc) + c) (m * (((M.toAssembly hF hrat).cellOf a.1).R.φs a.2.succ) + c) := by
    rw [CellPairing.arcIcc_eq, hst, hsp]
  have hIk' : (M.base p').arcIcc k' = Icc (m' * (((M.toAssembly hF hrat).cellOf a'.1).R.φs a'.2.castSucc) + c') (m' * (((M.toAssembly hF hrat).cellOf a'.1).R.φs a'.2.succ) + c') := by
    rw [CellPairing.arcIcc_eq, hst', hsp']
  have hmaps' : MapsTo α' (((M.toAssembly hF hrat).cellOf a'.1).R.arcIcc a'.2) ((M.base p').arcIcc k') := by
    rw [hα'f, CellPairing.arcIcc_eq ((((M.toAssembly hF hrat).cellOf a'.1)).R) a'.2, hIk']
    exact CellPairing.affine_mapsTo_pos hm'
  have hψmaps : MapsTo ψ₀ ((M.base p').arcIcc k') ((M.base p).arcIcc k) := by
    have hle : (M.base p').φs k'.castSucc ≤ (M.base p').φs k'.succ :=
      ((M.base p').hmono Fin.castSucc_lt_succ).le
    have hmt := CellPairing.mapsTo_Icc_of_strictAntiOn hle hψanti
    rw [hψ0, hψ1] at hmt
    rw [CellPairing.arcIcc_eq (M.base p') k', CellPairing.arcIcc_eq (M.base p) k]
    exact hmt
  have hinv : MapsTo (fun u : ℝ => (u - c) / m) ((M.base p).arcIcc k) (((M.toAssembly hF hrat).cellOf a.1).R.arcIcc a.2) := by
    rw [hIk, CellPairing.arcIcc_eq ((((M.toAssembly hF hrat).cellOf a.1)).R) a.2]
    exact CellPairing.affine_inv_mapsTo_pos hm
  have hα'C : ContDiffOn ℝ 1 α' (((M.toAssembly hF hrat).cellOf a'.1).R.arcIcc a'.2) := by
    rw [hα'f]
    exact CellPairing.contDiffOn_affine m' c' _
  refine ⟨_, M.revClause_of_transport hF hrat a a' hplaces hm.ne' hα h.read hinv h'.read hmaps'
    hα'C hψmaps hψC hloop ?_ ?_ ?_⟩
  ·
    have h1 : StrictAntiOn (fun t => ψ₀ (α' t)) (((M.toAssembly hF hrat).cellOf a'.1).R.arcIcc a'.2) :=
      CellPairing.strictAntiOn_comp_mono (by rw [hα'f]; exact CellPairing.strictMonoOn_affine_pos hm' _) hmaps' hψanti
    exact CellPairing.strictAntiOn_comp_anti h1 (fun t ht => hψmaps (hmaps' ht))
      ((CellPairing.strictMono_affine_inv (c := c) hm).strictMonoOn _)
  · rw [h'.start, hψ0, ← hsp, CellPairing.affine_inv_apply hm.ne']
  · rw [h'.stop, hψ1, ← hst, CellPairing.affine_inv_apply hm.ne']

theorem exists_revClause_sq_per (S2 : M.SideFacts2) (a a' : M.ArcOf hF hrat)
    (hplaces : M.arcPlaces hF hrat a' = M.arcPlaces hF hrat a)
    {p : ℤ × ℤ} {k : Fin (M.base p).N} {α : ℝ → ℝ} (h : M.IsSqPres hF hrat a p k α)
    {k₀ : Fin M.winReg.N} {α' : ℝ → ℝ} (h' : M.IsPerPres hF hrat a' k₀ α')
    (hbit : S2.sqbit p k = true) : ∃ ψ : ℝ → ℝ, M.RevClause hF hrat a a' ψ := by
  have hZ : (M.base p).arcSet k = M.winReg.arcSet k₀ := by
    apply LiesOver.eq M h.lies
    rw [← hplaces]
    exact h'.lies
  have hp : p ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi := M.regionOf_mem_win hF hrat a.1 h.region
  obtain ⟨ψ₀, hψmono, hψC, hψ0, hψ1, hloop⟩ := S2.rev_per_to_sq p k k₀ hp hZ hbit
  obtain ⟨m, c, hm, hα⟩ := h.affine
  obtain ⟨m', c', hm', hα'⟩ := h'.affine
  have hα'f : α' = fun t => m' * t + c' := funext hα'
  have hst := h.start
  have hsp := h.stop
  have hst' := h'.start
  have hsp' := h'.stop
  rw [hα] at hst hsp
  rw [hα'] at hst' hsp'
  have hIk : (M.base p).arcIcc k = Icc (m * (((M.toAssembly hF hrat).cellOf a.1).R.φs a.2.castSucc) + c) (m * (((M.toAssembly hF hrat).cellOf a.1).R.φs a.2.succ) + c) := by
    rw [CellPairing.arcIcc_eq, hst, hsp]

  have hIk' : M.winReg.arcIcc k₀ = Icc (m' * (((M.toAssembly hF hrat).cellOf a'.1).R.φs a'.2.succ) + c') (m' * (((M.toAssembly hF hrat).cellOf a'.1).R.φs a'.2.castSucc) + c') := by
    rw [CellPairing.arcIcc_eq, hst', hsp']
  have hmaps' : MapsTo α' (((M.toAssembly hF hrat).cellOf a'.1).R.arcIcc a'.2) (M.winReg.arcIcc k₀) := by
    rw [hα'f, CellPairing.arcIcc_eq ((((M.toAssembly hF hrat).cellOf a'.1)).R) a'.2, hIk']
    exact CellPairing.affine_mapsTo_neg hm'
  have hψmaps : MapsTo ψ₀ (M.winReg.arcIcc k₀) ((M.base p).arcIcc k) := by
    have hle : M.winReg.φs k₀.castSucc ≤ M.winReg.φs k₀.succ :=
      (M.winReg.hmono Fin.castSucc_lt_succ).le
    have hmt := CellPairing.mapsTo_Icc_of_strictMonoOn hle hψmono
    rw [hψ0, hψ1] at hmt
    rw [CellPairing.arcIcc_eq M.winReg k₀, CellPairing.arcIcc_eq (M.base p) k]
    exact hmt
  have hinv : MapsTo (fun u : ℝ => (u - c) / m) ((M.base p).arcIcc k) (((M.toAssembly hF hrat).cellOf a.1).R.arcIcc a.2) := by
    rw [hIk, CellPairing.arcIcc_eq ((((M.toAssembly hF hrat).cellOf a.1)).R) a.2]
    exact CellPairing.affine_inv_mapsTo_pos hm
  have hα'C : ContDiffOn ℝ 1 α' (((M.toAssembly hF hrat).cellOf a'.1).R.arcIcc a'.2) := by
    rw [hα'f]
    exact CellPairing.contDiffOn_affine m' c' _
  refine ⟨_, M.revClause_of_transport hF hrat a a' hplaces hm.ne' hα h.read hinv h'.read hmaps'
    hα'C hψmaps hψC hloop ?_ ?_ ?_⟩
  · have h1 : StrictAntiOn (fun t => ψ₀ (α' t)) (((M.toAssembly hF hrat).cellOf a'.1).R.arcIcc a'.2) :=
      CellPairing.strictAntiOn_comp_anti (by rw [hα'f]; exact CellPairing.strictAntiOn_affine_neg hm' _) hmaps' hψmono
    exact CellPairing.strictAntiOn_comp_anti h1 (fun t ht => hψmaps (hmaps' ht))
      ((CellPairing.strictMono_affine_inv (c := c) hm).strictMonoOn _)
  · rw [h'.start, hψ1, ← hsp, CellPairing.affine_inv_apply hm.ne']
  · rw [h'.stop, hψ0, ← hst, CellPairing.affine_inv_apply hm.ne']

theorem exists_revClause_per_sq (S2 : M.SideFacts2) (a a' : M.ArcOf hF hrat)
    (hplaces : M.arcPlaces hF hrat a' = M.arcPlaces hF hrat a)
    {k₀ : Fin M.winReg.N} {α : ℝ → ℝ} (h : M.IsPerPres hF hrat a k₀ α)
    {p' : ℤ × ℤ} {k' : Fin (M.base p').N} {α' : ℝ → ℝ} (h' : M.IsSqPres hF hrat a' p' k' α')
    (hbit : S2.perbit k₀ = true) : ∃ ψ : ℝ → ℝ, M.RevClause hF hrat a a' ψ := by
  have hZ : (M.base p').arcSet k' = M.winReg.arcSet k₀ := by
    apply LiesOver.eq M h'.lies
    rw [hplaces]
    exact h.lies
  have hbit' : S2.sqbit p' k' = false := by
    have hb := S2.bit_sq_per p' k' k₀ (M.regionOf_mem_win hF hrat a'.1 h'.region) hZ
    rw [hbit] at hb
    cases hsq : S2.sqbit p' k'
    · rfl
    · rw [hsq] at hb
      exact absurd hb (by decide)
  obtain ⟨ψ₀, hψmono, hψC, hψ0, hψ1, hloop⟩ :=
    S2.rev_sq_to_per p' k' k₀ (M.regionOf_mem_win hF hrat a'.1 h'.region) hZ hbit'
  obtain ⟨m, c, hm, hα⟩ := h.affine
  obtain ⟨m', c', hm', hα'⟩ := h'.affine
  have hα'f : α' = fun t => m' * t + c' := funext hα'
  have hst := h.start
  have hsp := h.stop
  have hst' := h'.start
  have hsp' := h'.stop
  rw [hα] at hst hsp
  rw [hα'] at hst' hsp'

  have hIk : M.winReg.arcIcc k₀ = Icc (m * (((M.toAssembly hF hrat).cellOf a.1).R.φs a.2.succ) + c) (m * (((M.toAssembly hF hrat).cellOf a.1).R.φs a.2.castSucc) + c) := by
    rw [CellPairing.arcIcc_eq, hsp, hst]
  have hIk' : (M.base p').arcIcc k' = Icc (m' * (((M.toAssembly hF hrat).cellOf a'.1).R.φs a'.2.castSucc) + c') (m' * (((M.toAssembly hF hrat).cellOf a'.1).R.φs a'.2.succ) + c') := by
    rw [CellPairing.arcIcc_eq, hst', hsp']
  have hmaps' : MapsTo α' (((M.toAssembly hF hrat).cellOf a'.1).R.arcIcc a'.2) ((M.base p').arcIcc k') := by
    rw [hα'f, CellPairing.arcIcc_eq ((((M.toAssembly hF hrat).cellOf a'.1)).R) a'.2, hIk']
    exact CellPairing.affine_mapsTo_pos hm'
  have hψmaps : MapsTo ψ₀ ((M.base p').arcIcc k') (M.winReg.arcIcc k₀) := by
    have hle : (M.base p').φs k'.castSucc ≤ (M.base p').φs k'.succ :=
      ((M.base p').hmono Fin.castSucc_lt_succ).le
    have hmt := CellPairing.mapsTo_Icc_of_strictMonoOn hle hψmono
    rw [hψ0, hψ1] at hmt
    rw [CellPairing.arcIcc_eq (M.base p') k', CellPairing.arcIcc_eq M.winReg k₀]
    exact hmt
  have hinv : MapsTo (fun u : ℝ => (u - c) / m) (M.winReg.arcIcc k₀) (((M.toAssembly hF hrat).cellOf a.1).R.arcIcc a.2) := by
    rw [hIk, CellPairing.arcIcc_eq ((((M.toAssembly hF hrat).cellOf a.1)).R) a.2]
    exact CellPairing.affine_inv_mapsTo_neg hm
  have hα'C : ContDiffOn ℝ 1 α' (((M.toAssembly hF hrat).cellOf a'.1).R.arcIcc a'.2) := by
    rw [hα'f]
    exact CellPairing.contDiffOn_affine m' c' _
  refine ⟨_, M.revClause_of_transport hF hrat a a' hplaces hm.ne hα h.read hinv h'.read hmaps'
    hα'C hψmaps hψC hloop ?_ ?_ ?_⟩
  · have h1 : StrictMonoOn (fun t => ψ₀ (α' t)) (((M.toAssembly hF hrat).cellOf a'.1).R.arcIcc a'.2) :=
      CellPairing.strictMonoOn_comp_mono (by rw [hα'f]; exact CellPairing.strictMonoOn_affine_pos hm' _) hmaps' hψmono
    exact CellPairing.strictAntiOn_comp_mono h1 (fun t ht => hψmaps (hmaps' ht))
      ((CellPairing.strictAnti_affine_inv (c := c) hm).strictAntiOn _)
  · rw [h'.start, hψ0, ← hsp, CellPairing.affine_inv_apply hm.ne]
  · rw [h'.stop, hψ1, ← hst, CellPairing.affine_inv_apply hm.ne]

theorem exists_revClause (SF : M.SideFacts) (S2 : M.SideFacts2) (a a' : M.ArcOf hF hrat)
    (hreg : M.regionOf hF hrat a'.1 ≠ M.regionOf hF hrat a.1)
    (hplaces : M.arcPlaces hF hrat a' = M.arcPlaces hF hrat a)
    (ha : M.orientArc hF hrat S2 a = true) : ∃ ψ : ℝ → ℝ, M.RevClause hF hrat a a' ψ := by
  rcases M.exists_pres hF hrat a with ⟨p, k, α, h⟩ | ⟨k₀, α, h⟩ <;>
    rcases M.exists_pres hF hrat a' with ⟨p', k', α', h'⟩ | ⟨k₀', α', h'⟩
  · exact M.exists_revClause_sq_sq hF hrat S2 a a' hreg hplaces h h'
      ((M.orientArc_of_sqPres hF hrat SF S2 h).symm.trans ha)
  · exact M.exists_revClause_sq_per hF hrat S2 a a' hplaces h h'
      ((M.orientArc_of_sqPres hF hrat SF S2 h).symm.trans ha)
  · exact M.exists_revClause_per_sq hF hrat S2 a a' hplaces h h'
      ((M.orientArc_of_perPres hF hrat S2 h).symm.trans ha)
  · exact absurd (h'.region.trans h.region.symm) hreg

theorem orientArc_partner (SF : M.SideFacts) (S2 : M.SideFacts2) (a a' : M.ArcOf hF hrat)
    (hreg : M.regionOf hF hrat a'.1 ≠ M.regionOf hF hrat a.1)
    (hplaces : M.arcPlaces hF hrat a' = M.arcPlaces hF hrat a) :
    M.orientArc hF hrat S2 a' = !M.orientArc hF hrat S2 a := by
  have hZ : ∀ {Z Z' : Set ℂ}, M.LiesOver (M.arcPlaces hF hrat a) Z → M.LiesOver (M.arcPlaces hF hrat a') Z' →
      Z = Z' := by
    intro Z Z' h1 h2
    rw [hplaces] at h2
    exact LiesOver.eq M h1 h2
  rcases M.exists_pres hF hrat a with ⟨p, k, α, h⟩ | ⟨k₀, α, h⟩ <;>
    rcases M.exists_pres hF hrat a' with ⟨p', k', α', h'⟩ | ⟨k₀', α', h'⟩
  · have hpp : p ≠ p' := by
      rintro rfl
      exact hreg (h'.region.trans h.region.symm)
    rw [M.orientArc_of_sqPres hF hrat SF S2 h, M.orientArc_of_sqPres hF hrat SF S2 h']
    exact S2.bit_sq_sq p p' hpp k k' (hZ h.lies h'.lies)
  · rw [M.orientArc_of_sqPres hF hrat SF S2 h, M.orientArc_of_perPres hF hrat S2 h']
    exact S2.bit_sq_per p k k₀' (M.regionOf_mem_win hF hrat a.1 h.region) (hZ h.lies h'.lies)
  · rw [M.orientArc_of_perPres hF hrat S2 h, M.orientArc_of_sqPres hF hrat SF S2 h']
    have hb := S2.bit_sq_per p' k' k₀ (M.regionOf_mem_win hF hrat a'.1 h'.region) (hZ h.lies h'.lies).symm
    rw [hb]
    cases S2.sqbit p' k' <;> rfl
  · exact absurd (h'.region.trans h.region.symm) hreg

noncomputable def edgeData (SF : M.SideFacts) (S2 : M.SideFacts2) : EdgeData (M.toAssembly hF hrat) where
  pair := M.pairArc hF hrat SF
  hpair := M.pairArc_pairArc hF hrat SF
  orient := M.orientArc hF hrat S2
  horient := fun a => M.orientArc_partner hF hrat SF S2 a (M.pairArc hF hrat SF a)
    (M.pairArc_region hF hrat SF a) (M.arcPlaces_pairArc hF hrat SF a)
  hrev := by
    intro C k C' k' hpair hor
    have hreg := M.pairArc_region hF hrat SF ⟨C, k⟩
    have hpl := M.arcPlaces_pairArc hF hrat SF ⟨C, k⟩
    rw [hpair] at hreg hpl
    exact M.exists_revClause hF hrat SF S2 ⟨C, k⟩ ⟨C', k'⟩ hreg hpl hor

def Contains : Option (ℤ × ℤ) → ℂ → Prop
  | some p, v => p ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi ∧ v ∈ (M.base p).K
  | none, v => v ∉ M.winReg.Kint

def Adj (v : ℂ) (ρ ρ' : Option (ℤ × ℤ)) : Prop :=
  ∃ Z : Set ℂ, M.Shares ρ Z ∧ M.Shares ρ' Z ∧ v ∈ Z

structure StarFacts : Prop where
  star : ∀ (v : ℂ) (ρ ρ' : Option (ℤ × ℤ)), M.Contains ρ v → M.Contains ρ' v →
    Relation.ReflTransGen (M.Adj v) ρ ρ'

theorem contains_of_mem_carrier (C : (M.toAssembly hF hrat).IdxC) {P : Place ℂ F}
    (hP : P ∈ ((M.toAssembly hF hrat).cellOf C).carrier) :
    (M.x ∈ P.toValuationSubring ∧ M.Contains (M.regionOf hF hrat C) (Place.evalAt P M.x)) ∨
      (M.x ∉ P.toValuationSubring ∧ ∃ w : (M.toAssembly hF hrat).FibInf, C = Sum.inr (Sum.inr w) ∧ w.1 = P) := by
  rcases C with ⟨Q, i⟩ | ⟨Q, w⟩ | w
  · left
    rw [carrier_inl] at hP
    have hQ := (M.toAssembly hF hrat).mem_plain_iff.mp
      ((M.toAssembly hF hrat).plain_finite.mem_toFinset.mp Q.2)
    have hfam := M.hsheet Q.1 hQ.1 hQ.2
    refine ⟨(hfam.forward i P hP.1).1, ?_⟩
    show Q.1 ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi ∧ Place.evalAt P M.x ∈ (M.base Q.1).K
    refine ⟨hQ.1, ?_⟩
    rw [base_K]
    exact hP.2
  · left
    rw [carrier_cap] at hP
    obtain ⟨hb, -, -, -⟩ := M.capVal_facts hF hrat Q
    have hQ := (M.toAssembly hF hrat).mem_caps_iff.mp
      ((M.toAssembly hF hrat).caps_finite.mem_toFinset.mp Q.2)
    refine ⟨(M.evalAt_eq_of_mem_capζ hrat hb w.2.1 w.2.2 hP.1).1, ?_⟩
    show Q.1 ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi ∧ Place.evalAt P M.x ∈ (M.base Q.1).K
    refine ⟨hQ.1, ?_⟩
    rw [base_K]
    exact hP.2
  · rw [carrier_inf] at hP
    by_cases hx : M.x ∈ P.toValuationSubring
    · left
      refine ⟨hx, ?_⟩
      show Place.evalAt P M.x ∉ M.winReg.Kint
      rcases hP.2 with h | h
      · exact absurd hx h
      · exact h
    · right
      exact ⟨hx, w, rfl, (M.eq_of_mem_infζ_source w.2 hx hP.1).symm⟩

theorem sheet_eq_of_mem (Q : (M.toAssembly hF hrat).plain_finite.toFinset) (i i' : Fin M.n) {P : Place ℂ F}
    (hP : P ∈ ((M.toAssembly hF hrat).cellOf (Sum.inl ⟨Q, i⟩)).carrier)
    (hP' : P ∈ ((M.toAssembly hF hrat).cellOf (Sum.inl ⟨Q, i'⟩)).carrier) : i' = i := by
  rw [carrier_inl] at hP hP'
  have hQ := (M.toAssembly hF hrat).mem_plain_iff.mp
    ((M.toAssembly hF hrat).plain_finite.mem_toFinset.mp Q.2)
  have hfam := M.hsheet Q.1 hQ.1 hQ.2
  by_contra hii
  exact Set.disjoint_left.mp (hfam.disjoint hii) hP'.1 hP.1

theorem cap_eq_of_mem (Q : (M.toAssembly hF hrat).caps_finite.toFinset)
    (w w' : (M.toAssembly hF hrat).Fib ((M.toAssembly hF hrat).capVal Q)) {P : Place ℂ F}
    (hP : P ∈ ((M.toAssembly hF hrat).cellOf (Sum.inr (Sum.inl ⟨Q, w⟩))).carrier)
    (hP' : P ∈ ((M.toAssembly hF hrat).cellOf (Sum.inr (Sum.inl ⟨Q, w'⟩))).carrier) : w' = w := by
  rw [carrier_cap] at hP hP'
  obtain ⟨hb, -, -, -⟩ := M.capVal_facts hF hrat Q
  by_contra hww
  have hne : w'.1 ≠ w.1 := fun h => hww (Subtype.ext h)
  exact Set.disjoint_left.mp (M.hcapdisj _ hb w'.1 w.1 w'.2.1 w'.2.2 w.2.1 w.2.2 hne) hP'.1 hP.1

theorem pole_eq_of_mem (w w' : (M.toAssembly hF hrat).FibInf) {P : Place ℂ F}
    (hP : P ∈ ((M.toAssembly hF hrat).cellOf (Sum.inr (Sum.inr w))).carrier)
    (hP' : P ∈ ((M.toAssembly hF hrat).cellOf (Sum.inr (Sum.inr w'))).carrier) : w' = w := by
  rw [carrier_inf] at hP hP'
  by_contra hww
  have hne : w'.1 ≠ w.1 := fun h => hww (Subtype.ext h)
  exact Set.disjoint_left.mp (M.hinfdisj w'.1 w.1 w'.2 w.2 hne) hP'.1 hP.1

theorem cell_eq_of_mem (C C' : (M.toAssembly hF hrat).IdxC) {P : Place ℂ F}
    (hP : P ∈ ((M.toAssembly hF hrat).cellOf C).carrier) (hP' : P ∈ ((M.toAssembly hF hrat).cellOf C').carrier)
    (hreg : M.regionOf hF hrat C' = M.regionOf hF hrat C) : C' = C := by
  rcases C with ⟨Q, i⟩ | ⟨Q, w⟩ | w <;> rcases C' with ⟨Q', i'⟩ | ⟨Q', w'⟩ | w'
  ·
    have hQQ : Q' = Q := Subtype.ext (Option.some.inj hreg)
    subst hQQ
    rw [M.sheet_eq_of_mem hF hrat _ _ _ hP hP']
  ·
    exfalso
    have hQQ : Q'.1 = Q.1 := Option.some.inj hreg
    have hplain := ((M.toAssembly hF hrat).mem_plain_iff.mp
      ((M.toAssembly hF hrat).plain_finite.mem_toFinset.mp Q.2)).2
    have hcap := ((M.toAssembly hF hrat).mem_caps_iff.mp
      ((M.toAssembly hF hrat).caps_finite.mem_toFinset.mp Q'.2)).2
    rw [hQQ] at hcap
    exact hcap hplain
  · exact absurd hreg (by simp [regionOf])
  · exfalso
    have hQQ : Q'.1 = Q.1 := Option.some.inj hreg
    have hplain := ((M.toAssembly hF hrat).mem_plain_iff.mp
      ((M.toAssembly hF hrat).plain_finite.mem_toFinset.mp Q'.2)).2
    have hcap := ((M.toAssembly hF hrat).mem_caps_iff.mp
      ((M.toAssembly hF hrat).caps_finite.mem_toFinset.mp Q.2)).2
    rw [← hQQ] at hcap
    exact hcap hplain
  ·
    have hQQ : Q' = Q := Subtype.ext (Option.some.inj hreg)
    subst hQQ
    rw [M.cap_eq_of_mem hF hrat _ _ _ hP hP']
  · exact absurd hreg (by simp [regionOf])
  · exact absurd hreg (by simp [regionOf])
  · exact absurd hreg (by simp [regionOf])
  · rw [M.pole_eq_of_mem hF hrat _ _ hP hP']

theorem exists_arc_through (X : (M.toAssembly hF hrat).IdxC) {P : Place ℂ F}
    (hx : M.x ∈ P.toValuationSubring)
    (hP : P ∈ ((M.toAssembly hF hrat).cellOf X).carrier) {Z : Set ℂ}
    (hsh : M.Shares (M.regionOf hF hrat X) Z) (hv : Place.evalAt P M.x ∈ Z) :
    ∃ k : Fin ((M.toAssembly hF hrat).cellOf X).R.N,
      P ∈ ((M.toAssembly hF hrat).cellOf X).arc k ∧ M.LiesOver (M.arcPlaces hF hrat ⟨X, k⟩) Z := by
  rcases X with ⟨Q, i⟩ | ⟨Q, w⟩ | w
  · obtain ⟨-, k, rfl⟩ := hsh
    rw [carrier_inl] at hP
    refine ⟨k, ?_, ?_⟩
    · rw [arc_inl]
      exact ⟨hP.1, hv⟩
    · obtain ⟨α, hα⟩ := M.sqPres_of_sheet hF hrat Q i k
      exact hα.lies
  · obtain ⟨-, k, rfl⟩ := hsh
    rw [carrier_cap] at hP
    obtain ⟨hb, -, hctr, -⟩ := M.capVal_facts hF hrat Q
    have he := M.cape_ne_zero hb w.2.1 w.2.2
    obtain ⟨-, lap, -, -, himg, -, hsep⟩ := M.capRegion_laps Q.1 he
    have hq : (M.base Q.1).q = (M.toAssembly hF hrat).capVal Q := by rw [base_q, hctr]
    have hval := (M.evalAt_eq_of_mem_capζ hrat hb w.2.1 w.2.2 hP.1).2
    have hmem : (M.base Q.1).q + (M.capζ ((M.toAssembly hF hrat).capVal Q) w.1 P) ^
        M.cape ((M.toAssembly hF hrat).capVal Q) w.1 ∈ (M.base Q.1).arcSet k := by
      rw [hq, ← hval]
      exact hv
    obtain ⟨j, hj⟩ := CellPairing.exists_lap_of_pow_mem he himg hsep hmem
    refine ⟨lap j k, ?_, ?_⟩
    · rw [arc_cap]
      exact ⟨hP.1, hj⟩
    · exact M.cap_arc_liesOver hF hrat Q w himg j k
  · obtain ⟨k₀, rfl⟩ := hsh
    rw [carrier_inf] at hP
    have he := M.infe_ne_zero w.2
    obtain ⟨-, lap, -, -, himg, -, hsep⟩ := M.infRegion_laps he
    obtain ⟨-, hrecSet⟩ := M.infIdx_spec
    have hq : M.infBase.q = 0 := M.infBase_q
    obtain ⟨-, hinv⟩ := M.evalAt_of_mem_infζ hrat w.2 hP.1 hx

    have hmem : M.infBase.q + (M.infζ w.1 P) ^ M.infe w.1 ∈ M.infBase.arcSet (M.infIdx k₀) := by
      rw [hq, zero_add, ← hinv]
      rw [← hrecSet k₀] at hv
      obtain ⟨u, hu, huv⟩ := hv
      have huv' : u⁻¹ = Place.evalAt P M.x := huv
      rw [← huv', inv_inv]
      exact hu
    obtain ⟨j, hj⟩ := CellPairing.exists_lap_of_pow_mem he himg hsep hmem
    refine ⟨lap j (M.infIdx k₀), ?_, ?_⟩
    · rw [arc_inf]
      exact ⟨hP.1, hj⟩
    · exact M.pole_arc_liesOver hF hrat w himg j k₀

abbrev Step (SF : M.SideFacts) (P : Place ℂ F) (X Y : (M.toAssembly hF hrat).IdxC) : Prop :=
  ∃ (k : Fin ((M.toAssembly hF hrat).cellOf X).R.N) (k' : Fin ((M.toAssembly hF hrat).cellOf Y).R.N),
    M.pairArc hF hrat SF ⟨X, k⟩ = ⟨Y, k'⟩ ∧ P ∈ ((M.toAssembly hF hrat).cellOf X).arc k

theorem shares_pairArc (SF : M.SideFacts) (a : M.ArcOf hF hrat) {Z : Set ℂ}
    (hZ : M.LiesOver (M.arcPlaces hF hrat a) Z) :
    M.Shares (M.regionOf hF hrat (M.pairArc hF hrat SF a).1) Z := by
  obtain ⟨Z', hsh, hlies⟩ := M.exists_shared hF hrat (M.pairArc hF hrat SF a)
  rw [M.arcPlaces_pairArc hF hrat SF a] at hlies
  rwa [LiesOver.eq M hZ hlies]

theorem exists_step (SF : M.SideFacts) (X : (M.toAssembly hF hrat).IdxC) {P : Place ℂ F}
    (hx : M.x ∈ P.toValuationSubring) (hP : P ∈ ((M.toAssembly hF hrat).cellOf X).carrier)
    {ρ' : Option (ℤ × ℤ)} (hadj : M.Adj (Place.evalAt P M.x) (M.regionOf hF hrat X) ρ') :
    ∃ Y : (M.toAssembly hF hrat).IdxC, M.regionOf hF hrat Y = ρ' ∧ P ∈ ((M.toAssembly hF hrat).cellOf Y).carrier ∧
      Relation.ReflTransGen (M.Step hF hrat SF P) X Y := by
  obtain ⟨Z, hshX, hsh', hv⟩ := hadj
  by_cases hρ : ρ' = M.regionOf hF hrat X
  · exact ⟨X, hρ.symm, hP, Relation.ReflTransGen.refl⟩
  obtain ⟨k, hPk, hlies⟩ := M.exists_arc_through hF hrat X hx hP hshX hv
  obtain ⟨ρ₁, -, -, huniq⟩ := SF.two_regions _ Z hshX
  have hY := M.shares_pairArc hF hrat SF ⟨X, k⟩ hlies
  have hYne := M.pairArc_region hF hrat SF ⟨X, k⟩
  have hρ'₁ : ρ' = ρ₁ := (huniq ρ' hsh').resolve_left hρ
  have hYρ₁ : M.regionOf hF hrat (M.pairArc hF hrat SF ⟨X, k⟩).1 = ρ₁ :=
    (huniq _ hY).resolve_left hYne
  refine ⟨(M.pairArc hF hrat SF ⟨X, k⟩).1, hYρ₁.trans hρ'₁.symm, ?_, Relation.ReflTransGen.single ?_⟩
  · have hPa : P ∈ M.arcPlaces hF hrat (M.pairArc hF hrat SF ⟨X, k⟩) := by
      rw [M.arcPlaces_pairArc hF hrat SF]
      exact hPk
    exact arc_subset_carrier ((M.toAssembly hF hrat).cellOf (M.pairArc hF hrat SF ⟨X, k⟩).1) _ hPa
  · exact ⟨k, (M.pairArc hF hrat SF ⟨X, k⟩).2, rfl, hPk⟩

theorem star_property (SF : M.SideFacts) (ST : M.StarFacts) (C C' : (M.toAssembly hF hrat).IdxC)
    {P : Place ℂ F} (hP : P ∈ ((M.toAssembly hF hrat).cellOf C).carrier)
    (hP' : P ∈ ((M.toAssembly hF hrat).cellOf C').carrier) :
    Relation.ReflTransGen (M.Step hF hrat SF P) C C' := by
  rcases M.contains_of_mem_carrier hF hrat C hP with ⟨hx, hcont⟩ | ⟨hx, w, rfl, hwP⟩
  · rcases M.contains_of_mem_carrier hF hrat C' hP' with ⟨-, hcont'⟩ | ⟨hx', -⟩
    · have hchain := ST.star _ _ _ hcont hcont'

      have key : ∀ ρ : Option (ℤ × ℤ), Relation.ReflTransGen (M.Adj (Place.evalAt P M.x)) (M.regionOf hF hrat C) ρ →
          ∃ Y : (M.toAssembly hF hrat).IdxC, M.regionOf hF hrat Y = ρ ∧
            P ∈ ((M.toAssembly hF hrat).cellOf Y).carrier ∧ Relation.ReflTransGen (M.Step hF hrat SF P) C Y := by
        intro ρ hρ
        induction hρ with
        | refl => exact ⟨C, rfl, hP, Relation.ReflTransGen.refl⟩
        | tail _ hadj ih =>
          obtain ⟨Y, hYρ, hPY, hCY⟩ := ih
          rw [← hYρ] at hadj
          obtain ⟨Y', hY'ρ, hPY', hYY'⟩ := M.exists_step hF hrat SF Y hx hPY hadj
          exact ⟨Y', hY'ρ, hPY', hCY.trans hYY'⟩
      obtain ⟨Y, hYρ, hPY, hCY⟩ := key _ hchain
      rwa [← M.cell_eq_of_mem hF hrat Y C' hPY hP' hYρ.symm] at hCY
    · exact absurd hx hx'
  · rcases M.contains_of_mem_carrier hF hrat C' hP' with ⟨hx', -⟩ | ⟨-, w', rfl, hw'P⟩
    · exact absurd hx' hx
    · have hww : w' = w := Subtype.ext (hw'P.trans hwP.symm)
      subst hww
      exact Relation.ReflTransGen.refl

end DissectionMaterials.Materials
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.AssemblyData P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.EdgeData"
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.AssemblyData P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.EdgeData"

end Part_D1Pair
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.AssemblyData P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.EdgeData"

section Part_D1Vert

set_option autoImplicit false

p2m_open "AlgebraicCurve~H1 Set P2MW.S_AlgebraicCurve_exists_pairedCellFamily.PlanarRegions P2MW.S_AlgebraicCurve_exists_pairedCellFamily.DissectionMaterials P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily P2MW.S_AlgebraicCurve_exists_pairedCellFamily.ArcPairing P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CellFacts"
open scoped Manifold ContDiff Topology Real

namespace DissectionMaterials
namespace Materials

variable {F : Type*} [Field F] [Algebra ℂ F] [TopologicalSpace (Place ℂ F)]
variable [ChartedSpace ℂ (Place ℂ F)]
variable {S : Finset (Place ℂ F)} {P₀ : Place ℂ F}
variable (M : Materials F S P₀) [Planar] [IsCurveOver ℂ F] [T2Space (Place ℂ F)]
variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]
variable (hF : OrdPack F) (hrat : ∀ P : Place ℂ F, P.IsRational)

structure VertFacts where
  B₀ : Finset ℂ
  card_B₀ : B₀.card = CellCount.V₀ (M.toAssembly hF hrat)
  sq_break : ∀ p ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi, ∀ i : Fin ((M.base p).N + 1),
    (M.base p).loop ((M.base p).φs i) ∈ B₀
  per_break : ∀ i : Fin (M.winReg.N + 1), M.winReg.loop (M.winReg.φs i) ∈ B₀
  break_of_mem : ∀ v ∈ B₀, ∃ p ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi, ∃ k : Fin (M.base p).N,
    v = (M.base p).loop ((M.base p).φs k.castSucc) ∨ v = (M.base p).loop ((M.base p).φs k.succ)
  on_grid_line : ∀ v ∈ B₀, ∃ j : ℤ, v.re - M.o = j * M.hm

noncomputable def fibre (t : ℂ) : Finset (Place ℂ F) := (M.hfib t).toFinset

omit [Planar] [IsCurveOver ℂ F] [T2Space (Place ℂ F)] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem mem_fibre {t : ℂ} {P : Place ℂ F} :
    P ∈ M.fibre t ↔ M.x ∈ P.toValuationSubring ∧ Place.evalAt P M.x = t := by
  unfold fibre
  rw [Set.Finite.mem_toFinset]
  rfl

theorem not_mem_bad_of_vertFacts (V : M.VertFacts hF hrat) {v : ℂ} (hv : v ∈ V.B₀) : v ∉ M.Bad := by
  intro hbad
  obtain ⟨j, hj⟩ := V.on_grid_line v hv
  exact (M.hbad_off v hbad j).1 hj

theorem exists_cell_over_square {p : ℤ × ℤ} (hp : p ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi)
    {P : Place ℂ F} (hxP : M.x ∈ P.toValuationSubring)
    (hvp : Place.evalAt P M.x ∈ PlaneGrid.gridSquare M.o M.hm p.1 p.2) :
    ∃ C : (M.toAssembly hF hrat).IdxC, M.regionOf hF hrat C = some p ∧
      P ∈ ((M.toAssembly hF hrat).cellOf C).carrier := by
  by_cases hcap : M.capAt p = none
  · have hpl : p ∈ (M.toAssembly hF hrat).Plain := (M.toAssembly hF hrat).mem_plain_iff.mpr ⟨hp, hcap⟩
    have hvV : Place.evalAt P M.x ∈ M.margin p := M.hmargin_sq p hp hcap hvp
    obtain ⟨i, hi⟩ := (M.hsheet p hp hcap).exhaust P hxP hvV
    refine ⟨Sum.inl ⟨⟨p, (M.toAssembly hF hrat).plain_finite.mem_toFinset.mpr hpl⟩, i⟩, rfl, ?_⟩
    rw [carrier_inl]
    exact ⟨hi, hvp⟩
  · obtain ⟨b, hb, hsome, hbd⟩ := M.exists_capAt_eq hcap
    have hcp : p ∈ (M.toAssembly hF hrat).Caps := (M.toAssembly hF hrat).mem_caps_iff.mpr ⟨hp, hcap⟩
    have hb_sq : b ∈ PlaneGrid.gridSquare M.o M.hm p.1 p.2 := by
      rw [gridSquare_eq]
      have h := M.bad_mem_of_capAt hsome
      exact ⟨⟨h.1.1.le, h.1.2.le⟩, h.2.1.le, h.2.2.le⟩
    have hclose : ‖Place.evalAt P M.x - b‖ < 2 * M.cs b := by
      have h1 := M.norm_sub_le_of_mem_gridSquare hvp hb_sq
      have h2 := M.hcs b hb
      linarith [M.hhm]
    obtain ⟨w, hxw, hwb, hPw⟩ := M.hcapexhaust b hb P hxP hclose
    let Q : (M.toAssembly hF hrat).caps_finite.toFinset :=
      ⟨p, (M.toAssembly hF hrat).caps_finite.mem_toFinset.mpr hcp⟩
    have hwfib : M.x ∈ w.toValuationSubring ∧
        Place.evalAt w M.x = (M.toAssembly hF hrat).capVal Q := by
      refine ⟨hxw, ?_⟩
      show Place.evalAt w M.x = (M.capAt p).getD 0
      rw [hbd]; exact hwb
    refine ⟨Sum.inr (Sum.inl ⟨Q, ⟨w, hwfib⟩⟩), rfl, ?_⟩
    rw [carrier_cap]
    refine ⟨?_, hvp⟩
    show P ∈ (M.capζ ((M.capAt p).getD 0) w).source
    rw [hbd]; exact hPw

theorem endPt_mem_fibre_B₀ (V : M.VertFacts hF hrat) (a : M.ArcOf hF hrat) (b : Bool) :
    M.x ∈ ((M.toAssembly hF hrat).endPt a b).toValuationSubring ∧
      Place.evalAt ((M.toAssembly hF hrat).endPt a b) M.x ∈ V.B₀ := by

  have hle : ((M.toAssembly hF hrat).cellOf a.1).R.φs a.2.castSucc ≤
      ((M.toAssembly hF hrat).cellOf a.1).R.φs a.2.succ :=
    (((M.toAssembly hF hrat).cellOf a.1).R.hmono (Fin.castSucc_lt_succ)).le
  have hparam : ((M.toAssembly hF hrat).cellOf a.1).R.φs (if b then a.2.succ else a.2.castSucc) ∈
      ((M.toAssembly hF hrat).cellOf a.1).R.arcIcc a.2 := by
    cases b
    · exact ⟨le_rfl, hle⟩
    · exact ⟨hle, le_rfl⟩
  have hmem : (M.toAssembly hF hrat).endPt a b ∈ M.arcPlaces hF hrat a :=
    bdry_mem_arc ((M.toAssembly hF hrat).cellOf a.1) hparam
  rcases M.exists_pres hF hrat a with ⟨p, k, α, h⟩ | ⟨k₀, α, h⟩
  · refine ⟨(h.lies.1 _ hmem).1, ?_⟩
    have hp : p ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi := M.regionOf_mem_win hF hrat a.1 h.region
    have hread := h.read _ hparam
    show Place.evalAt (((M.toAssembly hF hrat).cellOf a.1).bdry _) M.x ∈ V.B₀
    rw [hread]
    cases b
    · rw [if_neg Bool.false_ne_true, h.start]
      exact V.sq_break p hp _
    · rw [if_pos rfl, h.stop]
      exact V.sq_break p hp _
  · refine ⟨(h.lies.1 _ hmem).1, ?_⟩
    have hread := h.read _ hparam
    show Place.evalAt (((M.toAssembly hF hrat).cellOf a.1).bdry _) M.x ∈ V.B₀
    rw [hread]
    cases b
    · rw [if_neg Bool.false_ne_true, h.start]
      exact V.per_break _
    · rw [if_pos rfl, h.stop]
      exact V.per_break _

theorem mem_vertSet_of_mem_fibre (SF : M.SideFacts) (V : M.VertFacts hF hrat) {P : Place ℂ F}
    (hxP : M.x ∈ P.toValuationSubring) (hv : Place.evalAt P M.x ∈ V.B₀) :
    P ∈ (M.toAssembly hF hrat).VertSet := by
  obtain ⟨p, hp, k, hk⟩ := V.break_of_mem _ hv

  have hvK : Place.evalAt P M.x ∈ (M.base p).K := by
    rcases hk with hk | hk <;> (rw [hk]; exact loop_mem_K _ _)
  rw [base_K] at hvK
  obtain ⟨C, hCp, hPC⟩ := M.exists_cell_over_square hF hrat hp hxP hvK

  have hsh : M.Shares (M.regionOf hF hrat C) ((M.base p).arcSet k) := by
    rw [hCp]
    show p ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi ∧ ∃ k' : Fin (M.base p).N, (M.base p).arcSet k' = (M.base p).arcSet k
    exact ⟨hp, k, rfl⟩
  have hle : (M.base p).φs k.castSucc ≤ (M.base p).φs k.succ := ((M.base p).hmono Fin.castSucc_lt_succ).le
  have hvZ : Place.evalAt P M.x ∈ (M.base p).arcSet k := by
    rcases hk with hk | hk
    · exact ⟨_, ⟨le_rfl, hle⟩, hk.symm⟩
    · exact ⟨_, ⟨hle, le_rfl⟩, hk.symm⟩
  obtain ⟨k', hPk', hlies⟩ := M.exists_arc_through hF hrat C hxP hPC hsh hvZ

  rcases M.exists_pres hF hrat ⟨C, k'⟩ with ⟨p', k'', α, h⟩ | ⟨k₀, α, h⟩
  · have hpp : p' = p := by
      have h1 := h.region
      rw [hCp] at h1
      exact (Option.some.inj h1).symm
    subst hpp
    have hkk : k'' = k := SF.base_inj _ hp _ _ (LiesOver.eq M h.lies hlies)
    subst hkk

    rcases hk with hk | hk
    · have hE : ((M.toAssembly hF hrat).cellOf C).bdry (((M.toAssembly hF hrat).cellOf C).R.φs k'.castSucc) ∈
          M.arcPlaces hF hrat ⟨C, k'⟩ :=
        bdry_mem_arc ((M.toAssembly hF hrat).cellOf C) ⟨le_rfl, (((M.toAssembly hF hrat).cellOf C).R.hmono Fin.castSucc_lt_succ).le⟩
      have hval : Place.evalAt P M.x = Place.evalAt (((M.toAssembly hF hrat).cellOf C).bdry
          (((M.toAssembly hF hrat).cellOf C).R.φs k'.castSucc)) M.x := by
        rw [h.read (((M.toAssembly hF hrat).cellOf C).R.φs k'.castSucc)
          ⟨le_rfl, (((M.toAssembly hF hrat).cellOf C).R.hmono Fin.castSucc_lt_succ).le⟩, h.start, hk]
      have hPE := M.injOn_evalAt_arcPlaces hF hrat ⟨C, k'⟩ hPk' hE hval
      rw [hPE]
      exact (M.toAssembly hF hrat).endPt_mem_vertSet ⟨C, k'⟩ false
    · have hE : ((M.toAssembly hF hrat).cellOf C).bdry (((M.toAssembly hF hrat).cellOf C).R.φs k'.succ) ∈
          M.arcPlaces hF hrat ⟨C, k'⟩ :=
        bdry_mem_arc ((M.toAssembly hF hrat).cellOf C) ⟨(((M.toAssembly hF hrat).cellOf C).R.hmono Fin.castSucc_lt_succ).le, le_rfl⟩
      have hval : Place.evalAt P M.x = Place.evalAt (((M.toAssembly hF hrat).cellOf C).bdry
          (((M.toAssembly hF hrat).cellOf C).R.φs k'.succ)) M.x := by
        rw [h.read (((M.toAssembly hF hrat).cellOf C).R.φs k'.succ)
          ⟨(((M.toAssembly hF hrat).cellOf C).R.hmono Fin.castSucc_lt_succ).le, le_rfl⟩, h.stop, hk]
      have hPE := M.injOn_evalAt_arcPlaces hF hrat ⟨C, k'⟩ hPk' hE hval
      rw [hPE]
      exact (M.toAssembly hF hrat).endPt_mem_vertSet ⟨C, k'⟩ true
  · exfalso
    have h1 := h.region
    rw [hCp] at h1
    exact Option.some_ne_none p h1

theorem mem_vertSet_iff (SF : M.SideFacts) (V : M.VertFacts hF hrat) (P : Place ℂ F) :
    P ∈ (M.toAssembly hF hrat).VertSet ↔ ∃ v ∈ V.B₀, P ∈ M.fibre v := by
  constructor
  · rintro ⟨⟨a, b⟩, rfl⟩
    obtain ⟨hx, hv⟩ := M.endPt_mem_fibre_B₀ hF hrat V a b
    exact ⟨_, hv, (M.mem_fibre).mpr ⟨hx, rfl⟩⟩
  · rintro ⟨v, hv, hPv⟩
    obtain ⟨hx, hPv⟩ := (M.mem_fibre).mp hPv
    exact M.mem_vertSet_of_mem_fibre hF hrat SF V hx (by rw [hPv]; exact hv)

theorem card_idxV (SF : M.SideFacts) (V : M.VertFacts hF hrat) :
    Fintype.card (M.toAssembly hF hrat).IdxV = (M.toAssembly hF hrat).n * CellCount.V₀ (M.toAssembly hF hrat) := by
  classical
  have hset : (M.toAssembly hF hrat).VertSet = ↑(V.B₀.biUnion M.fibre) := by
    ext P
    rw [M.mem_vertSet_iff hF hrat SF V P, Finset.mem_coe, Finset.mem_biUnion]
  have hdisj : ∀ v ∈ V.B₀, ∀ v' ∈ V.B₀, v ≠ v' → Disjoint (M.fibre v) (M.fibre v') := by
    intro v _ v' _ hne
    rw [Finset.disjoint_left]
    intro P hP hP'
    obtain ⟨-, h⟩ := (M.mem_fibre).mp hP
    obtain ⟨-, h'⟩ := (M.mem_fibre).mp hP'
    exact hne (h.symm.trans h')
  have hsum : (V.B₀.biUnion M.fibre).card = V.B₀.card * M.n := by
    rw [Finset.card_biUnion (by intro v hv v' hv' hne; exact hdisj v hv v' hv' hne)]
    rw [Finset.sum_const_nat (m := M.n)]
    intro v hv
    exact M.hcard v (M.not_mem_bad_of_vertFacts hF hrat V hv)
  rw [Fintype.card_eq_nat_card]
  change Nat.card ↥(M.toAssembly hF hrat).VertSet = _
  rw [Nat.card_coe_set_eq, hset, Set.ncard_coe_finset, hsum, V.card_B₀]
  show CellCount.V₀ (M.toAssembly hF hrat) * M.n = M.n * CellCount.V₀ (M.toAssembly hF hrat)
  ring

end DissectionMaterials.Materials
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.AssemblyData P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.EdgeData"
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.AssemblyData P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.EdgeData"

end Part_D1Vert
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.AssemblyData P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.EdgeData"

section Part_D1CountWire

set_option autoImplicit false

p2m_open "AlgebraicCurve~H1 Set P2MW.S_AlgebraicCurve_exists_pairedCellFamily.PlanarRegions P2MW.S_AlgebraicCurve_exists_pairedCellFamily.DissectionMaterials P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily"
open scoped Manifold ContDiff Topology Real

namespace DissectionMaterials
namespace Materials

variable {F : Type*} [Field F] [Algebra ℂ F] [TopologicalSpace (Place ℂ F)]
variable [ChartedSpace ℂ (Place ℂ F)]
variable {S : Finset (Place ℂ F)} {P₀ : Place ℂ F}
variable (M : Materials F S P₀) [Planar] [IsCurveOver ℂ F] [T2Space (Place ℂ F)]
variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]
variable (hF : OrdPack F) (hrat : ∀ P : Place ℂ F, P.IsRational)

theorem N_plain (Q : (M.toAssembly hF hrat).plain_finite.toFinset) (i : Fin M.n) :
    ((M.toAssembly hF hrat).cellOf (Sum.inl ⟨Q, i⟩)).R.N = 6 := by
  show (M.base Q.1).N = 6
  exact M.base_N Q.1

theorem N_cap (Q : (M.toAssembly hF hrat).caps_finite.toFinset)
    (w : (M.toAssembly hF hrat).Fib ((M.toAssembly hF hrat).capVal Q)) :
    ((M.toAssembly hF hrat).cellOf (Sum.inr (Sum.inl ⟨Q, w⟩))).R.N
      = 6 * M.cape ((M.toAssembly hF hrat).capVal Q) w.1 := by
  have hQ := (M.toAssembly hF hrat).mem_caps_iff.mp
    ((M.toAssembly hF hrat).caps_finite.mem_toFinset.mp Q.2)
  obtain ⟨b, hb, -, hbd⟩ := M.exists_capAt_eq hQ.2
  have hw := w.2
  change M.x ∈ w.1.toValuationSubring ∧ Place.evalAt w.1 M.x = (M.capAt Q.1).getD 0 at hw
  rw [hbd] at hw
  have he : M.cape b w.1 ≠ 0 := (M.hcapchart b hb w.1 hw.1 hw.2).e_pos.ne'
  show (M.capRegion Q.1 ((M.capAt Q.1).getD 0) w.1).N = 6 * M.cape ((M.capAt Q.1).getD 0) w.1
  simp only [hbd]
  rw [M.capRegion_eq he, efold_N, base_N]
  exact Nat.mul_comm _ _

theorem N_inf (w : (M.toAssembly hF hrat).FibInf) :
    ((M.toAssembly hF hrat).cellOf (Sum.inr (Sum.inr w))).R.N
      = M.infe w.1 * CellCount.Nperim (M.toAssembly hF hrat) := by
  have hw : M.x ∉ w.1.toValuationSubring := w.2
  have he : M.infe w.1 ≠ 0 := (M.hinfchart w.1 hw).e_pos.ne'
  show (M.infRegion w.1).N = _
  rw [M.infRegion_eq he, efold_N, infBase_N, winReg_N]
  rfl

theorem capVal_spec (Q : (M.toAssembly hF hrat).caps_finite.toFinset) :
    (M.toAssembly hF hrat).capVal Q ∈ M.Bad ∧
      M.capAt Q.1 = some ((M.toAssembly hF hrat).capVal Q) := by
  have hQ := ((M.toAssembly hF hrat).mem_caps_iff.mp
    ((M.toAssembly hF hrat).caps_finite.mem_toFinset.mp Q.2)).2
  obtain ⟨b, hb, hQb, hgetD⟩ := M.exists_capAt_eq hQ
  have hval : (M.toAssembly hF hrat).capVal Q = b := hgetD
  rw [hval]
  exact ⟨hb, hQb⟩

theorem sq_capVal (Q : (M.toAssembly hF hrat).caps_finite.toFinset) :
    M.sq ((M.toAssembly hF hrat).capVal Q) = Q.1 := by
  have h := (M.hcap Q.1 _).mp (M.capVal_spec hF hrat Q).2
  exact Prod.ext h.2.1 h.2.2

theorem sq_mem_caps {b : ℂ} (hb : b ∈ M.Bad) :
    M.sq b ∈ (M.toAssembly hF hrat).caps_finite.toFinset := by
  refine (M.toAssembly hF hrat).caps_finite.mem_toFinset.mpr
    ((M.toAssembly hF hrat).mem_caps_iff.mpr ⟨M.sq_mem_win_of_norm_lt (M.hbadR b hb), ?_⟩)
  show M.capAt (M.sq b) ≠ none
  rw [M.capAt_sq hb]
  exact Option.some_ne_none b

theorem capVal_sq {b : ℂ} (hb : b ∈ M.Bad) : (M.toAssembly hF hrat).capVal (M.sq b) = b := by
  show (M.capAt (M.sq b)).getD 0 = b
  simp [M.capAt_sq hb]

theorem sum_fib_eq {β : Type*} [AddCommMonoid β] (b : ℂ) (f : Place ℂ F → β) :
    ∑ w : (M.toAssembly hF hrat).Fib b, f w.1 = ∑ w ∈ (M.hfib b).toFinset, f w :=
  (Finset.sum_subtype (M.hfib b).toFinset (fun _ => (M.hfib b).mem_toFinset) f).symm

theorem sum_fibInf_eq {β : Type*} [AddCommMonoid β] (f : Place ℂ F → β) :
    ∑ w : (M.toAssembly hF hrat).FibInf, f w.1 = ∑ w ∈ M.hpoles.toFinset, f w :=
  (Finset.sum_subtype M.hpoles.toFinset (fun _ => M.hpoles.mem_toFinset) f).symm

theorem sum_cape_of_mem
    (hcape : ∀ b ∈ M.Bad, ∀ w : Place ℂ F, M.x ∈ w.toValuationSubring → Place.evalAt w M.x = b →
      M.cape b w = (w.ord (M.x - algebraMap ℂ F b)).toNat)
    {b : ℂ} (hb : b ∈ M.Bad) :
    ∑ w : (M.toAssembly hF hrat).Fib b, M.cape b w.1 = M.n := by
  haveI := M.hfd
  calc ∑ w : (M.toAssembly hF hrat).Fib b, M.cape b w.1
      = ∑ w ∈ (M.hfib b).toFinset, M.cape b w := M.sum_fib_eq hF hrat b (M.cape b)
    _ = ∑ w ∈ (M.hfib b).toFinset, FibreDegree.eFin M.x w b := by
        refine Finset.sum_congr rfl (fun w hw => ?_)
        have hw' : M.x ∈ w.toValuationSubring ∧ Place.evalAt w M.x = b :=
          (M.hfib b).mem_toFinset.mp hw
        exact hcape b hb w hw'.1 hw'.2
    _ = FibreDegree.deg M.x :=
        FibreDegree.sum_eFin M.x M.hx b (M.hfib b).toFinset (fun w => (M.hfib b).mem_toFinset)
    _ = M.n := M.hdeg.symm

theorem sum_cap
    (hcape : ∀ b ∈ M.Bad, ∀ w : Place ℂ F, M.x ∈ w.toValuationSubring → Place.evalAt w M.x = b →
      M.cape b w = (w.ord (M.x - algebraMap ℂ F b)).toNat)
    (Q : (M.toAssembly hF hrat).caps_finite.toFinset) :
    ∑ w : (M.toAssembly hF hrat).Fib ((M.toAssembly hF hrat).capVal Q),
      M.cape ((M.toAssembly hF hrat).capVal Q) w.1 = M.n :=
  M.sum_cape_of_mem hF hrat hcape (M.capVal_spec hF hrat Q).1

theorem sum_inf
    (hinfe : ∀ w : Place ℂ F, M.x ∉ w.toValuationSubring → M.infe w = (w.ord M.x⁻¹).toNat) :
    ∑ w : (M.toAssembly hF hrat).FibInf, M.infe w.1 = M.n := by
  haveI := M.hfd
  calc ∑ w : (M.toAssembly hF hrat).FibInf, M.infe w.1
      = ∑ w ∈ M.hpoles.toFinset, M.infe w := M.sum_fibInf_eq hF hrat M.infe
    _ = ∑ w ∈ M.hpoles.toFinset, FibreDegree.eInf M.x w :=
        Finset.sum_congr rfl (fun w hw => hinfe w (M.hpoles.mem_toFinset.mp hw))
    _ = FibreDegree.deg M.x :=
        FibreDegree.sum_eInf M.x M.hx M.hpoles.toFinset (fun w => M.hpoles.mem_toFinset)
    _ = M.n := M.hdeg.symm

theorem rh [HasCanonicalDivisor (K := ℂ) (F := F)]
    (hcape : ∀ b ∈ M.Bad, ∀ w : Place ℂ F, M.x ∈ w.toValuationSubring → Place.evalAt w M.x = b →
      M.cape b w = (w.ord (M.x - algebraMap ℂ F b)).toNat)
    (hinfe : ∀ w : Place ℂ F, M.x ∉ w.toValuationSubring → M.infe w = (w.ord M.x⁻¹).toNat) :
    (∑ Q : (M.toAssembly hF hrat).caps_finite.toFinset,
        ∑ w : (M.toAssembly hF hrat).Fib ((M.toAssembly hF hrat).capVal Q),
          ((M.cape ((M.toAssembly hF hrat).capVal Q) w.1 : ℤ) - 1))
      + ∑ w : (M.toAssembly hF hrat).FibInf, ((M.infe w.1 : ℤ) - 1)
      = 2 * (Module.finrank ℂ ↥(regularDifferentials ℂ F) : ℤ) - 2 + 2 * (M.n : ℤ) := by
  haveI := M.hfd

  have hinner : ∀ b ∈ M.Bad,
      ∑ w : (M.toAssembly hF hrat).Fib b, ((M.cape b w.1 : ℤ) - 1)
        = ∑ w ∈ (M.hfib b).toFinset, ((FibreDegree.eFin M.x w b : ℤ) - 1) := by
    intro b hb
    refine (M.sum_fib_eq hF hrat b (fun w => ((M.cape b w : ℤ) - 1))).trans ?_
    refine Finset.sum_congr rfl (fun w hw => ?_)
    have hw' : M.x ∈ w.toValuationSubring ∧ Place.evalAt w M.x = b :=
      (M.hfib b).mem_toFinset.mp hw
    exact congrArg (fun k : ℕ => (k : ℤ) - 1) (hcape b hb w hw'.1 hw'.2)

  have hcaps : (∑ Q : (M.toAssembly hF hrat).caps_finite.toFinset,
        ∑ w : (M.toAssembly hF hrat).Fib ((M.toAssembly hF hrat).capVal Q),
          ((M.cape ((M.toAssembly hF hrat).capVal Q) w.1 : ℤ) - 1))
      = ∑ b ∈ M.Bad, ∑ w ∈ (M.hfib b).toFinset, ((FibreDegree.eFin M.x w b : ℤ) - 1) :=
    Finset.sum_bij' (fun Q _ => (M.toAssembly hF hrat).capVal Q)
      (fun b hb => ⟨M.sq b, M.sq_mem_caps hF hrat hb⟩)
      (fun Q _ => (M.capVal_spec hF hrat Q).1) (fun _ _ => Finset.mem_univ _)
      (fun Q _ => Subtype.ext (M.sq_capVal hF hrat Q)) (fun b hb => M.capVal_sq hF hrat hb)
      (fun Q _ => hinner _ (M.capVal_spec hF hrat Q).1)

  have hinf : ∑ w : (M.toAssembly hF hrat).FibInf, ((M.infe w.1 : ℤ) - 1)
      = ∑ w ∈ M.hpoles.toFinset, ((FibreDegree.eInf M.x w : ℤ) - 1) := by
    refine (M.sum_fibInf_eq hF hrat (fun w => ((M.infe w : ℤ) - 1))).trans ?_
    refine Finset.sum_congr rfl (fun w hw => ?_)
    exact congrArg (fun k : ℕ => (k : ℤ) - 1) (hinfe w (M.hpoles.mem_toFinset.mp hw))

  have hB : ∀ (b : ℂ) (w : Place ℂ F), w ∈ FibreDegree.fib M.x b → FibreDegree.eFin M.x w b ≠ 1 →
      b ∈ M.Bad := by
    intro b w hw hne
    by_contra hb
    have hw' : M.x ∈ w.toValuationSubring ∧ Place.evalAt w M.x = b := hw
    have hord := M.ord_eq_one_of_card_fiber hb hw'.1 hw'.2
    apply hne
    unfold FibreDegree.eFin
    omega
  have key := FibreDegree.rh_count M.x M.hx M.Bad hB (fun b => (M.hfib b).toFinset)
    (fun b w => (M.hfib b).mem_toFinset) M.hpoles.toFinset (fun w => M.hpoles.mem_toFinset)
  rw [hcaps, hinf, M.hdeg]
  exact key

end DissectionMaterials.Materials
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.AssemblyData P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.EdgeData"
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.AssemblyData P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.EdgeData"

end Part_D1CountWire
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.AssemblyData P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.EdgeData"

section Part_D1Transport

set_option autoImplicit false

p2m_open "AlgebraicCurve~H1 Set P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily"

namespace IndexTransport

variable {F : Type*} [Field F] [Algebra ℂ F] [TopologicalSpace (Place ℂ F)]
variable [ChartedSpace ℂ (Place ℂ F)]
variable (A : AssemblyData F)

noncomputable def m : ℕ := Fintype.card A.IdxC

noncomputable def e : A.IdxC ≃ Fin (m A) := Fintype.equivFin A.IdxC

noncomputable def cellT (i : Fin (m A)) : Cell F := A.cellOf ((e A).symm i)

noncomputable def τ : (Σ i : Fin (m A), Fin (cellT A i).R.N) ≃ A.ArcIdx :=
  Equiv.sigmaCongrLeft (β := fun C : A.IdxC => Fin (A.cellOf C).R.N) (e A).symm

theorem τ_apply (i : Fin (m A)) (k : Fin (cellT A i).R.N) :
    τ A ⟨i, k⟩ = (⟨(e A).symm i, k⟩ : A.ArcIdx) := rfl

variable {A} (E : EdgeData A)

noncomputable def pairT (a : Σ i : Fin (m A), Fin (cellT A i).R.N) : Σ i : Fin (m A), Fin (cellT A i).R.N :=
  (τ A).symm (E.pair (τ A a))

noncomputable def orientT (a : Σ i : Fin (m A), Fin (cellT A i).R.N) : Bool := E.orient (τ A a)

theorem pairT_pairT (a : Σ i : Fin (m A), Fin (cellT A i).R.N) : pairT E (pairT E a) = a := by
  unfold pairT
  rw [(τ A).apply_symm_apply, E.hpair, (τ A).symm_apply_apply]

theorem orientT_pairT (a : Σ i : Fin (m A), Fin (cellT A i).R.N) : orientT E (pairT E a) = !orientT E a := by
  unfold orientT pairT
  rw [(τ A).apply_symm_apply, E.horient]

theorem pairT_eq {i : Fin (m A)} {k : Fin (cellT A i).R.N} {i' : Fin (m A)} {k' : Fin (cellT A i').R.N}
    (h : E.pair ⟨(e A).symm i, k⟩ = ⟨(e A).symm i', k'⟩) : pairT E ⟨i, k⟩ = ⟨i', k'⟩ := by
  unfold pairT
  rw [τ_apply, h]
  exact (τ A).symm_apply_apply ⟨i', k'⟩

theorem pair_eq_of_pairT {i : Fin (m A)} {k : Fin (cellT A i).R.N} {i' : Fin (m A)} {k' : Fin (cellT A i').R.N}
    (h : pairT E ⟨i, k⟩ = ⟨i', k'⟩) : E.pair ⟨(e A).symm i, k⟩ = ⟨(e A).symm i', k'⟩ := by
  unfold pairT at h
  rw [τ_apply] at h
  exact ((τ A).symm_apply_eq.mp h)

abbrev StepA (x : Place ℂ F) (X Y : A.IdxC) : Prop :=
  ∃ (k : Fin (A.cellOf X).R.N) (k' : Fin (A.cellOf Y).R.N), E.pair ⟨X, k⟩ = ⟨Y, k'⟩ ∧ x ∈ (A.cellOf X).arc k

abbrev StepT (x : Place ℂ F) (X Y : Fin (m A)) : Prop :=
  ∃ (k : Fin (cellT A X).R.N) (k' : Fin (cellT A Y).R.N), pairT E ⟨X, k⟩ = ⟨Y, k'⟩ ∧ x ∈ (cellT A X).arc k

theorem stepT_of_stepA (x : Place ℂ F) (i i' : Fin (m A)) (h : StepA E x ((e A).symm i) ((e A).symm i')) :
    StepT E x i i' := by
  obtain ⟨k, k', hp, hx⟩ := h
  exact ⟨k, k', pairT_eq E hp, hx⟩

theorem reflTransGen_stepT (x : Place ℂ F) {C C' : A.IdxC} (h : Relation.ReflTransGen (StepA E x) C C') :
    ∀ i i' : Fin (m A), (e A).symm i = C → (e A).symm i' = C' → Relation.ReflTransGen (StepT E x) i i' := by
  induction h with
  | refl =>
    intro i i' hi hi'
    have hii : i = i' := (e A).symm.injective (hi.trans hi'.symm)
    subst hii
    exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih =>
    intro i i' hi hi'
    have hb : (e A).symm (e A b) = b := (e A).symm_apply_apply b
    have h1 := ih i (e A b) hi hb
    subst hi'
    rw [← hb] at hbc
    exact h1.tail (stepT_of_stepA E x _ _ hbc)

theorem vertSet_eq :
    {v : Place ℂ F | ∃ (i : Fin (m A)) (k : Fin (cellT A i).R.N),
        v = (cellT A i).bdry ((cellT A i).R.φs k.castSucc) ∨ v = (cellT A i).bdry ((cellT A i).R.φs k.succ)} =
      A.VertSet := by
  ext v
  constructor
  · rintro ⟨i, k, h | h⟩
    · exact ⟨(⟨(e A).symm i, k⟩, false), h.symm⟩
    · exact ⟨(⟨(e A).symm i, k⟩, true), h.symm⟩
  · rintro ⟨⟨⟨C, k⟩, b⟩, rfl⟩
    obtain ⟨i, rfl⟩ := (e A).symm.surjective C
    cases b
    · exact ⟨i, k, Or.inl (A.endPt_false ⟨(e A).symm i, k⟩)⟩
    · exact ⟨i, k, Or.inr (A.endPt_true ⟨(e A).symm i, k⟩)⟩

theorem ncard_vertSet : A.VertSet.ncard = Fintype.card A.IdxV := by
  rw [Fintype.card_eq_nat_card]
  exact (Nat.card_coe_set_eq A.VertSet).symm

theorem sum_cellT : ∑ i : Fin (m A), ((cellT A i).R.N : ℤ) = ∑ C : A.IdxC, ((A.cellOf C).R.N : ℤ) :=
  Equiv.sum_comp (e A).symm (fun C : A.IdxC => ((A.cellOf C).R.N : ℤ))

theorem exists_pairedCellFamily_of_edgeData
    (hcover : ∀ w : Place ℂ F, ∃ C : A.IdxC, w ∈ (A.cellOf C).carrier)
    (hstar : ∀ (C C' : A.IdxC) (x : Place ℂ F), x ∈ (A.cellOf C).carrier → x ∈ (A.cellOf C').carrier →
      Relation.ReflTransGen (StepA E x) C C')
    (P₀ : Place ℂ F) (S : Finset (Place ℂ F))
    (hmarked : ∀ v ∈ insert P₀ (S : Set (Place ℂ F)), ∃ C : A.IdxC,
      v ∈ (A.cellOf C).interior' ∧ (A.cellOf C).ζ v = (A.cellOf C).R.q)
    (hsub : ∀ C : A.IdxC, ((A.cellOf C).carrier ∩ (S : Set (Place ℂ F))).Subsingleton)
    (g : ℤ)
    (heuler : (Fintype.card A.IdxV : ℤ) - (Fintype.card E.IdxE : ℤ) + (Fintype.card A.IdxC : ℤ) = 2 - 2 * g) :
    ∃ (m : ℕ) (cell : Fin m → Cell F)
      (pair : (Σ C : Fin m, Fin (cell C).R.N) → (Σ C : Fin m, Fin (cell C).R.N))
      (orient : (Σ C : Fin m, Fin (cell C).R.N) → Bool),
      (∀ a, pair (pair a) = a) ∧
      (∀ a, orient (pair a) = !orient a) ∧
      (∀ (C : Fin m) (k : Fin (cell C).R.N) (C' : Fin m) (k' : Fin (cell C').R.N),
        pair ⟨C, k⟩ = ⟨C', k'⟩ → orient ⟨C, k⟩ = true →
        ∃ ψ : ℝ → ℝ,
          StrictAntiOn ψ ((cell C').R.arcIcc k') ∧
          ContDiffOn ℝ 1 ψ ((cell C').R.arcIcc k') ∧
          ψ ((cell C').R.φs k'.castSucc) = (cell C).R.φs k.succ ∧
          ψ ((cell C').R.φs k'.succ) = (cell C).R.φs k.castSucc ∧
          ∀ t ∈ (cell C').R.arcIcc k', (cell C').bdry t = (cell C).bdry (ψ t)) ∧
      (∀ w : Place ℂ F, ∃ C : Fin m, w ∈ (cell C).carrier) ∧
      (∀ (C C' : Fin m) (x : Place ℂ F), x ∈ (cell C).carrier → x ∈ (cell C').carrier →
        Relation.ReflTransGen
          (fun X Y : Fin m => ∃ (k : Fin (cell X).R.N) (k' : Fin (cell Y).R.N),
            pair ⟨X, k⟩ = ⟨Y, k'⟩ ∧ x ∈ (cell X).arc k) C C') ∧
      (∀ v ∈ insert P₀ (S : Set (Place ℂ F)), ∃ C : Fin m, v ∈ (cell C).interior') ∧
      (∀ C : Fin m, ((cell C).carrier ∩ (S : Set (Place ℂ F))).Subsingleton) ∧
      (2 * ({v : Place ℂ F | ∃ (C : Fin m) (k : Fin (cell C).R.N),
        v = (cell C).bdry ((cell C).R.φs k.castSucc) ∨ v = (cell C).bdry ((cell C).R.φs k.succ)}.ncard : ℤ)
        - (∑ C : Fin m, ((cell C).R.N : ℤ)) + 2 * (m : ℤ) = 2 * (2 - 2 * g)) ∧
      (∀ v ∈ (S : Set (Place ℂ F)), ∃ C : Fin m, v ∈ (cell C).interior' ∧ (cell C).ζ v = (cell C).R.q) := by
  refine ⟨m A, cellT A, pairT E, orientT E, pairT_pairT E, orientT_pairT E, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro i k i' k' hp ho
    exact E.hrev ((e A).symm i) k ((e A).symm i') k' (pair_eq_of_pairT E hp) ho
  ·
    intro w
    obtain ⟨C, hC⟩ := hcover w
    obtain ⟨i, rfl⟩ := (e A).symm.surjective C
    exact ⟨i, hC⟩
  ·
    intro i i' x hx hx'
    exact reflTransGen_stepT E x (hstar ((e A).symm i) ((e A).symm i') x hx hx') i i' rfl rfl
  ·
    intro v hv
    obtain ⟨C, hC, -⟩ := hmarked v hv
    obtain ⟨i, rfl⟩ := (e A).symm.surjective C
    exact ⟨i, hC⟩
  ·
    intro i
    exact hsub ((e A).symm i)
  ·
    rw [vertSet_eq, ncard_vertSet, sum_cellT]
    have h1 := CellCount.card_arcIdx A E
    have h2 := CellCount.card_arcIdx_eq_sum A
    have h3 : ((∑ C : A.IdxC, (A.cellOf C).R.N : ℕ) : ℤ) = ∑ C : A.IdxC, ((A.cellOf C).R.N : ℤ) :=
      Nat.cast_sum _ _
    rw [← h3, ← h2, h1]
    show 2 * (Fintype.card A.IdxV : ℤ) - ((2 * Fintype.card E.IdxE : ℕ) : ℤ) + 2 * (Fintype.card A.IdxC : ℤ)
      = 2 * (2 - 2 * g)
    push_cast
    linarith
  ·
    intro v hv
    obtain ⟨C, hC, hζ⟩ := hmarked v (Set.mem_insert_of_mem _ hv)
    obtain ⟨i, rfl⟩ := (e A).symm.surjective C
    exact ⟨i, hC, hζ⟩

end IndexTransport
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.AssemblyData P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.EdgeData"

end Part_D1Transport
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.AssemblyData P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.EdgeData"

section Part_D1Pack

set_option autoImplicit false

p2m_open "AlgebraicCurve~H1 Set"
open scoped Manifold ContDiff Topology

open DissectionMaterials in

theorem DissectionMaterials.exists_materials
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
    (P₀ : Place ℂ F) (S : Finset (Place ℂ F)) :
    ∃ M : Materials F S P₀,
      (∀ b ∈ M.Bad, ∀ w : Place ℂ F, M.x ∈ w.toValuationSubring → Place.evalAt w M.x = b →
        M.cape b w = (w.ord (M.x - algebraMap ℂ F b)).toNat) ∧
      (∀ w : Place ℂ F, M.x ∉ w.toValuationSubring → M.infe w = (w.ord M.x⁻¹).toNat) := by
  obtain ⟨x, n, Bad, o, hm, jlo, jhi, klo, khi, Rw, capAt, margin, sheet, capζ, capρ, cape, cs, infζ, infρ, infe, centre, h_hx, h_hfd, h_hn, h_hdeg, h_hfib, h_hcard, h_hpoles, h_hhm, h_hjlt, h_hklt, h_hRw, h_hwin, h_hinner, h_hbadR, h_hbad_off, h_hbad_sep, h_hcap, h_hperim_plain, h_hmargin_open, h_hmargin_sq, h_hmargin_bad, h_hsheet, h_hcs, h_hcs_sep, h_hcapchart, h_hcapbig, h_hcapdisj, h_hcapexhaust, h_hinfchart, h_hinfbig, h_hinfdisj, h_hinfexhaust, h_hcentre, h_hcentre0, h_hmarked, h_hmarked_sep, h_hmarked_R⟩ :=
    AlgebraicCurve.exists_dissectionScaleData F hfg hF P₀ S
  refine ⟨{
  x := x,
  hx := h_hx,
  hfd := h_hfd,
  n := n,
  hn := h_hn,
  hdeg := h_hdeg,
  Bad := Bad,
  hfib := h_hfib,
  hcard := fun t ht => by
    rw [← Set.ncard_eq_toFinset_card _ (h_hfib t)]
    exact h_hcard t ht,
  hpoles := h_hpoles,
  o := o,
  hm := hm,
  hhm := h_hhm,
  jlo := jlo,
  jhi := jhi,
  klo := klo,
  khi := khi,
  hjlt := h_hjlt,
  hklt := h_hklt,
  Rw := Rw,
  hRw := h_hRw,
  hwin := h_hwin,
  hinner := h_hinner,
  hbadR := h_hbadR,
  hbad_off := h_hbad_off,
  hbad_sep := h_hbad_sep,
  capAt := capAt,
  hcap := h_hcap,
  hperim_plain := h_hperim_plain,
  margin := margin,
  sheet := sheet,
  hmargin_open := h_hmargin_open,
  hmargin_sq := fun p hw hp => h_hmargin_sq p hw hp,
  hmargin_bad := h_hmargin_bad,
  hsheet := fun p hw hp => by
    obtain ⟨h1, h2, h3, h4⟩ := h_hsheet p hw hp
    exact ⟨h1, h2, h3, h4⟩,
  capζ := capζ,
  capρ := capρ,
  cape := cape,
  cs := cs,
  hcs := h_hcs,
  hcs_sep := h_hcs_sep,
  hcapchart := fun b hb w hw hwb => by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -⟩ := h_hcapchart b hb w hw hwb
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩,
  hcapbig := h_hcapbig,
  hcapdisj := h_hcapdisj,
  hcapexhaust := h_hcapexhaust,
  infζ := infζ,
  infρ := infρ,
  infe := infe,
  hinfchart := fun w hw => by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -⟩ := h_hinfchart w hw
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩,
  hinfbig := h_hinfbig,
  hinfdisj := h_hinfdisj,
  hinfexhaust := h_hinfexhaust,
  centre := centre,
  hcentre := h_hcentre,
  hcentre0 := h_hcentre0,
  hmarked := h_hmarked,
  hmarked_sep := h_hmarked_sep,
  hmarked_R := h_hmarked_R }, ?_, ?_⟩
  · intro b hb w hw hwb
    exact (h_hcapchart b hb w hw hwb).2.2.2.2.2.2.2.2.2
  · intro w hw
    exact (h_hinfchart w hw).2.2.2.2.2.2.2.2.2

end Part_D1Pack
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.AssemblyData P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.EdgeData"

section Part_D1PlanarInst

set_option autoImplicit false

p2m_open "AlgebraicCurve~H1 Set"
open scoped Real

namespace PlanarRegions

noncomputable scoped instance instPlanarOfRows : Planar where
  rect := fun x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁ => Classical.choose (AlgebraicCurve.RadialRegion.exists_rect_sixArcs x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁)
  rect_spec := fun x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁ => Classical.choose_spec (AlgebraicCurve.RadialRegion.exists_rect_sixArcs x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁)
  window := fun o hm hhm jlo jhi klo khi hj hk cy hcy hx₀ hx₁ hy₀ hy₁ hcy0 =>
    Classical.choose (AlgebraicCurve.RadialRegion.exists_window_perimeter o hm hhm jlo jhi klo khi hj hk cy hcy hx₀ hx₁ hy₀ hy₁ hcy0)
  window_spec := fun o hm hhm jlo jhi klo khi hj hk cy hcy hx₀ hx₁ hy₀ hy₁ hcy0 =>
    Classical.choose_spec (AlgebraicCurve.RadialRegion.exists_window_perimeter o hm hhm jlo jhi klo khi hj hk cy hcy hx₀ hx₁ hy₀ hy₁ hcy0)
  recip := fun R hq => Classical.choose (AlgebraicCurve.RadialRegion.exists_recip R hq)
  recip_spec := fun R hq => by
    have h := Classical.choose_spec (AlgebraicCurve.RadialRegion.exists_recip R hq)
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩
  recipIdx := fun R hq => Classical.choose (Classical.choose_spec (AlgebraicCurve.RadialRegion.exists_recip R hq)).2.2.2.2.2.2
  recipIdx_spec := fun R hq => Classical.choose_spec (Classical.choose_spec (AlgebraicCurve.RadialRegion.exists_recip R hq)).2.2.2.2.2.2
  efold := fun R hN e he => Classical.choose (AlgebraicCurve.RadialRegion.exists_pow_pullback_laps R hN e he)
  efold_spec := fun R hN e he => by
    have h := Classical.choose_spec (AlgebraicCurve.RadialRegion.exists_pow_pullback_laps R hN e he)
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩
  lap := fun R hN e he => Classical.choose (Classical.choose_spec (AlgebraicCurve.RadialRegion.exists_pow_pullback_laps R hN e he)).2.2.2.2.2
  lap_spec := fun R hN e he => Classical.choose_spec (Classical.choose_spec (AlgebraicCurve.RadialRegion.exists_pow_pullback_laps R hN e he)).2.2.2.2.2
  across := AlgebraicCurve.RadialRegion.exists_reparam_across_edge
  same := AlgebraicCurve.RadialRegion.exists_reparam_same_side

end PlanarRegions
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.AssemblyData P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.EdgeData P2MW.S_AlgebraicCurve_exists_pairedCellFamily.PlanarRegions"

end Part_D1PlanarInst
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.AssemblyData P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.EdgeData P2MW.S_AlgebraicCurve_exists_pairedCellFamily.PlanarRegions"

section Part_d1_sigma

set_option autoImplicit false

open scoped Manifold ContDiff Topology Real
p2m_open "Set AlgebraicCurve~H1 Complex"

private theorem place_isRational {F : Type*} [Field F] [Algebra ℂ F] [IsCurveOver ℂ F]
    (v : Place ℂ F) : v.IsRational := by
  haveI : Module.Finite ℂ v.ResidueField := IsCurveOver.finiteResidue v
  haveI : Algebra.IsIntegral ℂ v.ResidueField := Algebra.IsIntegral.of_finite ℂ v.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ) (K := v.ResidueField)).2

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
    (P₀ : Place ℂ F) (S : Finset (Place ℂ F)) :
    ∃ (m : ℕ) (cell : Fin m → Cell F)
      (pair : (Σ C : Fin m, Fin (cell C).R.N) → (Σ C : Fin m, Fin (cell C).R.N))
      (orient : (Σ C : Fin m, Fin (cell C).R.N) → Bool),
      (∀ a, pair (pair a) = a) ∧
      (∀ a, orient (pair a) = !orient a) ∧
      (∀ (C : Fin m) (k : Fin (cell C).R.N) (C' : Fin m)
        (k' : Fin (cell C').R.N),
        pair ⟨C, k⟩ = ⟨C', k'⟩ → orient ⟨C, k⟩ = true →
        ∃ ψ : ℝ → ℝ,
          StrictAntiOn ψ ((cell C').R.arcIcc k') ∧
          ContDiffOn ℝ 1 ψ ((cell C').R.arcIcc k') ∧
          ψ ((cell C').R.φs k'.castSucc) = (cell C).R.φs k.succ ∧
          ψ ((cell C').R.φs k'.succ) = (cell C).R.φs k.castSucc ∧
          ∀ t ∈ (cell C').R.arcIcc k', (cell C').bdry t = (cell C).bdry (ψ t)) ∧
      (∀ w : Place ℂ F, ∃ C : Fin m, w ∈ (cell C).carrier) ∧
      (∀ (C C' : Fin m) (x : Place ℂ F), x ∈ (cell C).carrier →
        x ∈ (cell C').carrier → Relation.ReflTransGen
          (fun X Y : Fin m => ∃ (k : Fin (cell X).R.N) (k' : Fin (cell Y).R.N),
            pair ⟨X, k⟩ = ⟨Y, k'⟩ ∧ x ∈ (cell X).arc k) C C') ∧
      (∀ v ∈ insert P₀ (S : Set (Place ℂ F)), ∃ C : Fin m, v ∈ (cell C).interior') ∧
      (∀ C : Fin m, ((cell C).carrier ∩ (S : Set (Place ℂ F))).Subsingleton) ∧
      (2 * ({v : Place ℂ F | ∃ (C : Fin m) (k : Fin (cell C).R.N),
        v = (cell C).bdry ((cell C).R.φs k.castSucc) ∨
          v = (cell C).bdry ((cell C).R.φs k.succ)}.ncard : ℤ)
        - (∑ C : Fin m, ((cell C).R.N : ℤ)) + 2 * (m : ℤ)
        = 2 * (2 - 2 * (Module.finrank ℂ ↥(regularDifferentials ℂ F) : ℤ))) ∧
      (∀ v ∈ (S : Set (Place ℂ F)), ∃ C : Fin m,
        v ∈ (cell C).interior' ∧ (cell C).ζ v = (cell C).R.q) := by
  obtain ⟨M, hcape, hinfe⟩ := DissectionMaterials.exists_materials F hfg hF P₀ S
  have hrat : ∀ P : Place ℂ F, P.IsRational := fun P => place_isRational P
  obtain ⟨sqbit, perbit, B₀, Sh, Co, hinj, hb1, hb2, hr1, hr2, hr3, hSs, hSn, hCs, hCn, h2reg, hstar,
      hcard, hsqb, hperb, hbom, hgrid⟩ :=
    RadialRegion.exists_grid_geometry M.o M.hm M.hhm M.jlo M.jhi M.klo M.khi M.hjlt M.hklt M.ctr
      M.ctr_mem M.zero_mem_window M.cy_zero M.base M.base_spec M.winReg M.winReg_spec
  have hSh : M.Shares = Sh := by
    funext ρ Z
    cases ρ with
    | none => exact propext (hSn Z).symm
    | some p => exact propext (hSs p Z).symm
  have hCo : M.Contains = Co := by
    funext ρ v
    cases ρ with
    | none => exact propext (hCn v).symm
    | some p => exact propext (hCs p v).symm
  have SF : M.SideFacts := ⟨fun p _ k k' h => hinj p k k' h, by rw [hSh]; exact h2reg⟩
  have ST : M.StarFacts := by
    refine ⟨fun v ρ ρ' hv hv' => ?_⟩
    rw [hCo] at hv hv'
    have hAdj : M.Adj v = fun ρ₁ ρ₂ : Option (ℤ × ℤ) => ∃ Z : Set ℂ, Sh ρ₁ Z ∧ Sh ρ₂ Z ∧ v ∈ Z := by
      funext ρ₁ ρ₂
      show (∃ Z : Set ℂ, M.Shares ρ₁ Z ∧ M.Shares ρ₂ Z ∧ v ∈ Z) = _
      rw [hSh]
    rw [hAdj]
    exact hstar v ρ ρ' hv hv'
  have S2 : M.SideFacts2 := ⟨sqbit, perbit, hb1, hb2, hr1, hr2, hr3⟩
  have VF : M.VertFacts hF hrat := ⟨B₀, hcard, hsqb, hperb, hbom, hgrid⟩
  exact IndexTransport.exists_pairedCellFamily_of_edgeData (M.edgeData hF hrat SF S2)
    (M.cover hF hrat)
    (fun C C' x hx hx' => M.star_property hF hrat SF ST C C' hx hx')
    P₀ S (M.marked_centred hF hrat) (M.carrier_inter_marked_subsingleton hF hrat)
    (Module.finrank ℂ ↥(regularDifferentials ℂ F) : ℤ)
    (CellCount.euler (M.toAssembly hF hrat) (M.edgeData hF hrat SF S2)
      (Module.finrank ℂ ↥(regularDifferentials ℂ F) : ℤ)
      (fun Q w => M.cape ((M.toAssembly hF hrat).capVal Q) w.1) (fun w => M.infe w.1)
      (M.N_plain hF hrat) (M.N_cap hF hrat) (M.N_inf hF hrat)
      (M.sum_cap hF hrat hcape) (M.sum_inf hF hrat hinfe)
      (M.card_idxV hF hrat SF VF)
      (M.rh hF hrat hcape hinfe))

end Part_d1_sigma
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.AssemblyData P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily P2MW.S_AlgebraicCurve_exists_pairedCellFamily.CurveCellFamily.EdgeData P2MW.S_AlgebraicCurve_exists_pairedCellFamily.PlanarRegions"

end S_AlgebraicCurve_exists_pairedCellFamily
end P2MW
export P2MW.S_AlgebraicCurve_exists_pairedCellFamily (solution)
