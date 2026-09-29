-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.mem_smoothLocus_toBase_of_asIdeal_eq_bot_of_charZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/679e9950-f665-55a0-95ad-df562364411a

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_smoothOfRelativeDimension_one_pullback_snd_toBase_of_charZero
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_mem_smoothLocus_of_flat_of_smoothOfRelativeDimension_pullback_snd
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_flat_toBase
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_mem_smoothLocus_toBase_of_asIdeal_eq_bot_of_charZero
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing"
p2m_attr_erase "instance" "TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K₀ : Type u) [Field K₀] [CharZero K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) [Fact (j ≠ 0)] (htj : Transcendental R j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    [LocallyOfFinitePresentation (toBase R F j)]
    (y : ↥(AlgebraicCurve.TwoChartIntegralModel R F j)) (hy : ((toBase R F j).base y).asIdeal = ⊥) :
    y ∈ (toBase R F j).smoothLocus := by
  have hinj : Function.Injective (algebraMap R F) := by
    rw [IsScalarTower.algebraMap_eq R K₀ F]
    exact (algebraMap K₀ F).injective.comp (IsFractionRing.injective R K₀)
  haveI : Flat (toBase R F j) := AlgebraicCurve.TwoChartIntegralModel.flat_toBase R F j hinj
  haveI : Flat ((⊤ : (AlgebraicCurve.TwoChartIntegralModel R F j).Opens).ι ≫ toBase R F j) := inferInstance

  have hsm : SmoothOfRelativeDimension 1
      (pullback.snd (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R K₀)))) :=
    AlgebraicCurve.TwoChartIntegralModel.smoothOfRelativeDimension_one_pullback_snd_toBase_of_charZero
      R K₀ F j htj hFD hsep K₀
  haveI := hsm
  have hsm' : SmoothOfRelativeDimension 1
      (pullback.snd ((⊤ : (AlgebraicCurve.TwoChartIntegralModel R F j).Opens).ι ≫ toBase R F j)
        (Spec.map (CommRingCat.ofHom (algebraMap R K₀)))) := by
    rw [← pullbackRightPullbackFstIso_inv_snd_snd (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R K₀)))
      (⊤ : (AlgebraicCurve.TwoChartIntegralModel R F j).Opens).ι]
    have : SmoothOfRelativeDimension (0 + (0 + 1))
        ((pullbackRightPullbackFstIso (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R K₀)))
            (⊤ : (AlgebraicCurve.TwoChartIntegralModel R F j).Opens).ι).inv ≫
          pullback.snd (⊤ : (AlgebraicCurve.TwoChartIntegralModel R F j).Opens).ι
              (pullback.fst (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R K₀)))) ≫
            pullback.snd (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R K₀)))) := inferInstance
    exact this
  refine AlgebraicGeometry.Scheme.Hom.mem_smoothLocus_of_flat_of_smoothOfRelativeDimension_pullback_snd
    (toBase R F j) ⊤ (Spec.map (CommRingCat.ofHom (algebraMap R K₀))) hsm' y trivial ?_

  rw [Scheme.Pullback.range_fst]
  show ((⊤ : (AlgebraicCurve.TwoChartIntegralModel R F j).Opens).ι ≫ toBase R F j).base ⟨y, trivial⟩ ∈
    Set.range (Spec.map (CommRingCat.ofHom (algebraMap R K₀))).base
  refine ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
  apply PrimeSpectrum.ext
  rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply, hy]
  show ((PrimeSpectrum.comap (algebraMap R K₀)) ⟨⊥, Ideal.isPrime_bot⟩).asIdeal = ⊥
  rw [PrimeSpectrum.comap_asIdeal, Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K₀)]

end S_AlgebraicCurve_TwoChartIntegralModel_mem_smoothLocus_toBase_of_asIdeal_eq_bot_of_charZero
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_mem_smoothLocus_toBase_of_asIdeal_eq_bot_of_charZero (solution)
