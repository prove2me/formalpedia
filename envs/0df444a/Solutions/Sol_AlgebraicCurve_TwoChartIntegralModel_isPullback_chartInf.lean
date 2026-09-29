-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.isPullback_chartInf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/db731c5e-e2cf-5c0e-acb6-e6ce8e351f23

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isLocalization_chartAlg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isPullback_chartInf

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra R' F] [IsScalarTower R R' F]
    (M : Submonoid R) [IsLocalization M R'] :
    IsPullback
      (Spec.map (CommRingCat.ofHom (AlgebraicCurve.TwoChartIntegralModel.chartBaseChange R F R' {j⁻¹})))
      (Spec.map (CommRingCat.ofHom
        (algebraMap R' (AlgebraicCurve.TwoChartIntegralModel.chartAlgInf R' F j))))
      (Spec.map (CommRingCat.ofHom
        (algebraMap R (AlgebraicCurve.TwoChartIntegralModel.chartAlgInf R F j))))
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := by
  letI : Algebra (AlgebraicCurve.TwoChartIntegralModel.chartAlg R F {j⁻¹})
      (AlgebraicCurve.TwoChartIntegralModel.chartAlg R' F {j⁻¹}) :=
    (AlgebraicCurve.TwoChartIntegralModel.chartBaseChange R F R' {j⁻¹}).toAlgebra
  haveI : IsScalarTower R (AlgebraicCurve.TwoChartIntegralModel.chartAlg R F {j⁻¹})
      (AlgebraicCurve.TwoChartIntegralModel.chartAlg R' F {j⁻¹}) :=
    IsScalarTower.of_algebraMap_eq fun r => rfl
  haveI : IsLocalization
      (Algebra.algebraMapSubmonoid (AlgebraicCurve.TwoChartIntegralModel.chartAlg R F {j⁻¹}) M)
      (AlgebraicCurve.TwoChartIntegralModel.chartAlg R' F {j⁻¹}) :=
    AlgebraicCurve.TwoChartIntegralModel.isLocalization_chartAlg R F R' M {j⁻¹}
  haveI : Algebra.IsPushout R (AlgebraicCurve.TwoChartIntegralModel.chartAlg R F {j⁻¹}) R'
      (AlgebraicCurve.TwoChartIntegralModel.chartAlg R' F {j⁻¹}) :=
    Algebra.isPushout_of_isLocalization M R' _ _
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout R (AlgebraicCurve.TwoChartIntegralModel.chartAlg R F {j⁻¹}) R'
      (AlgebraicCurve.TwoChartIntegralModel.chartAlg R' F {j⁻¹}))

end S_AlgebraicCurve_TwoChartIntegralModel_isPullback_chartInf
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isPullback_chartInf (solution)
