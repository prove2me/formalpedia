-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.exists_ringEquiv_functionField_apply_eq_algebraMap_germ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/51475d31-4ec9-50b8-8d2a-dbbcc70555ce

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_SemistableModel
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_ringEquiv_functionField_apply_eq_algebraMap_germ_iotaFin
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_ringEquiv_functionField_apply_eq_algebraMap_germ_iotaInf_of_iotaFin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_ringEquiv_functionField_apply_eq_algebraMap_germ

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

universe u

theorem solution
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    [IsIntegral (AlgebraicCurve.TwoChartIntegralModel R F j)]
    (hfrac : IsFractionRing ↥(chartAlgFin R F j) F) :
    ∃ φ : F ≃+* (AlgebraicCurve.TwoChartIntegralModel R F j).functionField,
      (∀ (y : ↥(XFin R F j)) (b : ↥(chartAlgFin R F j)),
        φ (b : F) = algebraMap ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk ((ιFin R F j).base y)) (AlgebraicCurve.TwoChartIntegralModel R F j).functionField
          (((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ((ιFin R F j) ''ᵁ ⊤) ((ιFin R F j).base y) ⟨y, trivial, rfl⟩).hom
            (((ιFin R F j).appIso ⊤).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin R F j))).inv.hom b)))) ∧
      (∀ (y : ↥(XInf R F j)) (b : ↥(chartAlgInf R F j)),
        φ (b : F) = algebraMap ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk ((ιInf R F j).base y)) (AlgebraicCurve.TwoChartIntegralModel R F j).functionField
          (((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ((ιInf R F j) ''ᵁ ⊤) ((ιInf R F j).base y) ⟨y, trivial, rfl⟩).hom
            (((ιInf R F j).appIso ⊤).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf R F j))).inv.hom b)))) ∧
      (∀ r : R, φ (algebraMap R F r) = SemistableModel.baseToFunctionField (toBase R F j) r) := by
  obtain ⟨φ, hFin, hconst⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_ringEquiv_functionField_apply_eq_algebraMap_germ_iotaFin R F j hfrac
  exact ⟨φ, hFin,
    AlgebraicCurve.TwoChartIntegralModel.ringEquiv_functionField_apply_eq_algebraMap_germ_iotaInf_of_iotaFin R F j φ hFin,
    hconst⟩

end S_AlgebraicCurve_TwoChartIntegralModel_exists_ringEquiv_functionField_apply_eq_algebraMap_germ
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_ringEquiv_functionField_apply_eq_algebraMap_germ (solution)
