-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.bijective_algebraMap_globalSections_iff_isIntegrallyClosedIn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/062ee54d-c598-5665-b9ae-e9ea67b39bf8

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_algEquiv_globalSections_chartAlgFin_inf_chartAlgInf
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_chartAlgFin_inf_chartAlgInf_eq_integralClosure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_bijective_algebraMap_globalSections_iff_isIntegrallyClosedIn

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel

theorem solution
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (toBase R F j) ⊤
    Function.Bijective (algebraMap R Γ(AlgebraicCurve.TwoChartIntegralModel R F j, ⊤)) ↔
      IsIntegrallyClosedIn R F := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (toBase R F j) ⊤
  obtain ⟨e, -, -⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_algEquiv_globalSections_chartAlgFin_inf_chartAlgInf R F j
  let e' : Γ(AlgebraicCurve.TwoChartIntegralModel R F j, ⊤) ≃ₐ[R] integralClosure R F :=
    e.trans (Subalgebra.equivOfEq _ _
      (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin_inf_chartAlgInf_eq_integralClosure R F j))
  have key : Function.Bijective (algebraMap R Γ(AlgebraicCurve.TwoChartIntegralModel R F j, ⊤)) ↔
      Function.Bijective (algebraMap R (integralClosure R F)) := by
    rw [show (⇑(algebraMap R (integralClosure R F))) =
        e' ∘ ⇑(algebraMap R Γ(AlgebraicCurve.TwoChartIntegralModel R F j, ⊤)) from
      funext fun r => (e'.commutes r).symm]
    exact (Function.Bijective.of_comp_iff' e'.bijective _).symm
  rw [key, isIntegrallyClosedIn_iff]
  constructor
  · rintro ⟨hinj, hsurj⟩
    refine ⟨fun a b hab => hinj (Subtype.ext ?_), fun {x} hx => ?_⟩
    · simpa only [Subalgebra.coe_algebraMap] using hab
    · obtain ⟨y, hy⟩ := hsurj ⟨x, hx⟩
      exact ⟨y, by simpa only [Subalgebra.coe_algebraMap] using congrArg Subtype.val hy⟩
  · rintro ⟨hinj, hsurj⟩
    refine ⟨fun a b hab => hinj ?_, fun x => ?_⟩
    · simpa only [Subalgebra.coe_algebraMap] using congrArg Subtype.val hab
    · obtain ⟨y, hy⟩ := hsurj x.2
      exact ⟨y, Subtype.ext (by simpa only [Subalgebra.coe_algebraMap] using hy)⟩

end S_AlgebraicCurve_TwoChartIntegralModel_bijective_algebraMap_globalSections_iff_isIntegrallyClosedIn
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_bijective_algebraMap_globalSections_iff_isIntegrallyClosedIn (solution)
