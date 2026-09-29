-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.hom_ext_of_iotaFin_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/698ba202-74ee-52fc-8740-116053297068

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_hom_ext_of_iotaFin_comp_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

namespace PinsBody

theorem isDominant_ιFin (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)] :
    IsDominant (ιFin R F j) := by
  haveI := TwoChartIntegralModel.isIntegral R F j
  exact ⟨(ιFin R F j).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩

theorem hom_ext (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    {Y Z : Scheme.{u}} (f g : AlgebraicCurve.TwoChartIntegralModel R F j ⟶ Y) (q : Y ⟶ Z) [IsSeparated q]
    (h : f ≫ q = g ≫ q) (hFin : ιFin R F j ≫ f = ιFin R F j ≫ g) : f = g := by
  haveI := TwoChartIntegralModel.isIntegral R F j
  haveI := isDominant_ιFin R F j
  exact ext_of_isDominant_of_isSeparated q h (ιFin R F j) hFin

end PinsBody

theorem solution
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    {Y Z : Scheme.{u}} (f g : AlgebraicCurve.TwoChartIntegralModel R F j ⟶ Y) (q : Y ⟶ Z) [IsSeparated q]
    (h : f ≫ q = g ≫ q) (hFin : ιFin R F j ≫ f = ιFin R F j ≫ g) : f = g :=
  PinsBody.hom_ext R F j f g q h hFin

#print axioms solution

end S_AlgebraicCurve_TwoChartIntegralModel_hom_ext_of_iotaFin_comp_eq
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_hom_ext_of_iotaFin_comp_eq (solution)
