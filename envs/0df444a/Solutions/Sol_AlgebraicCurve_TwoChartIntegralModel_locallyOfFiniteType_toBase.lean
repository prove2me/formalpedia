-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.locallyOfFiniteType_toBase
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/583ccaf7-9b92-55ea-b6d5-e492a9e6d608

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_locallyOfFiniteType_toBase

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

open AlgebraicCurve.TwoChartIntegralModel in

theorem solution
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    [Algebra.FiniteType R (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin R F j)]
    [Algebra.FiniteType R (AlgebraicCurve.TwoChartIntegralModel.chartAlgInf R F j)] :
    LocallyOfFiniteType (AlgebraicCurve.TwoChartIntegralModel.toBase R F j) := by

  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @LocallyOfFiniteType)
    (fun b : Bool => cond b (chartFinOpen R F j) (chartInfOpen R F j)) ?_ ?_
  · rw [iSup_bool_eq]; exact twoChartCover R F j
  rintro (_ | _)
  ·
    show LocallyOfFiniteType ((chartInfOpen R F j).ι ≫ toBase R F j)
    rw [chartInfOpen,
      ← MorphismProperty.cancel_left_of_respectsIso (P := @LocallyOfFiniteType) (ιInf R F j).isoOpensRange.hom,
      Scheme.Hom.isoOpensRange_hom_ι_assoc, ιInf_toBase]
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), CommRingCat.hom_ofHom,
      RingHom.finiteType_algebraMap]
    infer_instance
  ·
    show LocallyOfFiniteType ((chartFinOpen R F j).ι ≫ toBase R F j)
    rw [chartFinOpen,
      ← MorphismProperty.cancel_left_of_respectsIso (P := @LocallyOfFiniteType) (ιFin R F j).isoOpensRange.hom,
      Scheme.Hom.isoOpensRange_hom_ι_assoc, ιFin_toBase]
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), CommRingCat.hom_ofHom,
      RingHom.finiteType_algebraMap]
    infer_instance

end S_AlgebraicCurve_TwoChartIntegralModel_locallyOfFiniteType_toBase
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_locallyOfFiniteType_toBase (solution)
