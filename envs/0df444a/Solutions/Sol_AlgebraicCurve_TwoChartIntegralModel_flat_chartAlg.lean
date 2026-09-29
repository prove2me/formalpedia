-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.flat_chartAlg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/355c2275-c49d-5adf-b663-a75f02819756

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_flat_chartAlg

set_option autoImplicit false

universe u

theorem solution
    {R F : Type u} [CommRing R] [IsDomain R] [IsBezout R] [Field F] [Algebra R F]
    (hRF : Function.Injective (algebraMap R F)) (S : Set F) :
    Module.Flat R ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlg R F S) := by
  have hinj : Function.Injective (algebraMap R ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlg R F S)) :=
    fun a b hab => hRF (congrArg Subtype.val hab)
  haveI : Module.IsTorsionFree R ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlg R F S) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, ← Submodule.isTorsionFree_iff_torsion_eq_bot]
  infer_instance

#print axioms solution

end S_AlgebraicCurve_TwoChartIntegralModel_flat_chartAlg
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_flat_chartAlg (solution)
