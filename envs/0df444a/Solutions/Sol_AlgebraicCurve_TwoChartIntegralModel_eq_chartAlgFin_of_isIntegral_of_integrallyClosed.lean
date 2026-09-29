-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.eq_chartAlgFin_of_isIntegral_of_integrallyClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/c8aa2810-778b-5d47-9fe3-13897e59cab2

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_eq_chartAlgFin_of_isIntegral_of_integrallyClosed

set_option autoImplicit false

open AlgebraicCurve.TwoChartIntegralModel

theorem solution
    (R : Type) [CommRing R] (F : Type) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (B : Subalgebra R F) (hj : j ∈ B)
    (hint : ∀ x ∈ B, IsIntegral (Algebra.adjoin R ({j} : Set F)) x)
    (hic : ∀ x : F, IsIntegral B x → x ∈ B) :
    B = chartAlgFin R F j := by
  apply le_antisymm
  · intro x hx
    exact (mem_chartAlg_iff R F).mpr (hint x hx)
  · intro x hx
    have hx' : IsIntegral (Algebra.adjoin R ({j} : Set F)) x := (mem_chartAlg_iff R F).mp hx
    have hle : Algebra.adjoin R ({j} : Set F) ≤ B := Algebra.adjoin_le (Set.singleton_subset_iff.mpr hj)
    exact hic x (hx'.map_of_comp_eq (Subalgebra.inclusion hle).toRingHom (RingHom.id F) (by ext; rfl))

end S_AlgebraicCurve_TwoChartIntegralModel_eq_chartAlgFin_of_isIntegral_of_integrallyClosed
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_eq_chartAlgFin_of_isIntegral_of_integrallyClosed (solution)
