-- Prove2me | solution 1 for AlgebraicCurve.Place.inertiaDegAlong_eq_one_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/e2ffd65e-fa16-5a4a-99b1-7faf5c34468b

import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_inertiaDegAlong_eq_one_of_isAlgClosed

set_option autoImplicit false

open AlgebraicCurve

theorem solution
    {K F F' : Type*} [Field K] [IsAlgClosed K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [IsCurveOver K F] [Algebra.EssFiniteType K F] [IsCurveOver K F'] [Algebra.EssFiniteType K F']
    (ψ : F →ₐ[K] F') (hψ : ψ.toRingHom.IsIntegral) (W : Place K F') :
    W.inertiaDegAlong ψ hψ = 1 := by
  letI := algebraAlong ψ
  haveI := isScalarTower_along ψ
  haveI := isIntegral_along ψ hψ
  have h := W.deg_restrict_mul_inertiaDeg (F := F)
  rw [IsCurveOver.deg_eq_one_of_isAlgClosed, IsCurveOver.deg_eq_one_of_isAlgClosed, one_mul] at h
  exact h

end S_AlgebraicCurve_Place_inertiaDegAlong_eq_one_of_isAlgClosed
end P2MW
export P2MW.S_AlgebraicCurve_Place_inertiaDegAlong_eq_one_of_isAlgClosed (solution)
