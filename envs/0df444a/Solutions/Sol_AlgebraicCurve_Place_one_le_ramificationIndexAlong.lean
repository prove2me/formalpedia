-- Prove2me | solution 1 for AlgebraicCurve.Place.one_le_ramificationIndexAlong
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/2767d882-edf7-5c9f-84d1-275b84dbe89e

import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_one_le_ramificationIndexAlong
set_option autoImplicit false

namespace AlgebraicCurve p2m_export "AlgebraicCurve" "algebraAlong isIntegral_along Place.ramificationIndexAlong Place" namespace Place p2m_export "AlgebraicCurve.Place" "ramificationIndexAlong ramificationIndex_pos" end AlgebraicCurve.Place
p2m_open_scoped "AlgebraicCurve AlgebraicCurve.Place" in
private theorem AlgebraicCurve.Place.solution_impl
    {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : AlgebraicCurve.Place K F') :
    1 ≤ AlgebraicCurve.Place.ramificationIndexAlong φ w := by
  letI := AlgebraicCurve.algebraAlong φ
  haveI := AlgebraicCurve.isIntegral_along φ hφ
  exact w.ramificationIndex_pos (F := F)

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : AlgebraicCurve.Place K F') :
    1 ≤ AlgebraicCurve.Place.ramificationIndexAlong φ w :=
  AlgebraicCurve.Place.solution_impl φ hφ w

end S_AlgebraicCurve_Place_one_le_ramificationIndexAlong
end P2MW
export P2MW.S_AlgebraicCurve_Place_one_le_ramificationIndexAlong (solution)
