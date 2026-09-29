-- Prove2me | solution 1 for AlgebraicCurve.separableAlong_of_charZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/44cc6042-f4f3-51fa-9c42-cd3e2784896b

import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_separableAlong_of_charZero

set_option autoImplicit false

open AlgebraicCurve

theorem solution {K F F₁ : Type*} [Field K] [Field F] [Field F₁] [Algebra K F] [Algebra K F₁] [CharZero F] (φ : F →ₐ[K] F₁) (hφ : φ.toRingHom.IsIntegral) : SeparableAlong K φ := by
  letI := algebraAlong φ
  haveI := isIntegral_along φ hφ
  exact Algebra.IsSeparable.of_integral F F₁

end S_AlgebraicCurve_separableAlong_of_charZero
end P2MW
export P2MW.S_AlgebraicCurve_separableAlong_of_charZero (solution)
