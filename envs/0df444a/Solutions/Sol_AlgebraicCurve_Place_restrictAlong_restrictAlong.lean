-- Prove2me | solution 1 for AlgebraicCurve.Place.restrictAlong_restrictAlong
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/c443aab3-d51e-55e0-86b1-2b43a8991374

import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_restrictAlong_restrictAlong

set_option autoImplicit false

open IsDedekindDomain AlgebraicCurve

theorem solution {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F''] [Algebra K F] [Algebra K F'] [Algebra K F''] (φ : F →ₐ[K] F') (χ : F' →ₐ[K] F'') (hφ : φ.toRingHom.IsIntegral) (hχ : χ.toRingHom.IsIntegral) (hχφ : (χ.comp φ).toRingHom.IsIntegral) (W : Place K F'') : (W.restrictAlong χ hχ).restrictAlong φ hφ = W.restrictAlong (χ.comp φ) hχφ :=
  Place.ext (SetLike.ext fun _ => Iff.rfl)

end S_AlgebraicCurve_Place_restrictAlong_restrictAlong
end P2MW
export P2MW.S_AlgebraicCurve_Place_restrictAlong_restrictAlong (solution)
