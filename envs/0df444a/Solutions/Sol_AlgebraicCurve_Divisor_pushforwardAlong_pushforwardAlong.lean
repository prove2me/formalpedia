-- Prove2me | solution 1 for AlgebraicCurve.Divisor.pushforwardAlong_pushforwardAlong
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/1c9fc3ae-866c-5271-b3b3-14d688758cdc

import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_AlgebraicCurve_Place_restrictAlong_restrictAlong
import Theorems.Thm_AlgebraicCurve_Place_inertiaDegAlong_comp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Divisor_pushforwardAlong_pushforwardAlong

set_option autoImplicit false

open IsDedekindDomain AlgebraicCurve

theorem solution {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F''] [Algebra K F] [Algebra K F'] [Algebra K F''] (φ : F →ₐ[K] F') (χ : F' →ₐ[K] F'') (hφ : φ.toRingHom.IsIntegral) (hχ : χ.toRingHom.IsIntegral) (hχφ : (χ.comp φ).toRingHom.IsIntegral) (D : Divisor K F'') : Divisor.pushforwardAlong φ hφ (Divisor.pushforwardAlong χ hχ D) = Divisor.pushforwardAlong (χ.comp φ) hχφ D := by
  have key : (Divisor.pushforwardAlong φ hφ).comp (Divisor.pushforwardAlong χ hχ)
      = Divisor.pushforwardAlong (χ.comp φ) hχφ := by
    refine Finsupp.addHom_ext fun W n => ?_
    show Divisor.pushforwardAlong φ hφ (Divisor.pushforwardAlong χ hχ (Finsupp.single W n))
        = Divisor.pushforwardAlong (χ.comp φ) hχφ (Finsupp.single W n)
    rw [Divisor.pushforwardAlong_single, Divisor.pushforwardAlong_single, Divisor.pushforwardAlong_single,
      AlgebraicCurve.Place.restrictAlong_restrictAlong φ χ hφ hχ hχφ,
      AlgebraicCurve.Place.inertiaDegAlong_comp φ χ hφ hχ hχφ W]
    refine congrArg (Finsupp.single _) ?_
    push_cast
    ring
  exact DFunLike.congr_fun key D

end S_AlgebraicCurve_Divisor_pushforwardAlong_pushforwardAlong
end P2MW
export P2MW.S_AlgebraicCurve_Divisor_pushforwardAlong_pushforwardAlong (solution)
