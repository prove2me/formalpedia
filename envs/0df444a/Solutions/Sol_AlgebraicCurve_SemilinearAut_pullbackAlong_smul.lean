-- Prove2me | solution 1 for AlgebraicCurve.SemilinearAut.pullbackAlong_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/c62d302e-9e22-5600-af70-8b47699bf4c0

import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_AlgebraicCurve_SemilinearAut_pullback_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_SemilinearAut_pullbackAlong_smul

open AlgebraicCurve AlgebraicCurve.SemilinearAut
open scoped Pointwise

noncomputable section

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] {g : SemilinearAut K F} {g' : SemilinearAut K F'} [HasPrincipalDivisors K F'] (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hgg' : IntertwinesAlong φ.toRingHom g g') (D : Divisor K F) : Divisor.pullbackAlong φ hφ (g • D) = g' • Divisor.pullbackAlong φ hφ D := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact pullback_smul hgg' D

end

end S_AlgebraicCurve_SemilinearAut_pullbackAlong_smul
end P2MW
export P2MW.S_AlgebraicCurve_SemilinearAut_pullbackAlong_smul (solution)
