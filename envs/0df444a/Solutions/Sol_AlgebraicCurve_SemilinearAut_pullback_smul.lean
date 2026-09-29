-- Prove2me | solution 1 for AlgebraicCurve.SemilinearAut.pullback_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/3174644a-c30b-5b0d-9be9-bc291f376664

import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_AlgebraicCurve_SemilinearAut_restrict_smul
import Theorems.Thm_AlgebraicCurve_SemilinearAut_ramificationIndex_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_SemilinearAut_pullback_smul

open AlgebraicCurve AlgebraicCurve.SemilinearAut
open scoped Pointwise

noncomputable section

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] {g : SemilinearAut K F} {g' : SemilinearAut K F'} [HasPrincipalDivisors K F'] (hgg' : IntertwinesAlong (algebraMap F F') g g') (D : Divisor K F) : Divisor.pullback F' (g • D) = g' • Divisor.pullback F' D := by
  ext w
  rw [Divisor.pullback_apply, divisor_smul_apply, divisor_smul_apply, Divisor.pullback_apply,
    restrict_smul hgg'.inv w, ramificationIndex_smul hgg'.inv w]

end

end S_AlgebraicCurve_SemilinearAut_pullback_smul
end P2MW
export P2MW.S_AlgebraicCurve_SemilinearAut_pullback_smul (solution)
