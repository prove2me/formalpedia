-- Prove2me | solution 1 for AlgebraicCurve.SemilinearAut.pushforward_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/6854f39e-ee6c-5ed7-8696-5854c87318a5

import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_AlgebraicCurve_SemilinearAut_restrict_smul
import Theorems.Thm_AlgebraicCurve_SemilinearAut_inertiaDeg_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_SemilinearAut_pushforward_smul

open AlgebraicCurve AlgebraicCurve.SemilinearAut
open scoped Pointwise

noncomputable section

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] {g : SemilinearAut K F} {g' : SemilinearAut K F'} (hgg' : IntertwinesAlong (algebraMap F F') g g') (D : Divisor K F') : Divisor.pushforward F (g' • D) = g • Divisor.pushforward F D := by
  induction D using Finsupp.induction with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | single_add w n D _ _ ih =>
    rw [smul_add, map_add, map_add, smul_add, ih]
    congr 1
    rw [smul_single, Divisor.pushforward_single, Divisor.pushforward_single, smul_single,
      restrict_smul hgg' w, inertiaDeg_smul hgg' w]

end

end S_AlgebraicCurve_SemilinearAut_pushforward_smul
end P2MW
export P2MW.S_AlgebraicCurve_SemilinearAut_pushforward_smul (solution)
