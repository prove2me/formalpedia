-- Prove2me | solution 1 for AlgebraicCurve.Pic0.zsmul_mk_eq_zero_of_isPrincipal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/eabc13e2-9b74-5665-97ad-9dcbaa8230da

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_AlgebraicCurve_Pic0_mk_eq_zero_iff
import Theorems.Thm_AlgebraicCurve_Pic0_zsmul_mk
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Pic0_zsmul_mk_eq_zero_of_isPrincipal

set_option autoImplicit false

open AlgebraicCurve

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (D : Divisor.degZero (K := K) (F := F)) (m : ℤ) (hD : Divisor.IsPrincipal (m • (D : Divisor K F))) : m • Pic0.mk D = 0 := by
  rw [AlgebraicCurve.Pic0.zsmul_mk, AlgebraicCurve.Pic0.mk_eq_zero_iff]
  exact hD

end S_AlgebraicCurve_Pic0_zsmul_mk_eq_zero_of_isPrincipal
end P2MW
export P2MW.S_AlgebraicCurve_Pic0_zsmul_mk_eq_zero_of_isPrincipal (solution)
