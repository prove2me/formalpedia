-- Prove2me | solution 1 for AlgebraicCurve.Pic0.addOrderOf_mk_dvd_of_isPrincipal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/42bfde03-b481-59de-a51b-039b903ab0d1

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_AlgebraicCurve_Pic0_nsmul_mk_eq_zero_of_isPrincipal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Pic0_addOrderOf_mk_dvd_of_isPrincipal

set_option autoImplicit false

open AlgebraicCurve

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (D : Divisor.degZero (K := K) (F := F)) (m : ℕ) (hD : Divisor.IsPrincipal (m • (D : Divisor K F))) : addOrderOf (Pic0.mk D) ∣ m :=
  addOrderOf_dvd_of_nsmul_eq_zero (AlgebraicCurve.Pic0.nsmul_mk_eq_zero_of_isPrincipal D m hD)

end S_AlgebraicCurve_Pic0_addOrderOf_mk_dvd_of_isPrincipal
end P2MW
export P2MW.S_AlgebraicCurve_Pic0_addOrderOf_mk_dvd_of_isPrincipal (solution)
