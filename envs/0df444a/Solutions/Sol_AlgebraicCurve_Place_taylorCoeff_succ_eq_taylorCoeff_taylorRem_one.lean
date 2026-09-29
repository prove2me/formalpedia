-- Prove2me | solution 1 for AlgebraicCurve.Place.taylorCoeff_succ_eq_taylorCoeff_taylorRem_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/409caa8f-e560-5804-829b-7e669eb172a5

import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff
import Theorems.Thm_AlgebraicCurve_Place_taylorRem_succ_eq_taylorRem_taylorRem_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_taylorCoeff_succ_eq_taylorCoeff_taylorRem_one

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.Place

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (t f : F) (r : ℕ) :
    taylorCoeff v t (r + 1) f = taylorCoeff v t r (taylorRem v t f 1) := by
  rw [taylorCoeff_eq, taylorCoeff_eq, taylorRem_succ_eq_taylorRem_taylorRem_one]

end S_AlgebraicCurve_Place_taylorCoeff_succ_eq_taylorCoeff_taylorRem_one
end P2MW
export P2MW.S_AlgebraicCurve_Place_taylorCoeff_succ_eq_taylorCoeff_taylorRem_one (solution)
