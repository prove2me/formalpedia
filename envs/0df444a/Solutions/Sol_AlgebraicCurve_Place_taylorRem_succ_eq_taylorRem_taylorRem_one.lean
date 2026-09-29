-- Prove2me | solution 1 for AlgebraicCurve.Place.taylorRem_succ_eq_taylorRem_taylorRem_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/33ef3edf-0b6c-5ce7-8df8-c0f71d6ed71c

import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_taylorRem_succ_eq_taylorRem_taylorRem_one

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.Place

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (t f : F) (r : ℕ) :
    taylorRem v t f (r + 1) = taylorRem v t (taylorRem v t f 1) r := by
  induction r with
  | zero => rfl
  | succ r ih => rw [taylorRem_succ, ih, ← taylorRem_succ]

end S_AlgebraicCurve_Place_taylorRem_succ_eq_taylorRem_taylorRem_one
end P2MW
export P2MW.S_AlgebraicCurve_Place_taylorRem_succ_eq_taylorRem_taylorRem_one (solution)
