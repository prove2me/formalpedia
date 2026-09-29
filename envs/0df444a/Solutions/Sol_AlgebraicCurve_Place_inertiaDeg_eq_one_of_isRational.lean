-- Prove2me | solution 1 for AlgebraicCurve.Place.inertiaDeg_eq_one_of_isRational
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/b31dc104-e957-52ca-bf2e-c416f4ada3ae

import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_inertiaDeg_eq_one_of_isRational

open AlgebraicCurve

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (w : Place K F') (hw : w.IsRational) (hv : (w.restrict F).IsRational) : w.inertiaDeg F = 1 := by
  have h := w.deg_restrict_mul_inertiaDeg (F := F)
  rw [(AlgebraicCurve.Place.isRational_iff_deg_eq_one _).1 hv,
    (AlgebraicCurve.Place.isRational_iff_deg_eq_one _).1 hw, one_mul] at h
  exact h

end S_AlgebraicCurve_Place_inertiaDeg_eq_one_of_isRational
end P2MW
export P2MW.S_AlgebraicCurve_Place_inertiaDeg_eq_one_of_isRational (solution)
