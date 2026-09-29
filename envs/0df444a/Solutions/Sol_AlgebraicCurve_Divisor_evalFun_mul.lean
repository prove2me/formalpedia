-- Prove2me | solution 1 for AlgebraicCurve.Divisor.evalFun_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/e0624130-76dc-55c8-b2ea-9d2cde60744a

import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Divisor_evalFun_mul

open AlgebraicCurve

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] {f g : F} {D : Divisor K F} (hrat : ∀ v ∈ D.support, Place.IsRational v) (hf : ∀ v ∈ D.support, f ∈ v.toValuationSubring) (hg : ∀ v ∈ D.support, g ∈ v.toValuationSubring) : Divisor.evalFun (f * g) D = Divisor.evalFun f D * Divisor.evalFun g D := by
  rw [show Divisor.evalFun (f * g) D = D.prod fun v n => v.evalAt f ^ n * v.evalAt g ^ n from
    Finsupp.prod_congr fun v hv => by
      rw [AlgebraicCurve.Place.evalAt_mul v (hrat v hv) (hf v hv) (hg v hv), mul_zpow]]
  exact Finsupp.prod_mul

end S_AlgebraicCurve_Divisor_evalFun_mul
end P2MW
export P2MW.S_AlgebraicCurve_Divisor_evalFun_mul (solution)
