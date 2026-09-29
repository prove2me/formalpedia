-- Prove2me | solution 1 for AlgebraicCurve.Divisor.pushforwardAlong_single_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/81202a25-de1d-598f-ac5d-d58d2042d52d

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Divisor_pushforwardAlong_single_one

set_option autoImplicit false

open AlgebraicCurve in
theorem solution
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (ψ : F →ₐ[K] F') (hψ : ψ.toRingHom.IsIntegral) (W : AlgebraicCurve.Place K F')
    (hW : W.deg = 1) (hV : (W.restrictAlong ψ hψ).deg = 1) :
    AlgebraicCurve.Divisor.pushforwardAlong ψ hψ (Finsupp.single W 1) =
      Finsupp.single (W.restrictAlong ψ hψ) 1 := by
  have h1 : W.inertiaDegAlong ψ hψ = 1 := by
    letI := algebraAlong ψ
    haveI := isScalarTower_along ψ
    haveI := isIntegral_along ψ hψ
    have ht : (W.restrictAlong ψ hψ).deg * W.inertiaDegAlong ψ hψ = W.deg :=
      W.deg_restrict_mul_inertiaDeg (F := F)
    rw [hV, hW, one_mul] at ht
    exact ht
  rw [Divisor.pushforwardAlong_single, h1, Nat.cast_one, mul_one]

end S_AlgebraicCurve_Divisor_pushforwardAlong_single_one
end P2MW
export P2MW.S_AlgebraicCurve_Divisor_pushforwardAlong_single_one (solution)
