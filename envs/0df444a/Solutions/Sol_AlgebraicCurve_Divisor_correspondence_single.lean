-- Prove2me | solution 1 for AlgebraicCurve.Divisor.correspondence_single
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/def2c27a-456f-5512-860a-7121146b831a

import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Divisor_correspondence_single

open AlgebraicCurve AlgebraicCurve.SemilinearAut
open scoped Pointwise

noncomputable section

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [HasPrincipalDivisors K F'] (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral) (v : Place K F) (n : ℤ) : Divisor.correspondence φ ψ hφ hψ (Finsupp.single v n) = ∑ w ∈ Place.fiberAlong φ hφ v, Finsupp.single (w.restrictAlong ψ hψ) (n * (w.ramificationIndexAlong φ : ℤ) * (w.inertiaDegAlong ψ hψ : ℤ)) := by
  rw [Divisor.correspondence_apply, Divisor.pullbackAlong_single, map_sum]
  exact Finset.sum_congr rfl fun w _ => Divisor.pushforwardAlong_single ψ hψ w _

end

end S_AlgebraicCurve_Divisor_correspondence_single
end P2MW
export P2MW.S_AlgebraicCurve_Divisor_correspondence_single (solution)
