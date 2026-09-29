-- Prove2me | solution 1 for AlgebraicCurve.degree_canonicalDivisor_eq_of_riemannRoch
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/a9a86fc1-c645-5192-a794-16c9c83e2717

import Mathlib
import Definitions.Def_AlgebraicCurve_RiemannRochRows
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_degree_canonicalDivisor_eq_of_riemannRoch

open AlgebraicCurve KaehlerDifferential

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates] (hRR : FunctionFieldRiemannRoch K F) (hC : ConstantsAreBase K F) {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    Divisor.degree (canonicalDivisorOf hω) = 2 * (genus K F : ℤ) - 2 := by
  have h0 := hRR hω 0
  rw [map_zero, ell_zero_eq_one_of_constantsAreBase hC, sub_zero] at h0
  push_cast at h0
  have hW := hRR hω (canonicalDivisorOf hω)
  rw [sub_self, ell_zero_eq_one_of_constantsAreBase hC] at hW
  push_cast at hW
  linarith

end S_AlgebraicCurve_degree_canonicalDivisor_eq_of_riemannRoch
end P2MW
export P2MW.S_AlgebraicCurve_degree_canonicalDivisor_eq_of_riemannRoch (solution)
