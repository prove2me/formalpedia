-- Prove2me | solution 1 for AlgebraicCurve.exists_divisor_eq_max_ord_sub_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/4f54069c-e429-5fd5-8e91-e98ad1b66a55

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_divisor_eq_max_ord_sub_algebraMap

set_option autoImplicit false

open AlgebraicCurve

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F]
    (x : F) (hx : Transcendental K x) (a : K) :
    ∃ D : Divisor K F, ∀ v : Place K F, D v = max 0 (v.ord (x - algebraMap K F a)) := by
  classical
  have hxa : x - algebraMap K F a ≠ 0 := by
    intro h
    apply hx
    rw [sub_eq_zero] at h
    rw [h]
    exact isAlgebraic_algebraMap a
  obtain ⟨P, hP, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) (x - algebraMap K F a) hxa
  exact ⟨P.mapRange (fun n => max 0 n) (by simp), fun v => by rw [Finsupp.mapRange_apply, hP v]⟩

end S_AlgebraicCurve_exists_divisor_eq_max_ord_sub_algebraMap
end P2MW
export P2MW.S_AlgebraicCurve_exists_divisor_eq_max_ord_sub_algebraMap (solution)
