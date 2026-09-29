-- Prove2me | solution 1 for AlgebraicCurve.mem_range_algebraMap_of_isAlgebraic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/d8eff4fb-1acd-5ff2-873d-3f0b1ff6bf79

import Mathlib.FieldTheory.IsAlgClosed.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_mem_range_algebraMap_of_isAlgebraic
set_option Elab.async false

theorem solution {K L : Type*} [Field K] [Field L] [Algebra K L] [IsAlgClosed K] {x : L} (hx : IsAlgebraic K x) :
    x ∈ (algebraMap K L).range :=
  minpoly.degree_eq_one_iff.mp
    (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hx.isIntegral))

#print axioms solution

end S_AlgebraicCurve_mem_range_algebraMap_of_isAlgebraic
end P2MW
export P2MW.S_AlgebraicCurve_mem_range_algebraMap_of_isAlgebraic (solution)
