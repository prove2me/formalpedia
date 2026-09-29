-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/7b0e62d8-6715-58b1-b224-d93fef76cdfb

import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution {X : Scheme.{u}} {I : X.IdealSheafData} (hI : I.IsInvertible) (n : ℕ) :
    (I ^ n).IsInvertible := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact Scheme.IdealSheafData.isInvertible_top
  | succ n ih =>
    rw [pow_succ]
    exact ih.mul hI

end S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow (solution)
