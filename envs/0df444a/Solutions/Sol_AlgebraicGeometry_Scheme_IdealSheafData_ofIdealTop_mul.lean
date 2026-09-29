-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/751afd14-b584-5c64-83e1-5006dfcaa756

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_ofIdealTop_mul
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry

open TopologicalSpace Opposite
universe u

theorem solution {X : Scheme.{u}} (I J : Ideal Γ(X, ⊤)) :
    Scheme.IdealSheafData.ofIdealTop (I * J) = Scheme.IdealSheafData.ofIdealTop I * Scheme.IdealSheafData.ofIdealTop J := by
  apply Scheme.IdealSheafData.ext
  funext U
  simp only [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_mul]

end S_AlgebraicGeometry_Scheme_IdealSheafData_ofIdealTop_mul
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_ofIdealTop_mul (solution)
