-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.eq_iff_comap_subschemeInclusion_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/2e8ba3de-b56a-56c0-b593-e3729d0785c4

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_eq_iff_comap_subschemeInclusion_eq_bot

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory

theorem solution
    {W : Scheme.{u}} (I₁ I₂ : W.IdealSheafData) :
    I₁ = I₂ ↔ I₂.comap I₁.subschemeι = ⊥ ∧ I₁.comap I₂.subschemeι = ⊥ := by
  have key : ∀ (I J : W.IdealSheafData), J.comap I.subschemeι = ⊥ ↔ J ≤ I := by
    intro I J
    rw [← le_bot_iff, ← Scheme.IdealSheafData.le_map_iff_comap_le, Scheme.IdealSheafData.map_bot,
      Scheme.IdealSheafData.ker_subschemeι]
  rw [key, key, le_antisymm_iff, and_comm]

end S_AlgebraicGeometry_Scheme_IdealSheafData_eq_iff_comap_subschemeInclusion_eq_bot
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_eq_iff_comap_subschemeInclusion_eq_bot (solution)
