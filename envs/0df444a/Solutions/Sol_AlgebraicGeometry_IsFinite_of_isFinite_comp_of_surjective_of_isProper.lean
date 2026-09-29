-- Prove2me | solution 1 for AlgebraicGeometry.IsFinite.of_isFinite_comp_of_surjective_of_isProper
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/bed3c1d1-4c82-58c2-97cd-f31396f1d207

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_IsFinite_of_isFinite_comp_of_surjective_of_isProper

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {X₀ X Y : Scheme.{u}} (i : X₀ ⟶ X) [Surjective i] (g : X ⟶ Y) [IsProper g] [IsFinite (i ≫ g)] :
    IsFinite g := by
  have hq : LocallyQuasiFinite g := by
    refine LocallyQuasiFinite.of_finite_preimage_singleton g fun y => ?_
    have hfin : ((i ≫ g) ⁻¹' {y}).Finite := (i ≫ g).finite_preimage_singleton y
    refine (hfin.image i).subset ?_
    intro x hx
    obtain ⟨x₀, rfl⟩ := ‹Surjective i›.surj x
    exact ⟨x₀, by simpa [Scheme.Hom.comp_base] using hx, rfl⟩
  exact IsFinite.of_isProper_of_locallyQuasiFinite g

end S_AlgebraicGeometry_IsFinite_of_isFinite_comp_of_surjective_of_isProper
end P2MW
export P2MW.S_AlgebraicGeometry_IsFinite_of_isFinite_comp_of_surjective_of_isProper (solution)
