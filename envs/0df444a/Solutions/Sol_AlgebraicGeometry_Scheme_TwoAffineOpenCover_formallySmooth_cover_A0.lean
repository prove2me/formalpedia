-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.TwoAffineOpenCover.formallySmooth_cover_A0
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/978e132b-1f80-54e5-a5cd-c7d23a0a88a9

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_formallySmooth_cover_A0

universe u

open CategoryTheory

theorem solution {R : Type u} [CommRing R] {X : AlgebraicGeometry.Scheme.{u}} (𝒱 : X.TwoAffineOpenCover)
    (c : X ⟶ AlgebraicGeometry.Spec (.of R)) [AlgebraicGeometry.Smooth c] :
    Algebra.FormallySmooth R (𝒱.cover c).A0 := by
  have h1 : (c.appLE ⊤ 𝒱.U0 le_top).hom.FormallySmooth :=
    (AlgebraicGeometry.Smooth.smooth_appLE (f := c)
      (AlgebraicGeometry.isAffineOpen_top (AlgebraicGeometry.Spec (.of R))) 𝒱.isAffineOpen_U0 le_top).formallySmooth
  have h2 : ((AlgebraicGeometry.Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ 𝒱.U0 le_top).hom.FormallySmooth := by
    rw [CommRingCat.hom_comp]
    exact (RingHom.FormallySmooth.respectsIso.cancel_left_isIso _ _).mpr h1
  exact h2.toAlgebra

end S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_formallySmooth_cover_A0
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_formallySmooth_cover_A0 (solution)
