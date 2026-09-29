-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.TwoAffineOpenCover.flat_sections_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/e74b2f33-87c5-54dd-9a24-61373fec209b

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_flat_sections_of_flat

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of R)) [Flat c]
    (U : X.Opens) (hU : IsAffineOpen U) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    Module.Flat R Γ(X, U) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
  have h1 : (c.appLE ⊤ U le_top).hom.Flat :=
    HasRingHomProperty.appLE @Flat c inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  have hb : ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).Flat :=
    RingHom.Flat.of_bijective (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.bijective
  have h2 : ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ c.appLE ⊤ U le_top).hom.Flat := by
    rw [CommRingCat.hom_comp]
    exact RingHom.Flat.comp hb h1
  exact RingHom.flat_algebraMap_iff.mp h2

end S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_flat_sections_of_flat
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_flat_sections_of_flat (solution)
