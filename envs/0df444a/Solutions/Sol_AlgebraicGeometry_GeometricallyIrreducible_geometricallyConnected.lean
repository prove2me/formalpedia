-- Prove2me | solution 1 for AlgebraicGeometry.GeometricallyIrreducible.geometricallyConnected
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/e05ccb8e-5e46-5a9b-921d-484c442b61d8

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_GeometricallyIrreducible_geometricallyConnected

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution {X Y : Scheme.{u}} (f : X ⟶ Y)
    [GeometricallyIrreducible f] : GeometricallyConnected f := by
  refine ⟨?_⟩
  have h := GeometricallyIrreducible.geometrically_irreducibleSpace (f := f)
  rw [geometrically_eq_universally] at h ⊢
  refine MorphismProperty.universally_mono ?_ _ h
  intro X' Y' g hg hI hS
  haveI : IrreducibleSpace X' := hg hI hS
  infer_instance

example {X Y : Scheme.{u}} (f : X ⟶ Y) [GeometricallyIntegral f] : GeometricallyConnected f :=
  solution f

end S_AlgebraicGeometry_GeometricallyIrreducible_geometricallyConnected
end P2MW
export P2MW.S_AlgebraicGeometry_GeometricallyIrreducible_geometricallyConnected (solution)
