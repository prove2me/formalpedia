-- Prove2me | Definitions.Def_AlgebraicGeometry_Scheme_ProperAffineModels
-- name    : AlgebraicGeometry_Scheme_ProperAffineModels
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-22T02:30:44.229866+00:00
-- url     : https://prove2.me/theorems/82d9b972-7c25-49e5-9f98-b0ce399be301
-- title:
--   Proper approximation over Noetherian affine schemes
-- statement:
--   A proper approximation with affine Noetherian base stages and affine transitions.

import Mathlib.AlgebraicGeometry.Morphisms.Proper

noncomputable section

section

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite


namespace PhilipponProperAffineApproximation

universe u

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- An approximation of a proper morphism by proper morphisms over Noetherian
affine schemes, with affine transition maps. -/
structure AffineModels where
  index : Type u
  [category : Category.{u} index]
  [cofiltered : IsCofiltered index]
  rings : indexᵒᵖ ⥤ CommRingCat.{u}
  [noetherian : ∀ j, IsNoetherianRing (rings.obj j)]
  baseInclusion : rings ⟶ (Functor.const indexᵒᵖ).obj (CommRingCat.of R)
  baseColimit : IsColimit ⟨CommRingCat.of R, baseInclusion⟩
  ambient : index ⥤ Scheme.{u}
  [affine : ∀ {j k : index} (v : j ⟶ k), IsAffineHom (ambient.map v)]
  maps : ambient ⟶ rings.rightOp ⋙ Scheme.Spec
  [proper : ∀ j, IsProper (maps.app j)]
  projection : (Functor.const index).obj X ⟶ ambient
  ambientLimit : IsLimit ⟨X, projection⟩
  commutes : ∀ j, projection.app j ≫ maps.app j = f ≫ Spec.map (baseInclusion.app (op j))

end PhilipponProperAffineApproximation

end

end


