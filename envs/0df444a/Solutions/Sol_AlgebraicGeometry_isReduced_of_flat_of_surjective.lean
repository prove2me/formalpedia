-- Prove2me | solution 1 for AlgebraicGeometry.isReduced_of_flat_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/252f9677-297e-5930-b365-c766f63503c6

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isReduced_of_flat_of_surjective

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f] [IsReduced X] : IsReduced Y := by
  haveI : ∀ y : Y, _root_.IsReduced (Y.presheaf.stalk y) := by
    intro y
    obtain ⟨x, rfl⟩ := f.surjective y
    let φ := (f.stalkMap x).hom
    letI := φ.toAlgebra
    haveI : Module.Flat (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) := Flat.stalkMap f x
    haveI : IsLocalHom (algebraMap (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom φ)
    haveI : Module.FaithfullyFlat (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact isReduced_of_injective (algebraMap (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x))
      (FaithfulSMul.algebraMap_injective _ _)
  exact isReduced_of_isReduced_stalk Y

end S_AlgebraicGeometry_isReduced_of_flat_of_surjective
end P2MW
export P2MW.S_AlgebraicGeometry_isReduced_of_flat_of_surjective (solution)
