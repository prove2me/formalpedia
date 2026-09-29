-- Prove2me | solution 1 for AlgebraicGeometry.isIntegral_and_isIntegral_pullback_of_isIntegral_pullback_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/0fed0021-95f8-5896-985b-2d83b78ab580

import Mathlib
import Theorems.Thm_AlgebraicGeometry_GeometricallyIrreducible_of_irreducibleSpace_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_GeometricallyReduced_of_isReduced_of_perfectField
import Theorems.Thm_AlgebraicGeometry_GeometricallyIntegral_of_isPullback_of_geometricallyIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isIntegral_and_isIntegral_pullback_of_isIntegral_pullback_of_isAlgClosed

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits

theorem solution
    (K : Type) [Field K] (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType πX]
    (L : Type) [Field L] [IsAlgClosed L] [Algebra K L]
    (hL : IsIntegral (CategoryTheory.Limits.pullback πX (Spec.map (CommRingCat.ofHom (algebraMap K L))))) :
    IsIntegral X ∧
      ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra K k],
        IsIntegral (CategoryTheory.Limits.pullback πX (Spec.map (CommRingCat.ofHom (algebraMap K k)))) := by
  let ιL := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let fL : pullback πX ιL ⟶ Spec (CommRingCat.of L) := pullback.snd πX ιL
  haveI : IsIntegral (pullback πX ιL) := hL
  haveI : LocallyOfFiniteType fL := inferInstance
  haveI : GeometricallyIrreducible fL :=
    AlgebraicGeometry.GeometricallyIrreducible.of_irreducibleSpace_of_isAlgClosed fL
  haveI : GeometricallyReduced fL :=
    AlgebraicGeometry.GeometricallyReduced.of_isReduced_of_perfectField fL
  haveI : GeometricallyIntegral fL :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible fL
  haveI hGI : GeometricallyIntegral πX :=
    AlgebraicGeometry.GeometricallyIntegral.of_isPullback_of_geometricallyIntegral πX fL (pullback.fst πX ιL)
      (IsPullback.of_hasPullback πX ιL)
  refine ⟨GeometricallyIntegral.isIntegral_of_subsingleton πX, fun k _ _ _ => ?_⟩
  exact pullback_of_geometrically (GeometricallyIntegral.eq_geometrically ▸ hGI) k
    (Spec.map (CommRingCat.ofHom (algebraMap K k)))

end S_AlgebraicGeometry_isIntegral_and_isIntegral_pullback_of_isIntegral_pullback_of_isAlgClosed
end P2MW
export P2MW.S_AlgebraicGeometry_isIntegral_and_isIntegral_pullback_of_isIntegral_pullback_of_isAlgClosed (solution)
