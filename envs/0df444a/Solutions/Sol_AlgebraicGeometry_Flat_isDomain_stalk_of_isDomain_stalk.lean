-- Prove2me | solution 1 for AlgebraicGeometry.Flat.isDomain_stalk_of_isDomain_stalk
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/644c931a-d425-5ca1-a793-ed57f9323aad

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Flat_isDomain_stalk_of_isDomain_stalk

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {Y Z : Scheme.{u}} (h : Y ⟶ Z) [Flat h] (y : Y) [IsDomain (Y.presheaf.stalk y)] :
    IsDomain (Z.presheaf.stalk (h y)) := by
  have hflat : (h.stalkMap y).hom.Flat := Flat.stalkMap h y
  letI := (h.stalkMap y).hom.toAlgebra
  haveI : Module.Flat (Z.presheaf.stalk (h y)) (Y.presheaf.stalk y) := hflat
  haveI : IsLocalHom (algebraMap (Z.presheaf.stalk (h y)) (Y.presheaf.stalk y)) := by
    rw [RingHom.algebraMap_toAlgebra]; infer_instance
  haveI : Module.FaithfullyFlat (Z.presheaf.stalk (h y)) (Y.presheaf.stalk y) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hinj : Function.Injective (algebraMap (Z.presheaf.stalk (h y)) (Y.presheaf.stalk y)) :=
    (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance).injective
  exact hinj.isDomain _

#print axioms solution

end S_AlgebraicGeometry_Flat_isDomain_stalk_of_isDomain_stalk
end P2MW
export P2MW.S_AlgebraicGeometry_Flat_isDomain_stalk_of_isDomain_stalk (solution)
