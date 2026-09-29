-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.RigidifiedLineBundle.subsingleton_iso_map_pullback_rigSection_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/a5cee2dd-9e89-5e95-a692-776c231d896f

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_iso_eq_of_map_pullback_rigSection_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_subsingleton_iso_map_pullback_rigSection_comp_eq

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M M' : RigidifiedLineBundle c ε t)
    (α : (Scheme.Modules.pullback (rigSection c t ε)).obj M.L ≅ SheafOfModules.unit T.ringCatSheaf)
    (α' : (Scheme.Modules.pullback (rigSection c t ε)).obj M'.L ≅ SheafOfModules.unit T.ringCatSheaf) :
    Subsingleton {φ : M.L ≅ M'.L // (Scheme.Modules.pullback (rigSection c t ε)).mapIso φ ≪≫ α' = α} :=
  ⟨fun a b => Subtype.ext (AlgebraicGeometry.RelPicard.RigidifiedLineBundle.iso_eq_of_map_pullback_rigSection_comp_eq R c ε hH0 t M M' α α' a.1 b.1 a.2 b.2)⟩

end S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_subsingleton_iso_map_pullback_rigSection_comp_eq
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_subsingleton_iso_map_pullback_rigSection_comp_eq (solution)
