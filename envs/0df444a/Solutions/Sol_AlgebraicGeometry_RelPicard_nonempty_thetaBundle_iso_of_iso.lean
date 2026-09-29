-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.nonempty_thetaBundle_iso_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/4fd31881-e9d2-5b58-9ec9-715ff4b36c5e

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_nonempty_thetaBundle_iso_of_iso

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra"

theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M M' : RigidifiedLineBundle c ε t) (e : M.L ≅ M'.L) (r n : ℕ) :
    Nonempty (thetaBundle c ε t M r n ≅ thetaBundle c ε t M' r n) := by

  let i1 : M.L ⊗ sectionTwist c ε t r ≅ M'.L ⊗ sectionTwist c ε t r := whiskerRightIso e _
  let i2 := (Scheme.Modules.pushforward (pullback.snd c t)).mapIso i1
  let i3 := (Scheme.Modules.exteriorPower T n).mapIso i2
  exact ⟨(MonoidalClosed.internalHom.mapIso i3.symm.op).app (𝟙_ T.Modules)⟩

end S_AlgebraicGeometry_RelPicard_nonempty_thetaBundle_iso_of_iso
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_nonempty_thetaBundle_iso_of_iso (solution)
