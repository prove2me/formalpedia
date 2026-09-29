-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.surjective_toBase_of_representsRelSubPic_algEquivZeroCut
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/fc281ea7-98e9-5809-a36b-78919ea8ae30

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_surjective_toBase_of_representsRelSubPic_algEquivZeroCut

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian

theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) :
    Surjective D.toBase := by
  refine ⟨fun s => ⟨D.zeroSection.base s, ?_⟩⟩
  have hs := congrArg (fun φ : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R) => φ.base s) D.zeroSection_toBase
  simpa using hs

end S_AlgebraicGeometry_RelPicard_surjective_toBase_of_representsRelSubPic_algEquivZeroCut
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_surjective_toBase_of_representsRelSubPic_algEquivZeroCut (solution)
