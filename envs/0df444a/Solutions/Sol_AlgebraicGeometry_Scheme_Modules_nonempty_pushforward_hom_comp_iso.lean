-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.nonempty_pushforward_hom_comp_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/aba8ec84-3fe0-591f-aaf1-d0099380c702

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pushforward_hom_comp_iso

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace PushIso

variable {X Y : Scheme.{u}} (φ : X ≅ Y)

noncomputable def pushEquiv : X.Modules ≌ Y.Modules :=
  CategoryTheory.Equivalence.mk (Scheme.Modules.pushforward φ.hom) (Scheme.Modules.pushforward φ.inv)
    ((Scheme.Modules.pushforwardId X).symm ≪≫ Scheme.Modules.pushforwardCongr φ.hom_inv_id.symm ≪≫
      (Scheme.Modules.pushforwardComp φ.hom φ.inv).symm)
    (Scheme.Modules.pushforwardComp φ.inv φ.hom ≪≫ Scheme.Modules.pushforwardCongr φ.inv_hom_id ≪≫
      Scheme.Modules.pushforwardId Y)

noncomputable def pullbackIsoPushforwardInv :
    Scheme.Modules.pullback φ.hom ≅ Scheme.Modules.pushforward φ.inv :=
  (Scheme.Modules.pullbackPushforwardAdjunction φ.hom).leftAdjointUniq (pushEquiv φ).symm.toAdjunction

end PushIso

theorem solution
    {X Y Z : Scheme.{u}} (e : X ≅ Y) (f : Y ⟶ Z) (F : X.Modules) :
    Nonempty ((Scheme.Modules.pushforward (e.hom ≫ f)).obj F ≅
      (Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback e.inv).obj F)) :=
  ⟨(Scheme.Modules.pushforwardComp e.hom f).symm.app F ≪≫
    (Scheme.Modules.pushforward f).mapIso ((PushIso.pullbackIsoPushforwardInv e.symm).app F).symm⟩

end S_AlgebraicGeometry_Scheme_Modules_nonempty_pushforward_hom_comp_iso
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pushforward_hom_comp_iso (solution)
