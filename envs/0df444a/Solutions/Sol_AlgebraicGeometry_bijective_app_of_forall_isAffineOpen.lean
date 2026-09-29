-- Prove2me | solution 1 for AlgebraicGeometry.bijective_app_of_forall_isAffineOpen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/c1572a83-8e6f-5637-aba1-f1f8834bcdb7

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_bijective_app_of_forall_isAffineOpen

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

open TopologicalSpace Opposite

namespace SheafGlueGC3

open TopCat TopCat.Presheaf

theorem stalkFunctor_map_surjective_of_isBasis {X : TopCat.{u}} {B : Set (Opens X)} (hB : Opens.IsBasis B)
    {F G : X.Presheaf CommRingCat.{u}} {α : F ⟶ G} (hα : ∀ U ∈ B, Function.Surjective (α.app (op U))) (x : X) :
    Function.Surjective ((stalkFunctor _ x).map α) := by
  intro t
  obtain ⟨U, hxU, hU, t, rfl⟩ := exists_mem_germ_eq_of_isBasis hB G x t
  obtain ⟨s, rfl⟩ := hα U hU t
  exact ⟨F.germ U x hxU s, by rw [stalkFunctor_map_germ_apply]⟩

end SheafGlueGC3

theorem solution {X B : Scheme.{u}} (p : X ⟶ B)
    (h : ∀ U : B.Opens, IsAffineOpen U → Function.Bijective (p.app U)) (U : B.Opens) :
    Function.Bijective (p.app U) := by
  let F : TopCat.Sheaf CommRingCat.{u} B.carrier := B.sheaf
  let G : TopCat.Sheaf CommRingCat.{u} B.carrier := (TopCat.Sheaf.pushforward _ p.base).obj X.sheaf
  let f : F ⟶ G := ⟨p.c⟩
  have key := TopCat.Presheaf.app_bijective_of_stalkFunctor_map_bijective f U (fun x _ =>
    ⟨TopCat.Presheaf.stalkFunctor_map_injective_of_isBasis B.isBasis_affineOpens
        (fun V hV => (h V hV).1) x,
     SheafGlueGC3.stalkFunctor_map_surjective_of_isBasis B.isBasis_affineOpens
        (fun V hV => (h V hV).2) x⟩)
  exact key

end S_AlgebraicGeometry_bijective_app_of_forall_isAffineOpen
end P2MW
export P2MW.S_AlgebraicGeometry_bijective_app_of_forall_isAffineOpen (solution)
