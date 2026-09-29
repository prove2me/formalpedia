-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction_unit_app_eq_of_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/c23df761-cf9f-58ee-a51f-3ff95e3ef5bf

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_pullbackPushforwardAdjunction_unit_app_eq_of_comp_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {Z Z' X : Scheme.{u}} (t : Z ⟶ Z') (ι' : Z' ⟶ X) (ι : Z ⟶ X) (h : t ≫ ι' = ι) (N : X.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app N =
      (Scheme.Modules.pullbackPushforwardAdjunction ι').unit.app N
        ≫ (Scheme.Modules.pushforward ι').map
            ((Scheme.Modules.pullbackPushforwardAdjunction t).unit.app ((Scheme.Modules.pullback ι').obj N))
        ≫ (Scheme.Modules.pushforwardComp t ι').hom.app
            ((Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback ι').obj N))
        ≫ (Scheme.Modules.pushforward (t ≫ ι')).map ((Scheme.Modules.pullbackComp t ι').hom.app N)
        ≫ (Scheme.Modules.pushforward (t ≫ ι')).map ((Scheme.Modules.pullbackCongr h).hom.app N)
        ≫ (Scheme.Modules.pushforwardCongr h).hom.app ((Scheme.Modules.pullback ι).obj N) := by
  subst h
  have key := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction ι').comp (Scheme.Modules.pullbackPushforwardAdjunction t))
    (Scheme.Modules.pullbackPushforwardAdjunction (t ≫ ι')) (Scheme.Modules.pullbackComp t ι').inv N
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at key
  have h1 : (Scheme.Modules.pullbackCongr (rfl : t ≫ ι' = t ≫ ι')).hom.app N = 𝟙 _ := by
    simp [Scheme.Modules.pullbackCongr]
  have h2 : (Scheme.Modules.pushforwardCongr (rfl : t ≫ ι' = t ≫ ι')).hom.app
      ((Scheme.Modules.pullback (t ≫ ι')).obj N) = 𝟙 _ := by
    apply Scheme.Modules.hom_ext
    intro U
    rw [Scheme.Modules.pushforwardCongr_hom_app_app]
    simp
  rw [h1, h2, CategoryTheory.Functor.map_id, Category.comp_id, Category.comp_id]
  have key' := key =≫ (Scheme.Modules.pushforward (t ≫ ι')).map ((Scheme.Modules.pullbackComp t ι').hom.app N)
  dsimp only [Functor.comp_obj] at key'
  simp only [Category.assoc] at key'
  erw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.comp_id] at key'
  simp only [Category.assoc, Functor.comp_obj]
  exact key'.symm

end S_AlgebraicGeometry_Scheme_Modules_pullbackPushforwardAdjunction_unit_app_eq_of_comp_eq
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_pullbackPushforwardAdjunction_unit_app_eq_of_comp_eq (solution)
