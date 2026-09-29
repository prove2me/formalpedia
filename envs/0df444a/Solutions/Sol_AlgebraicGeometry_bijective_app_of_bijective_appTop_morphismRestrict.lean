-- Prove2me | solution 1 for AlgebraicGeometry.bijective_app_of_bijective_appTop_morphismRestrict
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/d89fa730-2309-59e1-957e-3b1365807cfe

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_bijective_app_of_bijective_appTop_morphismRestrict

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

open TopologicalSpace Opposite

namespace P4Aux

theorem bijective_app_congr {X B : Scheme.{u}} (p : X ⟶ B) {V W : B.Opens} (e : V = W)
    (h : Function.Bijective (p.app V)) : Function.Bijective (p.app W) := by
  subst e; exact h

end P4Aux

open P4Aux

set_option backward.isDefEq.respectTransparency false in

theorem solution {X B : Scheme.{u}} (p : X ⟶ B) (U : B.Opens)
    (h : Function.Bijective (p ∣_ U).appTop) : Function.Bijective (p.app U) := by
  have e : U.ι ''ᵁ ⊤ = U := U.ι_image_top
  apply bijective_app_congr p e
  have key : p.app (U.ι ''ᵁ ⊤) =
      (p ∣_ U).appTop ≫ X.presheaf.map (eqToHom (image_morphismRestrict_preimage p U ⊤).symm).op := by
    simp only [morphismRestrict_appTop, Category.assoc, ← Functor.map_comp, ← op_comp, eqToHom_trans, eqToHom_refl,
      op_id]
    rw [show X.presheaf.map (𝟙 _) = 𝟙 _ from X.presheaf.map_id _, Category.comp_id]
  rw [key]
  exact (ConcreteCategory.bijective_of_isIso
    (X.presheaf.map (eqToHom (image_morphismRestrict_preimage p U ⊤).symm).op)).comp h

end S_AlgebraicGeometry_bijective_app_of_bijective_appTop_morphismRestrict
end P2MW
export P2MW.S_AlgebraicGeometry_bijective_app_of_bijective_appTop_morphismRestrict (solution)
