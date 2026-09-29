-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.TwoAffineOpenCover.nonempty_inf_of_not_isAffine
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/e4c97dd1-6914-5972-89ee-bf57e6483c83

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_inf_of_not_isAffine

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {X : Scheme.{u}} [IrreducibleSpace X] (𝒱 : X.TwoAffineOpenCover) (hX : ¬ IsAffine X) :
    ((𝒱.U0 ⊓ 𝒱.U1 : X.Opens) : Set X).Nonempty := by

  have hne : ∀ {U V : X.Opens}, IsAffineOpen U → U ⊔ V = ⊤ → ((V : X.Opens) : Set X).Nonempty := by
    intro U V hU hUV
    rw [← TopologicalSpace.Opens.ne_bot_iff_nonempty]
    rintro rfl
    rw [sup_bot_eq] at hUV
    subst hUV
    exact hX (@IsAffine.of_isIso _ _ X.topIso.inv inferInstance hU)
  have h1 : ((𝒱.U1 : X.Opens) : Set X).Nonempty := hne 𝒱.isAffineOpen_U0 𝒱.sup_eq_top
  have h0 : ((𝒱.U0 : X.Opens) : Set X).Nonempty := hne 𝒱.isAffineOpen_U1 (by rw [sup_comm]; exact 𝒱.sup_eq_top)
  exact nonempty_preirreducible_inter 𝒱.U0.isOpen 𝒱.U1.isOpen h0 h1

end S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_inf_of_not_isAffine
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_inf_of_not_isAffine (solution)
