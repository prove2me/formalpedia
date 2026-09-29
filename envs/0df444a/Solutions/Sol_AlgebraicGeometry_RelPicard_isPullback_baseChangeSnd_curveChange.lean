-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.isPullback_baseChangeSnd_curveChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/163dd9fc-9fe2-5b25-b323-4abe7bfdf36e

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Theorems.Thm_CategoryTheory_IsPullback_fst_pullbackMap_of_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_isPullback_baseChangeSnd_curveChange

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard

theorem solution
    {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    (f : C' ⟶ C) (hf : f ≫ c = c')
    {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) :
    IsPullback (baseChangeSnd c' ψ) (curveChange f hf t') (curveChange f hf t) (baseChangeSnd c ψ) := by

  have sq : IsPullback (pullback.fst c' t) (curveChange f hf t) f (pullback.fst c t) :=
    CategoryTheory.IsPullback.fst_pullbackMap_of_comp_eq c c' t f hf
  have sq' : IsPullback (pullback.fst c' t') (curveChange f hf t') f (pullback.fst c t') :=
    CategoryTheory.IsPullback.fst_pullbackMap_of_comp_eq c c' t' f hf
  have e₁ : baseChangeSnd c' ψ ≫ pullback.fst c' t = pullback.fst c' t' :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have e₂ : baseChangeSnd c ψ ≫ pullback.fst c t = pullback.fst c t' :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  rw [← e₁, ← e₂] at sq'
  exact IsPullback.of_right sq' (curveChange_baseChangeSnd f hf ψ).symm sq

end S_AlgebraicGeometry_RelPicard_isPullback_baseChangeSnd_curveChange
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_isPullback_baseChangeSnd_curveChange (solution)
